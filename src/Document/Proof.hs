{-# LANGUAGE BangPatterns #-} 
{-# LANGUAGE ScopedTypeVariables            #-}
module Document.Proof where

    -- Modules
import Logic.Expr.Parser
import Document.Visitor

import Latex.Parser 

import UnitB.UnitB
import UnitB.Expr.Parser

import Logic.Expr
import Logic.Expr.Printable
import Logic.Operator
import Logic.Proof as LP
import Logic.Proof.Tactics as LP

    -- Libraries
import Control.Arrow
import Control.Lens hiding (Context,indices)

import           Control.Monad hiding ( guard )
import           Control.Monad.Reader.Class hiding ( reader )
import           Control.Monad.State as ST ( StateT )
import           Control.Monad.State.Class as ST
import qualified Control.Monad.Writer.Class as W
import           Control.Monad.Trans
import qualified Control.Monad.Trans.Either as E
import           Control.Monad.Trans.Writer

import           Data.Char
import           Data.Map hiding ( map )
import qualified Data.Map as M
import           Data.Maybe
import qualified Data.Set as S
import qualified Data.Traversable as T 

import Text.Printf.TH as Printf

import           Utilities.Error
import           Utilities.Syntactic hiding (line)

data ProofStep = Step 
       { assertions  :: Map Label (Tactic Expr)    -- assertions
       , subproofs   :: Map Label (Tactic Proof)   -- proofs of assertions
       , assumptions :: Map Label (Tactic Expr)    -- assumptions
       , definition  :: [(Name, Tactic Expr)] 
       , theorem_ref :: [Tactic (TheoremRef, LineInfo)]
       , new_goal    :: Maybe (Tactic Expr)        -- new_goal
       , main_proof  :: Maybe (Tactic Proof)       -- main proof        
       }

data FreeVarOpt = WithFreeDummies | WithoutFreeDummies

set_proof :: ( Monad m
             , MonadReader LineInfo m
             , MonadError m
             , MonadState ProofStep m)
          => Tactic Proof -> m ()
set_proof p = do
        s <- ST.get
        case main_proof s of
            Nothing -> ST.put $ s { main_proof = Just p }
            Just _  -> do
                li <- ask
                hard_error [Error "too many proofs" li]

set_goal :: ( Monad m
            , MonadReader LineInfo m
            , MonadError m
            , MonadState ProofStep m)
         => Tactic Expr
         -> m ()
set_goal g = do
        s <- ST.get
        case new_goal s of       
            Nothing ->
                ST.put $ s { new_goal = Just g }
            Just _ -> do
                li    <- ask
                hard_error [Error ("too many goals") li]

add_refs :: ( Monad m
                  , MonadReader LineInfo m
                  , MonadError m
                  , MonadState ProofStep m)
         => [Tactic (TheoremRef,LineInfo)] -> m ()
add_refs xs = ST.modify $ \p -> p { theorem_ref = xs ++ theorem_ref p }

add_definition :: ( Monad m
                  , MonadReader LineInfo m
                  , MonadError m
                  , MonadState ProofStep m)
               => Name -> Tactic Expr
               -> m ()
add_definition v e = do
        s <- ST.get
        ST.put $ s { definition = (v,e) : definition s }

add_assumption :: ( Monad m
                  , MonadReader LineInfo m
                  , MonadError m
                  , MonadState ProofStep m)
               => Label -> Tactic Expr
               -> m ()
add_assumption lbl asm = do
        s <- ST.get
        if lbl `member` assumptions s then do
            li    <- ask
            hard_error [Error ([Printf.s|an assumption %s already exists|] $ pretty lbl) li]
        else ST.put $ s { assumptions = insert lbl asm $ assumptions s }

add_assert :: ( Monad m
              , MonadReader LineInfo m
              , MonadError m
              , MonadState ProofStep m)
           => Label -> Tactic Expr
           -> m ()
add_assert lbl asrt = do
        s <- ST.get
        if lbl `member` assertions s then do
            li    <- ask
            hard_error [Error ([Printf.s|an assertion %s already exists|] $ pretty lbl) li]
        else ST.put $ s { assertions = insert lbl asrt $ assertions s }

add_proof :: ( Monad m
             , MonadReader LineInfo m
             , MonadError m
             , MonadState ProofStep m)
          => Label -> Tactic Proof
          -> m ()
add_proof lbl prf = do
        s <- ST.get
        if lbl `member` subproofs s then do
            li    <- ask
            hard_error [Error ([Printf.s|a proof for assertion %s already exists|] $ pretty lbl) li]
        else
            ST.put $ s { subproofs = insert lbl prf $ subproofs s }

empty_step :: ProofStep
empty_step = Step empty empty empty [] [] Nothing Nothing

find_assumptions :: (MonadReader Thy m)
                 => VisitorT (StateT ProofStep m) () 
find_assumptions = visitor
        [   (   "calculation"
            ,   VEnvBlock $ \() _ -> return ()
            )
        ,   (   "free:var"
            ,   VEnvBlock $ \(_ :: Label,_ :: Label) _ -> return ()
            )
        ,   (   "by:cases"
            ,   VEnvBlock $ \() _ -> return ()
            )
        ,   (   "by:parts"
            ,   VEnvBlock $ \() _ -> return ()
            )
        ,   (   "subproof"
            ,   VEnvBlock $ \(Identity (_ :: Label)) _ -> return ()
            )
        ] [ (   "\\assume"
            ,   VCmdBlock $ \(lbl,formula) -> do
                    expr   <- lift_i $ get_expression (Just bool) formula 
                    add_assumption lbl expr 
            )
        ,   (   "\\assert"
            ,   VCmdBlock $ \(lbl,formula) -> do
                    expr   <- lift_i $ get_expression (Just bool) formula 
                    add_assert lbl expr
            )
        ,   (   "\\define"
            ,   VCmdBlock $ \(var,formula) -> do
                    expr   <- lift_i $ get_expression Nothing formula 
                    add_definition var expr
            )
        ,   (   "\\goal"
            ,   VCmdBlock $ \(Identity formula) -> do
                    expr   <- lift_i $ get_expression (Just bool) formula 
                    set_goal expr
            )
        ,   (   "\\using"
            ,   VCmdBlock $ \(Identity refs) -> do
                    ((),hs) <- add_writer $ with_content refs hint
                    add_refs hs
            )       
        ]

find_proof_step :: (MonadReader Thy m, Monad m)
                => VisitorT (StateT ProofStep m) ()
find_proof_step = visitor
        [   (   "calculation"
            ,   VEnvBlock $ \() _ -> do
                    li <- ask
                    cc' <- lift_i $ parse_calc
                    let cc = (\c -> c { l_info = li }) <$> cc'
                    notat <- lift $ lift $ ask
                    set_proof $ LP.with_line_info li $ do
                        cc <- cc
                        case infer_goal cc notat of
                            Right cc_goal -> do
                                    return (ByCalc $ cc & goal .~ cc_goal )
                            Left msgs      -> hard_error $ map (\x -> Error ([s|type error: %s|] x) li) msgs
                    return ()
            )
                -- TODO: make into a command
        ,   (   "free:var"
            ,   VEnvBlock $ \(from,to) _ -> do
                    li    <- ask
                    proof <- lift_i $ collect_proof_step
                    set_proof $ LP.with_line_info li $ do
                        free_goal from to proof
            )
        ,   (   "by:cases"
            ,   VEnvBlock $ \() _ -> do
                    li         <- ask
                    ((),cases) <- lift_i $ add_writer find_cases
                    set_proof $ LP.with_line_info li $ do
                        xs <- forM cases $ \(lbl,xp,pr) -> do
                            x <- xp
                            return (lbl,x,pr)
                        by_cases xs
            )
        ,   (   "by:parts"
            ,   VEnvBlock $ \() _ -> do
                    li    <- ask
                    ((),cases) <- lift_i $ add_writer find_parts
                    set_proof $ LP.with_line_info li $ do
                        xs <- forM cases $ \(xp,pr) -> do
                            x <- xp
                            return (x,pr)
                        by_parts xs
            )
        ,   (   "subproof"
            ,   VEnvBlock $ \(Identity lbl) _ -> do
                    li     <- ask
                    proofs <- lift $ ST.get
                    unless (lbl `M.member` assertions proofs)
                            (hard_error [Error ([s|invalid subproof label: %s|] $ pretty lbl) li])
                    p <- lift_i collect_proof_step-- (change_goal pr new_goal) m
                    add_proof lbl p
            )
        ,   (   "indirect:equality"
            ,   VEnvBlock $ \(String dir,rel,zVar) _ -> do
                    li <- ask
                    notat <- lift $ lift ask
                    op <- make_soft equal $ fromEitherM
                        $ parse_oper 
                            notat
                            (flatten_li' rel) 
                    dir <- case map toLower dir of
                                "left"  -> return $ Left ()
                                "right" -> return $ Right ()
                                _ -> hard_error [Error "invalid inequality side, expecting 'left' or 'right': " li]
                    p <- lift_i collect_proof_step
                    set_proof $ LP.with_line_info li $ do
                        var <- get_dummy zVar
                        indirect_equality dir op 
                                var p
            )
        ,   (   "indirect:inequality"
            ,   VEnvBlock $ \(String dir,rel,zVar) _ -> do
                    li <- ask
                    notat <- lift $ lift ask
                    op <- make_soft equal $ fromEitherM
                        $ parse_oper 
                            notat
                            (flatten_li' rel) 
                    dir <- case map toLower dir of
                                "left"  -> return $ Left ()
                                "right" -> return $ Right ()
                                _ -> hard_error [Error "invalid inequality side, expecting 'left' or 'right': " li]
                    p <- lift_i $ collect_proof_step
                    set_proof $ LP.with_line_info li $ do
                        var <- get_dummy zVar
                        indirect_inequality dir op 
                                var p
            )
        ,   (   "by:symmetry"
            ,   VEnvBlock $ \(lbl,vars) _ -> do
                    li <- ask
                    p <- lift_i collect_proof_step
                    set_proof $ LP.with_line_info li $ do
                        vs <- mapM get_dummy vars 
                        by_symmetry vs lbl Nothing p
            )
        ] [ (   "\\easy"
            ,   VCmdBlock $ \() -> do
                    li <- ask        
                    set_proof $ LP.with_line_info li easy
            )
        ,   (   "\\withTimeout"
            ,   VCmdBlock $ \(Identity to) -> do
                    li <- ask        
                    set_proof $ LP.with_line_info li (easyWithTimeout to)
            )
        ] 

find_cases :: (MonadReader Thy m)
           => VisitorT (WriterT [(Label,Tactic Expr,Tactic Proof)] m) ()
find_cases = visitor 
        [   (   "case"
            ,   VEnvBlock $ \(lbl,formula) _ -> do
                    expr      <- lift_i $ get_expression (Just bool) formula 
                    p         <- lift_i collect_proof_step
                    lift $ tell [(lbl, expr, p)]
            )
        ] []

find_parts :: (MonadReader Thy m)
           => VisitorT (WriterT [(Tactic Expr,Tactic Proof)] m) () -- [(Expr,Proof)]
find_parts = visitor 
        [   (   "part:a"
            ,   VEnvBlock $ \(Identity formula) _ -> do -- xs cases -> do
                    expr  <- lift_i $ get_expression (Just bool) formula 
                    p     <- lift_i collect_proof_step -- (pr { po = new_po }) m
                    lift $ tell [(expr, p)]
                    return ()
            )
        ] []

type Thy = Notation

collect_proof_step :: (MonadReader Thy m)
                   => VisitorT m (Tactic Proof)
collect_proof_step = do
        ((),step) <- make_hard $ add_state empty_step find_assumptions
        li   <- ask
        (_,step) <- add_state step find_proof_step
        case main_proof step of
            Just p -> do
                let assrt   = assertions step
                    prfs    = subproofs step
                    asm     = assumptions step
                    defs    = definition step
                    ng      = new_goal step
                    thm_ref = theorem_ref step
                if keysSet prfs `S.isSubsetOf` keysSet assrt
                     then return $ LP.with_line_info li $ do
                        defs <- forM defs $ 
                            runKleisli $ second $ Kleisli id
                        define defs $ do
                            thm  <- sequence thm_ref
                            let make_assert = use_theorems thm $ do
                                    assrt <- forM (toList assrt) $ \(lbl,xp) -> do
                                        xp <- xp
                                        let p = fromMaybe easy $ M.lookup lbl prfs
                                        return (lbl,xp,p)
                                    LP.assert assrt p
                            -- thm <- sequence thm_ref
                            use_theorems thm $ do
                                case ng of
                                    Just g  -> LP.with_line_info li $ do
                                        g <- g
                                        asm <- toList <$> T.sequenceA asm
                                        assume asm g make_assert
                                    Nothing -> 
                                        if M.null asm 
                                        then make_assert
                                        else hard_error [Error "assumptions must be accompanied by a new goal" li]
                    else hard_error [Error "assertion labels and proofs mismatch" li]
            _   -> hard_error [Error "expecting a single proof step" li]         

hint :: ( MonadReader Thy m
        , W.MonadWriter [Tactic (TheoremRef, LineInfo)] m)
     => VisitorT m ()
hint = visitor []
        [ ( "\\ref", VCmdBlock f )
        , ( "\\eqref", VCmdBlock f )
        , ( "\\inst", VCmdBlock g )
        , ( "\\eqinst", VCmdBlock g )
        -- , ( "\\stmt", VCmdBlock h )
        ]
    where
        g (lbl,subst) = do
                li <- ask
                ((),w) <- with_content subst $ add_writer $ visitor []
                    [ ( "\\subst", VCmdBlock $ \(var, expr) -> do
                            expr <- get_expression Nothing expr
                            lift $ W.tell [do
                                dum <- get_dummy var
                                xp  <- expr
                                return (dum,xp)]  
                            return ()
                      ) ]
                lift $ W.tell [do
                    w <- sequence w 
                    return (ThmRef lbl w,li)]
        f (Identity b) = do
            li <- ask
            lift $ W.tell [return (ThmRef b [],li)]

parse_calc :: ( MonadReader Thy m )
           => VisitorT m (Tactic Calculation)
parse_calc = do
    xs <- get_content
    case find_cmd_arg 2 ["\\hint"] xs of
        Just (step,kw,[rel,tx_hint],remainder)    -> do
            let li = line_info step
            xp <- local (const li) $ get_expression Nothing step
            notat <- lift ask 
            op <- make_soft equal $ fromEitherM
                $ parse_oper 
                    notat
                    (flatten_li' rel) 
            ((),hs) <- add_writer $ with_content tx_hint $ hint
            calc    <- with_content remainder parse_calc
            return $ LP.with_line_info (line_info kw) $ do
                hs  <- sequence hs
                xp  <- make_soft ztrue xp
                c   <- add_step xp op hs calc
                return $ c { l_info = li }
        Nothing         -> do
            li <- ask
            xp <- get_expression Nothing xs
            return $ LP.with_line_info li $ do
                xp  <- make_soft ztrue xp
                last_step xp
        _ -> do
            li <- ask
            soft_error [Error "invalid hint" li]
            return $ LP.with_line_info li $ last_step ztrue
                               
parse_expr'' :: ParserSetting
             -> StringLi
             -> M DispExpr
parse_expr'' p xs = do
        hoistEither $ parse_expr p xs

unfail :: M a -> M (Maybe a)
unfail (M cmd) = M $ do
    x <- lift (E.runEitherT cmd)
    case x of
        Right x -> return $ Just x
        Left es -> W.tell es >> return Nothing

get_expression :: ( MonadReader Thy m )
               => Maybe Type
               -> LatexDoc
               -> VisitorT m (Tactic Expr)
get_expression t ys = do
            let li = line_info xs
            notation  <- lift ask            
            -- sys <- lift $ ST.get
            return $ LP.with_line_info li $ do
                ctx <- get_context
                let parser = setting_from_context notation ctx & expected_type .~ t
                either hard_error return $ 
                    getExpr <$> parse_expr parser (flatten_li' xs)
        where
            xs    = drop_blank_text' ys

get_predicate' :: Theory
               -> Context
               -> LatexDoc
               -> Either [Error] DispExpr
get_predicate' th ctx ys = parse_expr' 
        (setting_from_context 
            (th_notation th) ctx)
        ys

get_assert :: Machine
           -> LatexDoc
           -> Either [Error] DispExpr
get_assert m = parse_expr' (machine_setting m)

get_evt_part :: Machine -> Event
             -> LatexDoc
             -> Either [Error] DispExpr
get_evt_part m e = parse_expr' (event_setting m e & is_step .~ True)
                        

get_assert_with_free :: Machine 
                     -> LatexDoc
                     -> Either [Error] DispExpr
get_assert_with_free m = parse_expr' (machine_setting m & free_dummies .~ True)

lift2 :: (MonadTrans t0, MonadTrans t1, Monad m, Monad (t1 m))
      => m a
      -> t0 (t1 m) a
lift2 cmd = lift $ lift cmd
