{-# LANGUAGE FlexibleContexts, BangPatterns #-} 
{-# LANGUAGE ScopedTypeVariables            #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
module Document.Proof where

    -- Modules
import Document.Expression
import Document.Visitor

import Latex.Parser 

import UnitB.AST
import UnitB.PO

import Logic.Calculation hiding ( context )
import Logic.Classes
import Logic.Expr
import Logic.Const
import Logic.Genericity
import Logic.Label
import Logic.Operator
import Logic.Tactics as Tac
import Logic.Theory

    -- Libraries
import           Control.Monad hiding ( guard )
import           Control.Monad.Reader.Class hiding ( reader )
import           Control.Monad.State.Class as ST
import           Control.Monad.Trans
import           Control.Monad.Trans.Either
import           Control.Monad.Trans.RWS hiding ( ask, tell, asks, reader, local )
import           Control.Monad.Trans.Reader ( runReaderT )
import           Control.Monad.Trans.State as ST ( StateT, evalStateT )
import           Control.Monad.Trans.Writer

import           Data.Char
import           Data.Map hiding ( map, foldl )
import qualified Data.Map as M
import           Data.Monoid (Monoid)
import           Data.List as L hiding ( union, insert, inits )
import qualified Data.Set as S

import           Utilities.Error
import           Utilities.Format
import           Utilities.Syntactic hiding (line)

context :: Machine -> Context
context m = step_ctx m `merge_ctx` theory_ctx S.empty (theory m)

data ProofStep = Step 
       { assertions  :: Map Label (Tactic Expr)    -- assertions
       , subproofs   :: Map Label (Tactic Proof)   -- proofs of assertions
       , assumptions :: Map Label (Tactic Expr)    -- assumptions
       , new_goal    :: Maybe (Tactic Expr)        -- new_goal
       , main_proof  :: Maybe (Tactic Proof)       -- main proof        
       }

data ProofParam = ProofParam 
    { hypotheses :: Map Label (Tactic Expr)
    , notat      :: Notation
    }

empty_pr :: Machine -> ProofParam
empty_pr m = ProofParam hyps (all_notation m)
    where
        p0 = props m
        p1 = inh_props m
        hyps = M.map return $ M.unions $
                [ inv p0
                , inv_thm p0
                , inv p1
                , inv_thm p1
                , inits m
                , fact $ theory m
                ] ++ map g (elems $ events m)
        g ev = M.unions
            [ coarse $ new_sched ev
            , new_guard ev
            , action ev ]

--par_ctx :: ProofParam -> Context
--par_ctx pr = ctx pr `merge_ctx` Context M.empty (locals pr) M.empty M.empty M.empty

set_proof :: ( Monad m
             , MonadReader LineInfo m
             , MonadError m
             , MonadState ProofStep m)
          => Tactic Proof -> m ()
set_proof p = do
        (Step a b c d mg) <- ST.get
        case mg of
            Nothing -> ST.put $ Step a b c d $ Just p
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
        (Step a b c goal d) <- ST.get
        case goal of       
            Nothing ->
                ST.put $ Step a b c (Just g) d
            Just _ -> do
                li    <- ask
                hard_error [Error ("too many goals") li]

add_assumption :: ( Monad m
                  , MonadReader LineInfo m
                  , MonadError m
                  , MonadState ProofStep m)
               => Label -> Tactic Expr
               -> m ()
add_assumption lbl asm = do
        (Step a b c d e) <- ST.get
        if lbl `member` c then do
            li    <- ask
            hard_error [Error (format "an assumption {0} already exists" lbl) li]
        else ST.put $ Step a b (insert lbl asm c) d e

add_assert :: ( Monad m
              , MonadReader LineInfo m
              , MonadError m
              , MonadState ProofStep m)
           => Label -> Tactic Expr
           -> m ()
add_assert lbl asrt = do
        (Step a b c d e) <- ST.get
        if lbl `member` a then do
            li    <- ask
            hard_error [Error (format "an assertion {0} already exists" lbl) li]
        else ST.put $ Step (insert lbl asrt a) b c d e

add_proof :: ( Monad m
             , MonadReader LineInfo m
             , MonadError m
             , MonadState ProofStep m)
          => Label -> Tactic Proof
          -> m ()
add_proof lbl prf = do
        (Step a b c d e) <- ST.get
        if lbl `member` b then do
            li    <- ask
            hard_error [Error (format "a proof for assertion {0} already exists" lbl) li]
        else
            ST.put $ Step a (insert lbl prf b) c d e

empty_step :: ProofStep
empty_step = Step empty empty empty Nothing Nothing

find_assumptions :: (MonadState System m, MonadReader Theory m)
                 => VisitorT (StateT ProofStep m) () -- ProofStep
--                 -> RWST LineInfo [Error] System m ProofStep
find_assumptions = visitor
        [   (   "calculation"
            ,   VEnvBlock $ \() _ -> return ()
            )
        ,   (   "free:var"
            ,   VEnvBlock $ \(_ :: Label,_ :: Label,()) _ -> return ()
            )
        ,   (   "by:cases"
            ,   VEnvBlock $ \() _ -> return ()
            )
        ,   (   "by:parts"
            ,   VEnvBlock $ \() _ -> return ()
            )
        ,   (   "subproof"
            ,   VEnvBlock $ \(_ :: Label,()) _ -> return ()
            )
        ] [ (   "\\assume"
            ,   VCmdBlock $ \(lbl,formula :: [LatexDoc],()) -> do
                    expr   <- lift_i $ get_expression (Just bool) formula 
--                        get_predicate m (par_ctx pr) WithoutFreeDummies formula 
                    add_assumption lbl expr 
            )
        ,   (   "\\assert"
            ,   VCmdBlock $ \(lbl,formula :: [LatexDoc],()) -> do
                    expr   <- lift_i $ get_expression (Just bool) formula 
--                        get_predicate m (par_ctx pr) WithoutFreeDummies formula
                    add_assert lbl expr
            )
        ,   (   "\\goal"
            ,   VCmdBlock $ \(formula :: [LatexDoc],()) -> do
                    expr   <- lift_i $ get_expression (Just bool) formula 
--                        get_predicate m (par_ctx pr) WithoutFreeDummies formula
                    set_goal expr
            )
        ]


--indirect_eq_thm :: MonadReader LineInfo m 
--                => Either () () -> BinOperator 
--                -> Type -> EitherT [Error] m Expr
--indirect_eq_thm dir op t = do
--        li <- ask
--        let (x,x_decl) = var "x" t
--            (y,y_decl) = var "y" t
--            (z,z_decl) = var "z" t
--        x <- hoistEither x
--        y <- hoistEither y
--        z <- hoistEither z
--        let equiv = indirect_eq dir op x y z
--        hoistEither $ with_li li $ mzforall [x_decl,y_decl] mztrue $
--                    (Right x `mzeq` Right y) `mzeq` mzforall [z_decl] mztrue equiv

indirect_eq :: Either () () -> BinOperator 
            -> Expr -> Expr -> Expr 
            -> Either String Expr
indirect_eq dir op x y z = do
                case dir of
                    Left()  -> mk_expr op z x `mzeq` mk_expr op z y
                    Right() -> mk_expr op x z `mzeq` mk_expr op y z

indirect_equality :: Monad m
                  => Either () () 
                  -> BinOperator 
                  -> Var
                  -> TacticT m Proof
                  -> TacticT m Proof
indirect_equality dir op zVar@(Var _ t) proof = do 
        x_decl <- new_fresh "x" t
        y_decl <- new_fresh "y" t
        z_decl <- new_fresh "z" t
        let x       = Word x_decl
            y       = Word y_decl
            z       = Word z_decl
            rel     = mk_expr op
            rel_z   = case dir of
                        Left ()  -> rel z
                        Right () -> flip rel z
            thm_rhs x y = mzforall [z_decl] mztrue $ rel_z x `mzeq` rel_z y
        thm  <- make_expr $ mzforall [x_decl,y_decl] mztrue $ Right (zeq x y) `mzeq` thm_rhs x y
        goal <- get_goal
        case goal of
            FunApp f [lhs,rhs] 
                | name f == "=" -> do
                    new_goal <- make_expr $ mzforall [z_decl] mztrue $ thm_rhs lhs rhs
                    assert 
                        [ (label "indirect:eq", thm, easy)      -- (Ax,y:: x = y == ...)
                        , (label "new:goal", new_goal, do       -- (Az:: z ≤ lhs == z ≤ rhs)
                                free_goal z_decl zVar proof) ]
                        $ do
                            lbl <- fresh_label "inst"
                            instantiate_hyp                       -- lhs = rhs
                                thm lbl                             -- | we could instantiate indirect
                                [ (x_decl,lhs)                      -- | inequality explicitly 
                                , (y_decl,rhs) ]                    -- | for that, we need hypotheses 
                                easy                                -- | to be named in sequents
                                                              
            _ -> fail $ "expecting an equality:\n" ++ pretty_print' goal


find_proof_step :: (MonadState System m, MonadReader Theory m, Monad m)
                => ProofParam
                -> VisitorT (StateT ProofStep m) ()
find_proof_step pr = visitor
        [   (   "calculation"
            ,   VEnvBlock $ \() _ -> do
                    li <- ask
                    cc <- lift_i $ parse_calc pr
                    set_proof $ Tac.with_line_info li $ do
                        cc <- cc
                        case infer_goal cc (notat pr) of
                            Right cc_goal -> do
                                    return (Proof $ cc { goal = cc_goal })
                            Left msg      -> hard_error [Error (format "type error: {0}" msg) li]
                    return ()
            )
                -- TODO: make into a command
        ,   (   "free:var"
            ,   VEnvBlock $ \(String from,String to,()) _ -> do
                    li    <- ask
                    proof <- lift_i $ collect_proof_step pr
                    set_proof $ Tac.with_line_info li $ do
                        ctx <- get_context
                        let Context _ _ _ _ dums  = ctx
                        Var _ t <- maybe 
                                (hard_error [Error (format "cannot infer the type of '{0}'" to) li])
                                return
                                (M.lookup to dums)
                        free_goal (Var from t) (Var to t)
                            proof
            )
        ,   (   "by:cases"
            ,   VEnvBlock $ \() _ -> do
                    li         <- ask
                    ((),cases) <- lift_i $ add_writer $ find_cases pr
                    set_proof $ Tac.with_line_info li $ do
                        xs <- forM cases $ \(lbl,xp,pr) -> do
                            x <- xp
                            return (lbl,x,pr)
                        by_cases xs
            )
        ,   (   "by:parts"
            ,   VEnvBlock $ \() _ -> do
                    li    <- ask
                    ((),cases) <- lift_i $ add_writer $ find_parts pr
                    set_proof $ Tac.with_line_info li $ do
                        xs <- forM cases $ \(xp,pr) -> do
                            x <- xp
                            return (x,pr)
                        by_parts xs
            )
        ,   (   "subproof"
            ,   VEnvBlock $ \(lbl,()) _ -> do
                    li     <- ask
                    proofs <- lift $ ST.get
                    unless (lbl `M.member` assertions proofs)
                            (hard_error [Error (format "invalid subproof label: {0}" lbl) li])
                    p <- lift_i $ collect_proof_step pr-- (change_goal pr new_goal) m
                    add_proof lbl p
            )
        ,   (   "indirect:equality"
            ,   VEnvBlock $ \(String dir,rel,String zVar,()) _ -> do
                    li <- ask
                    op <- make_soft equal $ fromEitherM
                        $ parse_oper 
                            (notat pr)
                            (concatMap flatten_li rel) 
                    dir <- case map toLower dir of
                                "left"  -> return $ Left ()
                                "right" -> return $ Right ()
                                _ -> hard_error [Error "invalid inequality side, expecting 'left' or 'right': " li]
                    p <- lift_i $ collect_proof_step pr
                    set_proof $ Tac.with_line_info li $ do
                        ctx <- get_context
                        let Context _ _ _ _ vars = ctx
                        Var _ t <- maybe 
                            (hard_error [Error ("invalid dummy: " ++ zVar) li])
                            return
                            $ M.lookup zVar vars
                        indirect_equality dir op 
                                (Var zVar t) 
                                p
            )
        ] [ (   "\\easy"
            ,   VCmdBlock $ \() -> do
                    li <- ask        
                    set_proof $ Tac.with_line_info li easy
            )
        ] 

find_cases :: (MonadState System m, MonadReader Theory m)
           => ProofParam
           -> VisitorT (WriterT [(Label,Tactic Expr,Tactic Proof)] m) ()
find_cases pr = visitor 
        [   (   "case"
            ,   VEnvBlock $ \(lbl,formula :: [LatexDoc],()) _ -> do
                    expr      <- lift_i $ get_expression (Just bool) formula 
                    p         <- lift_i $ collect_proof_step 
                            (pr { hypotheses = insert lbl expr hyps })
                    lift $ tell [(lbl, expr, p)]
            )
        ] []
    where
        hyps = hypotheses pr 

find_parts :: (MonadState System m, MonadReader Theory m)
           => ProofParam
           -> VisitorT (WriterT [(Tactic Expr,Tactic Proof)] m) () -- [(Expr,Proof)]
find_parts pr = visitor 
        [   (   "part:a"
            ,   VEnvBlock $ \(formula :: [LatexDoc],()) _ -> do -- xs cases -> do
                    expr  <- lift_i $ get_expression (Just bool) formula 
                    p         <- lift_i $ collect_proof_step pr -- (pr { po = new_po }) m
                    lift $ tell [(expr, p)]
                    return ()
            )
        ] []

collect_proof_step :: (MonadState System m, MonadReader Theory m)
                   => ProofParam
                   -> VisitorT m (Tactic Proof)
collect_proof_step pr = do
        let hyps = hypotheses pr
        ((),step@(Step asrt _ asm _ _)) <- make_hard $ add_state empty_step $ find_assumptions
        li   <- ask
        let pr2 = pr { hypotheses = asrt `union` asm `union` hyps }
        (_,step) <- add_state step $ find_proof_step pr2
        case step of
            Step assrt prfs asm ng (Just p) -> do
                p <- if M.null assrt && M.null prfs
                    then return p
                    else if keysSet assrt == keysSet prfs
                    then return $ Tac.with_line_info li $ do
                        assrt <- forM (toList assrt) $ \(lbl,xp) -> do
                            xp <- xp
                            let p = prfs ! lbl
                            return (lbl,xp,p)
                        assert assrt p
                    else hard_error [Error "assertion labels and proofs mismatch" li]
                case ng of
                    Just g  -> return $ Tac.with_line_info li $ do
                        g <- g
                        asm <- forM (toList asm) $ \(lbl,x) -> do
                            x <- x
                            return (lbl,x)
                        assume asm g p
                    Nothing -> 
                        if M.null asm 
                        then return p
                        else hard_error [Error "assumptions must be accompanied by a new goal" li]
            _   -> hard_error [Error "expecting a single proof step" li]         

hint :: Monad m
     => VisitorT (WriterT [(Label, LineInfo)] m) ()
hint = visitor []
        [ ( "\\ref", VCmdBlock f ), ( "\\eqref", VCmdBlock f ) ]
    where
        f (b,()) = do
            li <- ask
            lift $ tell [(b,li)]

parse_calc :: ( MonadState System m, MonadReader Theory m )
           => ProofParam 
           -> VisitorT m (Tactic Calculation)
parse_calc pr = do
    xs <- get_content
    case find_cmd_arg 2 ["\\hint"] xs of
        Just (step,kw,[rel,tx_hint],remainder)    -> do
            xp <- get_expression Nothing step
            op <- make_soft equal $ fromEitherM
                $ parse_oper 
                    (notat pr)
                    (concatMap flatten_li rel) 
            li      <- ask
            ((),hs) <- add_writer $ with_content li tx_hint $ hint
            calc    <- with_content li remainder $ parse_calc pr
            return $ Tac.with_line_info (line_info kw) $ do
                xp  <- make_soft ztrue xp
                add_step xp op hs calc
        Nothing         -> do
            li <- ask
            xp <- get_expression Nothing xs
            return $ Tac.with_line_info li $ do
                xp  <- make_soft ztrue xp
                last_step xp
        _ -> do
            li <- ask
            soft_error [Error "invalid hint" li]
            return $ Tac.with_line_info li $ last_step ztrue

get_table :: ( MonadState System m, MonadReader LineInfo m ) 
          => Theory
          -> EitherT [Error] m (Matrix Operator Assoc)
get_table th = do 
        let key = sort $ M.keys $ extends th
        !tb <- lift $ ST.gets parse_table
        case M.lookup key tb of
            Just x -> do
                return x
            Nothing -> do
                let !x   = assoc' $ th_notation th
                    !new = insert key x tb
                lift $ ST.modify $ \s -> s { parse_table = new }
                return x
                                
data FreeVarOpt = WithFreeDummies | WithoutFreeDummies

--withProofParam cmd = EitherT $ mapRWST (\r (s0,s1) -> (r,(s0,s1))) $ runEitherT cmd

remove_ref :: [Char] -> [Char]
remove_ref ('\\':'r':'e':'f':'{':xs) = remove_ref xs
remove_ref ('}':xs) = remove_ref xs
remove_ref (x:xs)   = x:remove_ref xs
remove_ref []       = []

get_expr_with_ctx :: ( Monad m, Monoid b ) 
                  => Machine
                  -> Context
                  -> [LatexDoc] 
                  -> EitherT [Error] (RWST LineInfo b (System) m)  Expr
get_expr_with_ctx m ctx ys = do
        tb <- get_table $ theory m
        y  <- parse_expr 
                (context m `merge_ctx` ctx) 
                (all_notation m) tb
                (concatMap flatten_li xs)
        let x = normalize_generics y
        li <- if L.null xs
            then ask
            else return $ line_info xs
        unless (L.null $ ambiguities x) $ left 
            $ map (\x -> Error (format msg x (type_of x)) li)
                $ ambiguities x
        return x
    where
        xs    = drop_blank_text ys
        msg   = "type of {0} is ill-defined: {1}"

get_expr :: ( Monad m, Monoid b ) 
         => Machine
         -> FreeVarOpt
         -> [LatexDoc] 
         -> EitherT [Error] (RWST LineInfo b (System) m)  Expr
get_expr m opt ys = do
        let ctx = case opt of
                    WithFreeDummies -> dummy_ctx m
                    WithoutFreeDummies -> empty_ctx
        get_expr_with_ctx m ctx ys

get_expression :: (MonadState System m, MonadReader Theory m)
               => Maybe Type
               -> [LatexDoc]
               -> VisitorT m (Tactic Expr)
get_expression t ys = do
            li <- if L.null xs
                then ask
                else return $ line_info xs
            th  <- lift $ ask            
            tb  <- fromEitherM $ get_table th
--            traceM $ show tb
--            traceM $ show ctx
--            traceM $ show xs
            sys <- lift $ ST.get
            return $ Tac.with_line_info li $ do
                ctx <- get_context
                x   <- lift $ flip runReaderT li $ 
                        flip evalStateT sys $ 
                        runEitherT $ 
                        parse_expr 
                            ctx (th_notation th) tb
                            (concatMap flatten_li xs)
                x <- either hard_error return x
                let cast x = case t of
                                Just t -> zcast t x
                                Nothing -> x                    
                x <- either
                    fail
                    (return . normalize_generics) 
                    $ cast $ Right x
                unless (L.null $ ambiguities x) $ hard_error 
                    $ map (\x -> Error (format msg x (type_of x)) li)
                        $ ambiguities x
                return x
--            return $ either (const ztrue) id x
        where
            xs    = drop_blank_text ys
            msg   = "type of {0} is ill-defined: {1}"


get_predicate :: ( Monad m, Monoid b ) 
           => Machine
           -> Context
           -> FreeVarOpt
           -> [LatexDoc] 
           -> EitherT [Error] (RWST LineInfo b (System) m) Expr
get_predicate m ctx opt ys = do
        let th = theory m
        let d_ctx = case opt of
                        WithFreeDummies -> dummy_ctx m
                        WithoutFreeDummies -> empty_ctx
        get_predicate' th (ctx `merge_ctx` d_ctx `merge_ctx` context m) ys

get_predicate' :: ( Monad m, Monoid b ) 
           => Theory
           -> Context
           -> [LatexDoc] 
           -> EitherT [Error] (RWST LineInfo b System m) Expr
get_predicate' th ctx ys = do
        tb <- get_table th
        x  <- parse_expr 
                ctx
                (th_notation th) tb
                (concatMap flatten_li xs)
        li <- if L.null xs
            then ask
            else return $ line_info xs
        x <- either 
            (\x -> left [Error x li]) 
            (right . normalize_generics) $ zcast bool $ Right x
        unless (L.null $ ambiguities x) $ left 
            $ map (\x -> Error (format msg x (type_of x)) li)
                $ ambiguities x
        return x
    where
        xs    = drop_blank_text ys
        msg   = "type of {0} is ill-defined: {1}"


get_assert :: ( Monad m, Monoid b ) 
           => Machine
           -> [LatexDoc] 
           -> EitherT [Error] (RWST LineInfo b (System) m) Expr
get_assert m ys = get_predicate m empty_ctx WithoutFreeDummies ys

get_evt_part :: ( Monad m, Monoid b ) 
             => Machine -> Event
             -> [LatexDoc] 
             -> EitherT [Error] (RWST LineInfo b System m)  Expr
get_evt_part m e ys = get_predicate m 
                        (            step_ctx m 
                         `merge_ctx` theory_ctx S.empty (theory m)
                         `merge_ctx` evt_live_ctx e
                         `merge_ctx` evt_saf_ctx  e)
                        WithoutFreeDummies
                        ys

get_assert_with_free :: ( Monad m, Monoid b ) 
                     => Machine -> [LatexDoc] 
                     -> EitherT [Error] (RWST LineInfo b System m)  Expr
get_assert_with_free m ys = get_predicate m 
                        (context m)
                        WithFreeDummies
                        ys
lift2 :: (MonadTrans t0, MonadTrans t1, Monad m, Monad (t1 m))
      => m a
      -> t0 (t1 m) a
lift2 cmd = lift $ lift cmd

predicate :: Maybe Type 
          -> [LatexDoc] 
          -> Notation
          -> Matrix Operator Assoc
          -> EitherT [Error] (RWST LineInfo () System Tactic) Expr
predicate t ys n tb = do
        ctx <- lift2 $ get_context
        li <- lift $ lift $ if L.null xs
            then get_line_info
            else return $ line_info xs
        x <- parse_expr 
                ctx
                n tb
                (concatMap flatten_li xs)
        x <- maybe 
            (return $ Right x)
            (\t -> return $ zcast t $ Right x)
            t
        x <- either 
            (\x -> left [Error x li]) 
            (right . normalize_generics) x
        unless (L.null $ ambiguities x) $ left 
            $ map (\x -> Error (format msg x (type_of x)) li)
                $ ambiguities x
        return x
    where
        xs    = drop_blank_text ys
        msg   = "type of {0} is ill-defined: {1}"

