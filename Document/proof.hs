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
import Logic.Sequent
import Logic.Tactics as Tac
import Logic.Theory

    -- Libraries
import           Control.Monad hiding ( guard )
import           Control.Monad.Reader.Class hiding ( reader )
import           Control.Monad.State.Class as ST
import           Control.Monad.Trans
import           Control.Monad.Trans.Either
import           Control.Monad.Trans.RWS hiding ( ask, tell, asks, reader, local )
import qualified Control.Monad.Trans.RWS as RWS
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
import qualified Utilities.Graph as G ( size )
import           Utilities.Syntactic hiding (line)
import           Utilities.Trace

--type StateT s m = RWST () () s m

--class (MonadState System m, MonadReader Theory m) => MonadProofParser m where

--instance (MonadState System m, MonadReader Theory m) => MonadProofParser m where

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
    , locals     :: Map String Var
    , ctx        :: Context
    , po         :: Sequent
    }

empty_pr :: Context -> Sequent -> ProofParam
empty_pr = ProofParam M.empty M.empty

par_ctx :: ProofParam -> Context
par_ctx pr = ctx pr `merge_ctx` Context M.empty (locals pr) M.empty M.empty M.empty

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

add_local :: [Var] -> ProofParam -> ProofParam
add_local v pr = pr { ctx =             Context M.empty 
                                            (symbol_table v)
                                            M.empty M.empty M.empty
                            `merge_ctx` ctx pr }

change_goal :: ProofParam -> Expr -> ProofParam
change_goal pr g = pr { po = Sequent ctx hyps g }
    where
        Sequent ctx hyps _ = po pr

forall_goal :: (MonadError m, MonadReader LineInfo m) => ProofParam -> String
            -> m Expr -- EitherT [Error] (RWST LineInfo [Error] System m) Expr
forall_goal pr from = do
            let Sequent _ _ goal = po pr 
            li <- ask
            case goal of
                Binder Forall vs rexp texp -> do
                    if from `elem` map name vs then do
                        let new_vars = L.filter (\v -> name v /= from) vs
                        if not $ L.null new_vars then
                            return $ Binder Forall new_vars rexp texp
                        else
                            return $ zimplies rexp texp
                    else hard_error [Error (format "{0} is not a bound variable" from) li]
                _ -> hard_error [Error "goal is not a universal quantification" li]


match_equal :: (MonadReader LineInfo m, MonadError m)
            => ProofParam -> m (Expr, Expr)
match_equal pr = do
            let Sequent _ _ goal = po pr
            li <- ask
            let msg = ("expecting an equality in the proof goal:\n" ++ pretty_print' goal)
            case goal of
                FunApp f [x,y] -> do
                    if name f == "=" then
                        return (x,y)
                    else hard_error [Error msg li]
                _ -> hard_error [Error msg li]

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
                        $ instantiate_hyp                       -- lhs = rhs
                            thm                                 -- | we could instantiate indirect
                            [ (x_decl,lhs)                      -- | inequality explicitly 
                            , (y_decl,rhs) ]                    -- | for that, we need hypotheses 
                            easy                                -- | to be named in sequents
                                                              
            _ -> fail $ "expecting an equality:\n" ++ pretty_print' goal

run_inner_tactic :: (Monad m)
                 => Sequent -> LineInfo
                 -> RWST a [Error] c Tactic d 
                 -> EitherT [Error] (RWST a [Error] c m) d
run_inner_tactic po li cmd = do
        (x,s',w) <- EitherT $ do
            r <- ask
            s <- RWS.get
            return $ runTactic li po $ runRWST cmd r s
        unless (L.null w) $ lift $ RWS.tell w
        lift $ RWS.put s'
        return x

find_proof_step :: (MonadState System m, MonadReader Theory m, Monad m)
                => ProofParam
                -> Machine
--                -> [LatexDoc] 
--                -> ProofStep
                -> VisitorT (StateT ProofStep m) ()
find_proof_step pr m = visitor
        [   (   "calculation"
            ,   VEnvBlock $ \() _ -> do
                    li <- ask
                    cc <- lift_i $ parse_calc pr m
                    set_proof $ Tac.with_line_info li $ do
                        cc <- cc
                        case infer_goal cc (all_notation m) of
                            Right cc_goal -> do
                                    return (Proof $ cc { goal = cc_goal })
                            Left msg      -> hard_error [Error (format "type error: {0}" msg) li]
                    return ()
            )
                -- TODO: make into a command
        ,   (   "free:var"
            ,   VEnvBlock $ \(String from,String to,()) _ -> do
                    li    <- ask
                    let Context _ _ _ _ dums  = ctx pr
                    let Sequent ctx hyps _ = po pr 
                    goal <- forall_goal pr from
                    v@(Var _ t) <- maybe 
                            (hard_error [Error (format "cannot infer the type of '{0}'" to) li])
                            return
                            (M.lookup to dums)
                    p     <- lift_i $ collect_proof_step (add_local [v] pr) 
                            { po = Sequent ctx hyps goal }
                            m
                    set_proof $ Tac.with_line_info li $ 
                        free_goal (Var from t) (Var to t) p
                    --(Proof $ FreeGoal from to t p li)
            )
        ,   (   "by:cases"
            ,   VEnvBlock $ \() _ -> do
                    li         <- ask
                    ((),cases) <- lift_i $ add_writer $ find_cases pr m
--                    cases <- toEither $ find_cases pr m xs []
--                    set_proof (Proof $ ByCases (reverse cases) li) proofs )
                    set_proof $ Tac.with_line_info li $ do
                        xs <- forM cases $ \(lbl,xp,pr) -> do
                            x <- xp
                            return (lbl,x,pr)
                        by_cases xs
            )
        ,   (   "by:parts"
            ,   VEnvBlock $ \() _ -> do
                    li    <- ask
                    ((),cases) <- lift_i $ add_writer $ find_parts pr m
                    set_proof $ Tac.with_line_info li $ do
                        xs <- forM cases $ \(xp,pr) -> do
                            x <- xp
                            return (x,pr)
                        by_parts xs
--                    (Proof $ ByParts (reverse cases) li)
            )
        ,   (   "subproof"
            ,   VEnvBlock $ \(lbl,()) _ -> do
                    li     <- ask
                    proofs <- lift $ ST.get
                    unless (lbl `M.member` assertions proofs)
                            (hard_error [Error (format "invalid subproof label: {0}" lbl) li])
                    p <- lift_i $ collect_proof_step pr m -- (change_goal pr new_goal) m
                    add_proof lbl p
            )
        ,   (   "indirect:equality"
            ,   VEnvBlock $ \(String dir,rel,String zVar,()) _ -> do
                    let Context _ _ _ _ vars = par_ctx pr
                    li <- ask
                    Var _ t <- maybe 
                        (hard_error [Error ("invalid dummy: " ++ zVar) li])
                        return
                        $ M.lookup zVar vars
                    op <- make_soft equal $ fromEitherM
                        $ parse_oper 
                            (context m)
                            (all_notation m)
                            (concatMap flatten_li rel) 
                    dir <- case map toLower dir of
                                "left"  -> return $ Left ()
                                "right" -> return $ Right ()
                                _ -> hard_error [Error "invalid inequality side, expecting 'left' or 'right': " li]
--                    thm <- indirect_eq_thm dir op t
                    (lhs,rhs) <- match_equal pr
                    let z = Word $ Var "z" t
                    expr <- fromEitherM $ hoistEither $ with_li li $ indirect_eq dir op lhs rhs z
--                    symb_eq <- hoistEither $ with_li li $ mzeq (Right lhs) (Right rhs) 
                    let new_pr = add_local [Var zVar t] (change_goal pr expr)
                    p <- lift_i $ collect_proof_step new_pr m
                    set_proof $ indirect_equality dir op 
                            (Var zVar t) 
                            p
--                    set_proof (Proof $ Assertion 
--                            (M.fromList [ (label "indirect:eq", (thm, Proof $ Easy li))
--                                        , (label "new:goal", ( (zforall [z_decl] ztrue expr)
--                                                             , (Proof $ FreeGoal "z" zVar t p li))) 
--                                        , (label "symb:eq", ( symb_eq, Proof $ Ignore li ))
--                                        ] )
--                                (-- Proof $ Prune 2 $ 
--                                    Proof $ Easy li)
--                            li) proofs
            )
        ] [ (   "\\easy"
            ,   VCmdBlock $ \() -> do
                    li <- ask        
                    set_proof $ Tac.with_line_info li easy
            )
        ] 

find_cases :: (MonadState System m, MonadReader Theory m)
           => ProofParam
           -> Machine
--           -> [LatexDoc] 
--           -> [(Label,Expr,Proof)]
           -> VisitorT (WriterT [(Label,Tactic Expr,Tactic Proof)] m) ()
find_cases pr m = visitor 
        [   (   "case"
            ,   VEnvBlock $ \(lbl,formula :: [LatexDoc],()) _ -> do
                    expr      <- lift_i $ get_expression (Just bool) formula 
--                        get_predicate m (par_ctx pr) WithoutFreeDummies formula
--                    let (Sequent ctx old_hyps goal) = po pr
--                        new_po = Sequent ctx (expr:old_hyps) goal
                    p         <- lift_i $ collect_proof_step 
                            (pr { hypotheses = insert lbl expr hyps })
--                                , po = new_po }) 
                            m
                    lift $ tell [(lbl, expr, p)]
            )
        ] []
    where
        hyps = hypotheses pr 

find_parts :: (MonadState System m, MonadReader Theory m)
           => ProofParam
           -> Machine
--           -> [LatexDoc] 
--           -> [(Expr,Proof)]
           -> VisitorT (WriterT [(Tactic Expr,Tactic Proof)] m) () -- [(Expr,Proof)]
find_parts pr m = visitor 
        [   (   "part:a"
            ,   VEnvBlock $ \(formula :: [LatexDoc],()) _ -> do -- xs cases -> do
                    expr  <- lift_i $ get_expression (Just bool) formula 
--                        get_predicate m (par_ctx pr) WithoutFreeDummies formula
--                    let (Sequent ctx hyps _) = po pr
--                        new_po = Sequent ctx hyps expr
                    p         <- lift_i $ collect_proof_step pr m -- (pr { po = new_po }) m
                    lift $ tell [(expr, p)]
                    return ()
            )
        ] []

collect_proof_step :: (MonadState System m, MonadReader Theory m)
                   => ProofParam
                   -> Machine 
                   -> VisitorT m (Tactic Proof)
collect_proof_step pr m = do
        let hyps = hypotheses pr
        ((),step@(Step asrt _ asm _ _)) <- make_hard $ add_state empty_step $ find_assumptions
--        let step@(Step asrt _ asm ng _) = empty_step
        li   <- ask
--        let (Sequent ctx hyp goal) = po pr
--            new_goal = maybe goal id ng
--            new_po = Sequent ctx (M.elems asrt ++ M.elems asm ++ hyp) new_goal
        let pr2 = pr { hypotheses = asrt `union` asm `union` hyps }
                     -- , po = new_po } 
        (_,step) <- add_state step $ find_proof_step pr2 m
        case step of
            Step assrt prfs asm ng (Just p) -> do
--                let f k x = (x, prfs ! k)
                p <- if M.null assrt && M.null prfs
                    then return p
                    else if keysSet assrt == keysSet prfs
                    then return $ Tac.with_line_info li $ do
                        assrt <- forM (toList assrt) $ \(lbl,xp) -> do
                            xp <- xp
                            let p = prfs ! lbl
                            return (lbl,xp,p)
                        assert assrt p
                        -- Proof $ Assertion (M.mapWithKey f assrt) p li
                    else hard_error [Error "assertion labels and proofs mismatch" li]
                case ng of
                    Just g  -> return $ Tac.with_line_info li $ do
                        g <- g
                        asm <- forM (toList asm) $ \(lbl,x) -> do
                            x <- x
                            return (lbl,x)
                        assume asm g p
                        -- $ Proof $ Assume asm g p li
                    Nothing -> 
                        if M.null asm 
                        then return p
                        else hard_error [Error "assumptions must be accompanied by a new goal" li]
            _   -> hard_error [Error "expecting a single proof step" li]         

hint :: Monad m
--     => [LatexDoc] 
--     -> [(Label, LineInfo)]
     => VisitorT (WriterT [(Label, LineInfo)] m) ()
hint = visitor []
        [ ( "\\ref", VCmdBlock f ), ( "\\eqref", VCmdBlock f ) ]
    where
        f (b,()) = do
            li <- ask
            lift $ tell [(b,li)]

parse_calc :: ( MonadState System m, MonadReader Theory m )
           => ProofParam 
           -> Machine 
           -> VisitorT m (Tactic Calculation)
parse_calc pr m = do
    xs <- get_content
    case find_cmd_arg 2 ["\\hint"] xs of
        Just (step,kw,[rel,tx_hint],remainder)    -> do
            xp <- get_expression Nothing step
                    -- get_expr_with_ctx m (par_ctx pr) a
            op <- make_soft equal $ fromEitherM
                $ parse_oper 
                    (context m)
                    (all_notation m)
                    (concatMap flatten_li rel) 
            li  <- ask
            ((),hs) <- add_writer $ with_content li tx_hint $ hint
            hyp <- make_soft [] (do
                mapM find hs)
            r   <- with_content li remainder $ parse_calc pr m
            return $ Tac.with_line_info li $ do
                xp  <- make_soft ztrue xp
                r   <- r
                hyp <- sequence hyp
                return r { 
                    first_step = xp,
                    following  = (op,first_step r,hyp,line_info kw):following r }
        Nothing         -> do
            li <- ask
            xp <- get_expression Nothing xs
            return $ do
                xp <- make_soft ztrue xp
                -- fromEither ztrue $ get_expr_with_ctx m (par_ctx pr) xs
                return $ Calc (context m) ztrue xp [] li
        _               -> do
            li <- ask
            soft_error [Error "invalid hint" li]
            return $ do
                ctx <- get_context
                return $ Calc ctx ztrue ztrue [] li
    where
        hyps = hypotheses pr
--        find :: Map Label Expr -> Machine -> (Label,LineInfo) -> Either [Error] Expr
        find (xs,li) = maybe (hard_error [err_msg xs]) return 
            $ M.lookup xs $ M.union hyps $ M.map return $ M.unions $
                [ inv p0
                , inv_thm p0
                , inv p1
                , inv_thm p1
                , inits m
                , fact $ theory m
                ] ++ map g (elems $ events m)
--                foldM f [err_msg] $ elems $ events m
--                
----                either Right Left (do
--                err $ M.lookup xs $ hyps
--                err $ M.lookup xs $ inv p0
--                err $ M.lookup xs $ inv_thm p0
--                err $ M.lookup xs $ inv p1
--                err $ M.lookup xs $ inv_thm p1
--                err $ M.lookup xs $ inits m
--                err $ M.lookup xs $ fact $ theory m
--                foldM f [err_msg] $ elems $ events m
--                )
            where
                p0 = props m
                p1 = inh_props m
--                err (Just x) = Left x
--                err Nothing  = Right [err_msg]
                err_msg lbl      = Error (format "predicate is undefined: '{0}'" lbl) li
                g ev = M.unions
                    [ coarse $ new_sched ev
                    , new_guard ev
                    , action ev ]
--                f :: [Error] -> Event -> Either Expr [Error]
--                f _ ev = do
--                    err (M.lookup xs $ coarse $ new_sched ev)
--                    err $ M.lookup xs $ new_guard ev
--                    err $ M.lookup xs $ action ev

    -- assoc' n
get_table :: ( MonadState System m, MonadReader LineInfo m ) 
          => Theory
          -> EitherT [Error] m (Matrix Operator Assoc)
get_table th = do -- with_tracingM $ do
        let key = sort $ M.keys $ extends th
        traceM $ "KEY: " ++ show key
        !_ <- lift $ ST.get
        traceM $ "one more step!" -- show $ notation sys
        !tb <- lift $ ST.gets parse_table
        traceM $ "exists?"
        case M.lookup key tb of
            Just x -> do
                traceM "lookup: ..."
                return x
            Nothing -> do
                traceM "compute"
                let !x   = assoc' $ th_notation th
                    !new = insert key x tb
--                traceM $ show $ th_notation th
                lift $ ST.modify $ \s -> s { parse_table = new }
                traceM $ "end: " ++ show (G.size x)
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

