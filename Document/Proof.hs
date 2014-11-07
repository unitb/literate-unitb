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

import Logic.Expr
import Logic.Operator
import Logic.Proof as LP

    -- Libraries
import           Control.Monad hiding ( guard )
import           Control.Monad.Reader.Class hiding ( reader )
import           Control.Monad.State.Class as ST
import qualified Control.Monad.Writer.Class as W
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
import           Data.Tuple

import           Utilities.Error
import           Utilities.Format
import           Utilities.Syntactic hiding (line)

context :: Machine -> Context
context m = step_ctx m `merge_ctx` theory_ctx (theory m)

data ProofStep = Step 
       { assertions  :: Map Label (Tactic Expr)    -- assertions
       , subproofs   :: Map Label (Tactic Proof)   -- proofs of assertions
       , assumptions :: Map Label (Tactic Expr)    -- assumptions
       , theorem_ref :: [Tactic (TheoremRef, LineInfo)]
       , new_goal    :: Maybe (Tactic Expr)        -- new_goal
       , main_proof  :: Maybe (Tactic Proof)       -- main proof        
       }

data ProofParam = ProofParam 
    { notat      :: Notation
    }

empty_pr :: Theory -> ProofParam
empty_pr th = ProofParam (th_notation th)

--par_ctx :: ProofParam -> Context
--par_ctx pr = ctx pr `merge_ctx` Context M.empty (locals pr) M.empty M.empty M.empty

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
            hard_error [Error (format "an assumption {0} already exists" lbl) li]
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
            hard_error [Error (format "an assertion {0} already exists" lbl) li]
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
            hard_error [Error (format "a proof for assertion {0} already exists" lbl) li]
        else
            ST.put $ s { subproofs = insert lbl prf $ subproofs s }

empty_step :: ProofStep
empty_step = Step empty empty empty [] Nothing Nothing

find_assumptions :: (MonadState System m, MonadReader Theory m)
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
            ,   VEnvBlock $ \(One (_ :: Label)) _ -> return ()
            )
        ] [ (   "\\assume"
            ,   VCmdBlock $ \(lbl,formula :: [LatexDoc]) -> do
                    expr   <- lift_i $ get_expression (Just bool) formula 
                    add_assumption lbl expr 
            )
        ,   (   "\\assert"
            ,   VCmdBlock $ \(lbl,formula :: [LatexDoc]) -> do
                    expr   <- lift_i $ get_expression (Just bool) formula 
                    add_assert lbl expr
            )
        ,   (   "\\goal"
            ,   VCmdBlock $ \(One (formula :: [LatexDoc])) -> do
                    expr   <- lift_i $ get_expression (Just bool) formula 
                    set_goal expr
            )
        ,   (   "\\using"
            ,   VCmdBlock $ \(One refs) -> do
                    li      <- ask
                    s       <- lift $ lift $ ST.get
                    (((),hs),s) <- add_state s $ add_writer $ with_content li refs hint
                    lift $ lift $ ST.put s
                    add_refs hs
--                    li <- ask 
--                    lift $ do
--                        ((),hs) <- lift $ runWriterT $ run_visitor li refs $ hint
--                        add_refs hs                    
            )       
        ]


intersectionsWith :: Ord a => (b -> b -> b) -> [Map a b] -> Map a b
intersectionsWith _ [] = error "intersection of an empty list of sets"
intersectionsWith f (x:xs) = L.foldl (intersectionWith f) x xs

intersections :: Ord a => [Map a b] -> Map a b
intersections = intersectionsWith const

by_symmetry :: Monad m
            => [Var]
            -> Label
            -> Maybe Label
            -> TacticT m Proof
            -> TacticT m Proof
by_symmetry vs hyp mlbl proof = do
        cs <- lookup_hypothesis (ThmRef hyp [])
        let err0 = format "expecting a disjunction\n{0}: {1}" hyp $ pretty_print' cs
        lbl  <- maybe (fresh_label "symmetry") return mlbl
        goal <- get_goal
        case cs of
            FunApp f cs
                | name f /= "or" -> fail err0
                | otherwise -> do
                    ps <- forM (permutations vs) $ \us -> do
                        hyp <- get_named_hyps
                        asm <- get_nameless_hyps
                        let rn = zip vs us
                            new_hyp = M.filter p $ M.map f hyp 
                            new_asm = L.filter p $ L.map f asm
                            f h = rename_all rn h
                            p h = any (`S.member` used_var h) vs
                        new_asm <- forM new_asm $ \x -> do
                            lbl <- fresh_label "H"
                            return (x,lbl)
                        return $ M.fromList $ map swap (toList new_hyp) ++ new_asm
                    let common = (head cs,hyp) : M.toList (intersections ps)
                        named  = map swap common
                        thm = zforall vs (zall $ map fst common) goal
                        f xs = zip vs $ map Word xs
                    cs <- forM cs $ \x -> return (hyp,x,easy)
                    assert [(lbl,thm,clear_vars vs $ do
                            us <- forM vs $ \(Var n t) -> new_fresh n t
                            free_vars_goal (zip (map name vs) 
                                                (map name us)) 
                              $ assume named goal proof)] $
                        instantiate_hyp_with thm (map f $ permutations vs) $ 
                            by_cases cs
            _ -> fail err0

indirect_inequality :: Monad m
                    => Either () () 
                    -> BinOperator 
                    -> Var
                    -> TacticT m Proof
                    -> TacticT m Proof
indirect_inequality dir op zVar@(Var _ t) proof = do 
        x_decl <- new_fresh "x" t
        y_decl <- new_fresh "y" t
        z_decl <- new_fresh "z" t
        let x         = Word x_decl
            y         = Word y_decl
            z         = Word z_decl
            rel       = mk_expr op
            rel_z x y = case dir of
                        Left ()  -> rel z x `mzimplies` rel z y
                        Right () -> rel y z `mzimplies` rel x z
            thm_rhs x y = mzforall [z_decl] mztrue $ rel_z x y
        thm  <- make_expr $ mzforall [x_decl,y_decl] mztrue $ rel x y `mzeq` thm_rhs x y
        goal <- get_goal
        let is_op f x y = either (const False) id $ do
                            xp <- mk_expr op x y
                            return $ FunApp f [x,y] == xp
        case goal of
            FunApp f [lhs,rhs] 
                | is_op f x y -> do
                    new_goal <- make_expr $ mzforall [z_decl] mztrue $ thm_rhs lhs rhs
                    g_lbl   <- fresh_label "new:goal"
                    thm_lbl <- fresh_label "indirect:ineq"
                    assert 
                        [ (thm_lbl, thm, easy)       -- (Ax,y:: x = y == ...)
                        , (g_lbl, new_goal, do       -- (Az:: z ≤ lhs => z ≤ rhs)
                                free_goal (name z_decl) (name zVar) proof) ]
                        $ do
                            lbl <- fresh_label "inst"
                            instantiate_hyp                       -- lhs = rhs
                                thm lbl                             -- | we could instantiate indirect
                                [ (x_decl,lhs)                      -- | inequality explicitly 
                                , (y_decl,rhs) ]                    -- | for that, we need hypotheses 
                                easy                                -- | to be named in sequents
                                                              
            _ -> fail $ "expecting an inequality:\n" ++ pretty_print' goal

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
                                free_goal (name z_decl) (name zVar) proof) ]
                        $ do
                            lbl <- fresh_label "inst"
                            instantiate_hyp                       -- lhs = rhs
                                thm lbl                             -- | we could instantiate indirect
                                [ (x_decl,lhs)                      -- | inequality explicitly 
                                , (y_decl,rhs) ]                    -- | for that, we need hypotheses 
                                easy                                -- | to be named in sequents
                                                              
            _ -> fail $ "expecting an equality:\n" ++ pretty_print' goal

--by_antisymmetry :: Monad m 
--                => BinOperator 
--                -> 

find_proof_step :: (MonadState System m, MonadReader Theory m, Monad m)
                => ProofParam
                -> VisitorT (StateT ProofStep m) ()
find_proof_step pr = visitor
        [   (   "calculation"
            ,   VEnvBlock $ \() _ -> do
                    li <- ask
                    cc <- lift_i $ parse_calc pr
                    set_proof $ LP.with_line_info li $ do
                        cc <- cc
                        case infer_goal cc (notat pr) of
                            Right cc_goal -> do
                                    return (ByCalc $ cc { goal = cc_goal })
                            Left msg      -> hard_error [Error (format "type error: {0}" msg) li]
                    return ()
            )
                -- TODO: make into a command
        ,   (   "free:var"
            ,   VEnvBlock $ \(String from,String to) _ -> do
                    li    <- ask
                    proof <- lift_i $ collect_proof_step pr
                    set_proof $ LP.with_line_info li $ do
                        free_goal from to proof
            )
        ,   (   "by:cases"
            ,   VEnvBlock $ \() _ -> do
                    li         <- ask
                    ((),cases) <- lift_i $ add_writer $ find_cases pr
                    set_proof $ LP.with_line_info li $ do
                        xs <- forM cases $ \(lbl,xp,pr) -> do
                            x <- xp
                            return (lbl,x,pr)
                        by_cases xs
            )
        ,   (   "by:parts"
            ,   VEnvBlock $ \() _ -> do
                    li    <- ask
                    ((),cases) <- lift_i $ add_writer $ find_parts pr
                    set_proof $ LP.with_line_info li $ do
                        xs <- forM cases $ \(xp,pr) -> do
                            x <- xp
                            return (x,pr)
                        by_parts xs
            )
        ,   (   "subproof"
            ,   VEnvBlock $ \(One lbl) _ -> do
                    li     <- ask
                    proofs <- lift $ ST.get
                    unless (lbl `M.member` assertions proofs)
                            (hard_error [Error (format "invalid subproof label: {0}" lbl) li])
                    p <- lift_i $ collect_proof_step pr-- (change_goal pr new_goal) m
                    add_proof lbl p
            )
        ,   (   "indirect:equality"
            ,   VEnvBlock $ \(String dir,rel,String zVar) _ -> do
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
                    set_proof $ LP.with_line_info li $ do
                        var <- get_dummy zVar
                        indirect_equality dir op 
                                var p
            )
        ,   (   "indirect:inequality"
            ,   VEnvBlock $ \(String dir,rel,String zVar) _ -> do
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
                    set_proof $ LP.with_line_info li $ do
                        var <- get_dummy zVar
                        indirect_inequality dir op 
                                var p
            )
        ,   (   "by:symmetry"
            ,   VEnvBlock $ \(lbl,vars) _ -> do
                    li <- ask
                    p <- lift_i $ collect_proof_step pr
                    set_proof $ LP.with_line_info li $ do
                        vs <- mapM (get_dummy . toString) vars 
                        by_symmetry vs lbl Nothing p
            )
        ] [ (   "\\easy"
            ,   VCmdBlock $ \() -> do
                    li <- ask        
                    set_proof $ LP.with_line_info li easy
            )
        ] 

find_cases :: (MonadState System m, MonadReader Theory m)
           => ProofParam
           -> VisitorT (WriterT [(Label,Tactic Expr,Tactic Proof)] m) ()
find_cases pr = visitor 
        [   (   "case"
            ,   VEnvBlock $ \(lbl,formula :: [LatexDoc]) _ -> do
                    expr      <- lift_i $ get_expression (Just bool) formula 
                    p         <- lift_i $ collect_proof_step pr
                    lift $ tell [(lbl, expr, p)]
            )
        ] []

find_parts :: (MonadState System m, MonadReader Theory m)
           => ProofParam
           -> VisitorT (WriterT [(Tactic Expr,Tactic Proof)] m) () -- [(Expr,Proof)]
find_parts pr = visitor 
        [   (   "part:a"
            ,   VEnvBlock $ \(One (formula :: [LatexDoc])) _ -> do -- xs cases -> do
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
        ((),step) <- make_hard $ add_state empty_step $ find_assumptions
        li   <- ask
        (_,step) <- add_state step $ find_proof_step pr
        case main_proof step of
            Just p -> do
                let assrt   = assertions step
                    prfs    = subproofs step
                    asm     = assumptions step
                    ng      = new_goal step
                    thm_ref = theorem_ref step
                p <- if keysSet assrt == keysSet prfs
                     then return $ LP.with_line_info li $ do
                        thm <- sequence thm_ref
                        use_theorems thm $ do
                            assrt <- forM (toList assrt) $ \(lbl,xp) -> do
                                xp <- xp
                                let p = prfs ! lbl
                                return (lbl,xp,p)
                            assert assrt p
                    else hard_error [Error "assertion labels and proofs mismatch" li]
                case ng of
                    Just g  -> return $ LP.with_line_info li $ do
                        thm <- sequence thm_ref
                        use_theorems thm $ do
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

hint :: ( MonadReader Theory m
        , MonadState System m
        , W.MonadWriter [Tactic (TheoremRef, LineInfo)] m)
     => VisitorT m ()
hint = visitor []
        [ ( "\\ref", VCmdBlock f )
        , ( "\\eqref", VCmdBlock f )
        , ( "\\inst", VCmdBlock g )
        , ( "\\eqinst", VCmdBlock g )
        ]
    where
        g (lbl,subst) = do
                li <- ask
                ((),w) <- with_content li subst $ add_writer $ visitor []
                    [ ( "\\subst", VCmdBlock $ \(String var, expr) -> do
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
        f (One b) = do
            li <- ask
            lift $ W.tell [return (ThmRef b [],li)]

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
            return $ LP.with_line_info (line_info kw) $ do
                hs  <- sequence hs
                xp  <- make_soft ztrue xp
                add_step xp op hs calc
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
                               
data FreeVarOpt = WithFreeDummies | WithoutFreeDummies

remove_ref :: [Char] -> [Char]
remove_ref ('\\':'r':'e':'f':'{':xs) = remove_ref xs
remove_ref ('}':xs) = remove_ref xs
remove_ref (x:xs)   = x:remove_ref xs
remove_ref []       = []

get_expr_with_ctx :: ( Monad m, Monoid b ) 
                  => Machine
                  -> Context
                  -> [LatexDoc] 
                  -> EitherT [Error] (RWST LineInfo b System m)  Expr
get_expr_with_ctx m ctx ys = do
        y  <- parse_expr 
                (context m `merge_ctx` ctx) 
                (all_notation m)
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

get_expression :: ( MonadReader Theory m
                  , MonadState System m )
               => Maybe Type
               -> [LatexDoc]
               -> VisitorT m (Tactic Expr)
get_expression t ys = do
            li <- if L.null xs
                then ask
                else return $ line_info xs
            th  <- lift $ ask            
            sys <- lift $ ST.get
            return $ LP.with_line_info li $ do
                ctx <- get_context
                x   <- lift $ flip runReaderT li $ 
                        flip evalStateT sys $ 
                        runEitherT $ 
                        parse_expr 
                            ctx (th_notation th)
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
        x  <- parse_expr ctx
                (th_notation th)
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
                         `merge_ctx` theory_ctx (theory m)
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
          -> EitherT [Error] (RWST LineInfo () System Tactic) Expr
predicate t ys n = do
        ctx <- lift2 $ get_context
        li <- lift $ lift $ if L.null xs
            then get_line_info
            else return $ line_info xs
        x <- parse_expr 
                ctx n
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

