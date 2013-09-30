{-# LANGUAGE BangPatterns, FlexibleContexts, TupleSections, ScopedTypeVariables #-}
module Document.Machine where

    -- Modules
import Document.Expression
import Document.Visitor
import Document.Proof -- hiding ( context )
import Document.Refinement hiding ( parse_rule )

import Latex.Parser

import UnitB.AST
import UnitB.PO
import UnitB.Theory
import UnitB.SetTheory
import UnitB.FunctionTheory
import UnitB.Genericity

import Z3.Z3 

    -- Libraries
import           Control.Applicative hiding ( empty )
import           Control.Monad hiding ( guard )
import qualified Control.Monad.Reader.Class as R
import           Control.Monad.Trans
import           Control.Monad.Trans.RWS as RWS
import           Control.Monad.Trans.Either

import           Data.Char
import           Data.Functor.Identity
import           Data.Graph
import           Data.Map  as M hiding ( map, foldl, (\\) )
import           Data.List as L hiding ( union, insert, inits )
import qualified Data.Map as M
import qualified Data.Set as S

import System.IO

import Utilities.Format
import Utilities.Syntactic

list_file_obligations fn = do
        ct <- readFile fn
        return $ list_proof_obligations ct

list_proof_obligations :: String -> Either [Error] [(Machine, Map Label ProofObligation)]
list_proof_obligations ct = do
        xs <- list_machines ct
        forM xs $ \x -> do
            y <- proof_obligation x
            return (x,y)

list_machines :: String -> Either [Error] [Machine]
list_machines ct = do
        xs <- latex_structure ct
        ms <- all_machines xs
        return $ map snd $ toList $ ms

inject :: Monad m => c -> RWST a b c m d -> RWST a b e m d
inject s0 m = RWST f
    where
        f r s = do
            (x,s1,w) <- runRWST m r s0 
            return (x,s,w)
        
cycles xs = stronglyConnComp $ map f $ groupBy ((==) `on` fst) $ sort xs
    where
        eq (x,_) (y,_) = x == y
        f xs = (fst $ head xs, fst $ head xs, map snd xs)

parse_rule :: (Monad m)
           => String
           -> RuleParserParameter
           -> EitherT [Error] (RWST (Int,Int) [Error] Architecture m) Rule
parse_rule rule param = do
    (i,j) <- lift $ ask
    case M.lookup rule refinement_parser of
        Just f -> EitherT $ mapRWST (\x -> return (runIdentity x)) $
            runEitherT $ f rule param
        Nothing -> left [(format "invalid refinement rule: {0}" rule,i,j)]

refinement_parser :: Map String (
                  String
               -> RuleParserParameter
               -> EitherT [Error] (RWS (Int, Int) [Error] Architecture) Rule)
refinement_parser = fromList 
    [   ("disjunction", parse (disjunction, ()))
    ,   ("discharge", parse_discharge)
    ,   ("monotonicity", parse (Monotonicity, ()))
    ,   ("implication", parse (Implication, ()))
    ,   ("trading", parse (NegateDisjunct, ()))
    ,   ("transitivity", parse (Transitivity, ()))
    ,   ("psp", parse (PSP, ()))
    ,   ("induction", parse_induction)
    ]

check_acyclic :: (Monad m) => String -> [(Label,Label)] -> EitherT [Error] (RWST b [Error] d m) ()
check_acyclic x es = do
        let cs = cycles es
        toEither $ mapM_ (cycl_err_msg x) cs
    where
        cycle_msg x ys = format msg (x :: String) $ intercalate "," (map show ys)
            where
                msg = "A cycle exists in the {0}: {1}"
        cycl_err_msg _ (AcyclicSCC v) = return ()
        cycl_err_msg x (CyclicSCC vs) = tell [(cycle_msg x vs,0,0)]

trickle_down
        :: Monad m
        => Map Label Label 
        -> Map String a 
        -> (a -> a -> Either [String] a) 
        -> EitherT [Error] m (Map String a)
trickle_down s ms f = do -- error "not implemented"
            let rs = reverse $ map (\(AcyclicSCC v) -> v) $ cycles $ toList s
            foldM (\ms n -> 
                    case M.lookup n s of
                        Just anc  -> do
                            m <- hoistEither $ either 
                                (Left . map (\x -> (x,0,0))) Right 
                                $ f (ms ! show n) (ms ! show anc)
                            return $ insert (show n) m ms
                        Nothing -> return ms
                    ) ms rs

all_machines :: [LatexDoc] -> Either [Error] (Map String Machine)
all_machines xs = let { (x,_,_) = runRWS (runEitherT $ do
            ms <- foldM gather empty xs 
            ms <- toEither $ foldM (f type_decl) ms xs
            refs  <- lift $ RWS.gets ref_struct
            check_acyclic "refinement structure" $ toList refs

                -- take actual generic parameter from `type_decl'
            ms <- toEither $ foldM (f imports) ms xs
            ms <- trickle_down refs ms merge_struct
    
                -- take the types from `imports' and `type_decl`
            ms <- toEither $ foldM (f declarations) ms xs
            ms <- trickle_down refs ms merge_decl
                
                -- use the `declarations' of variables to check the
                -- type of expressions
            ms <- toEither $ foldM (f collect_expr) ms xs
            ms <- trickle_down refs ms merge_exprs
                
                -- use the label of expressions from `collect_expr' 
                -- in hints.
            ms <- toEither $ foldM (f collect_proofs) ms xs
            s  <- lift $ RWS.gets proof_struct
            check_acyclic "proof of liveness" s
            ms <- trickle_down refs ms merge_proofs
            return ms) () empty_arc }
        in x
    where
        gather ms (Env n _ c li)     
                | n == "machine"    = do
                    (name,cont) <- with_line_info li $ get_1_lbl c
                    let m        = empty_machine name
                    return (insert name m ms)
                | otherwise         = foldM gather ms c
        gather ms x                 = fold_docM gather ms x
        f pass ms (Env n _ c li)     
                | n == "machine"    = do
                    fromEither ms (do
                        (name,cont) <- with_line_info li $ get_1_lbl c
                        m           <- toEither $ pass cont (ms ! name)
                        return (insert name m ms))
                | otherwise         = foldM (f pass) ms c
        f pass ms x                 = fold_docM (f pass) ms x

type_decl :: [LatexDoc] -> Machine -> MSEither Error Architecture Machine
type_decl = visit_doc []
            [  (  "\\newset"
               ,  CmdBlock $ \(String name, String tag,()) m -> do
                    let th = theory m
                    let new_sort = Sort tag name 0
                    let new_type = USER_DEFINED new_sort []
                    toEither $ error_list
                        [ ( tag `member` all_types th
                          , format "a sort with name '{0}' is already declared" tag )
                        , ( tag `member` consts th
                          , format "a constant with name '{0}' is already declared" tag )
                        ]
                    let dummy = Var "x@@" new_type
                    let new_const = Var name $ set_type new_type
                    let hd = th 
                            {  types = insert 
                                    tag
                                    new_sort
                                    (types th) 
                            ,  consts = insert tag new_const $ consts th
                            ,  fact = insert 
                                    (label (tag ++ "-def"))
                                    (fromJust $ mzforall [dummy] mztrue 
                                        (zelem 
                                            (Right $ Word dummy) 
                                            (Right $ Word new_const)))
                                    (fact th)
                            }
                    return m { theory = hd } 
               )
            ,  (  "\\newevent"
               ,  CmdBlock $ \(evt,()) m -> do 
                        toEither $ error_list
                            [ ( evt `member` events m
                              , format "event '{0}' is already defined" evt )
                            ]
                        return m { events = insert evt (empty_event) $ events m } 
               )
            ,  (  "\\refines"
               ,  CmdBlock $ \(mch,()) m -> do
                        anc   <- lift $ gets ref_struct
                        (i,j) <- lift $ ask
                        when (_name m `member` anc) $ left [(format "Machines can only refine one other machine",i,j)]
                        lift $ modify $ \x -> x { ref_struct = insert (_name m) mch $ ref_struct x }
                        return m
               )
            ]

imports :: Monad m 
        => [LatexDoc] 
        -> Machine 
        -> MSEitherT Error Architecture m Machine 
imports = visit_doc 
            [   ( "use:set"
                , EnvBlock $ \(String cset,()) _ m -> do
                    let th = theory m
                    toEither $ error_list
                        [ ( not (cset `member` all_types th)
                          , format "Carrier set {0} undefined" cset )
                        ]
                    return m { theory = th {
                                extends = set_theory (USER_DEFINED (all_types th ! cset) []) : extends th } } 
                )
            ,   ( "use:fun"
                , EnvBlock $ \(String dset, String rset,()) _ m -> do
                    let th = theory m
                    toEither $ error_list 
                        [   ( not (dset `member` all_types th)
                            , format "Carrier set {0} undefined" dset )
                        ,   ( not (rset `member` all_types th)
                            , format "Carrier set {0} undefined" rset )
                        ]
                    let dtype = USER_DEFINED (all_types th ! dset) []
                    let rtype = USER_DEFINED (all_types th ! rset) []
                    return m { theory = th {
                                extends = function_theory dtype rtype : extends th } } 
                )
            ]
            []

    -- Todo: detect when the same variable is declared twice
    -- in the same declaration block.
declarations :: Monad m
             => [LatexDoc] 
             -> Machine 
             -> MSEitherT Error Architecture m Machine
declarations = visit_doc 
        [   (   "variable"
            ,   EnvBlock $ \() xs m -> do
                        vs <- get_variables (context m) xs
                        let inter = S.fromList (map fst vs) `S.intersection` keysSet (variables m)
                        toEither $ error_list 
                            [ ( not $ S.null inter
                              , format "repeated declaration: {0}" (intercalate ", " $ S.toList inter ))
                            ]
                        return m { variables = fromList vs `union` variables m} 
            )
        ,   (   "indices"
            ,   EnvBlock $ \(evt,()) xs m -> do
                        vs <- get_variables (context m) xs
                        toEither $ error_list
                            [ ( not (evt `member` events m) 
                              , format "event '{0}' is undeclared" evt )
                            ]
                        let old_event = events m ! evt
                        let var_names = map fst vs
                        let inter = S.fromList var_names `S.intersection` keysSet (indices old_event)
                        toEither $ error_list
                            [ ( not $ S.null inter
                              , format "repeated declaration: {0}" (intercalate ", " $ S.toList inter ) )
                            ]
                        let new_event = old_event { 
                            indices = fromList vs `union` indices old_event }
                        return m { events = insert evt new_event $ events m } 
            )
        ,   (   "constant"
            ,   EnvBlock $ \() xs m -> do
                        vs <- get_variables (context m) xs
                        return m { theory = (theory m) { 
                                consts = merge 
                                    (fromListWith (error "repeated definition") vs) 
                                    (consts $ theory m) } } 
            )
        ,   (   "dummy"
            ,   EnvBlock $ \() xs m -> do
                        vs <- get_variables (context m) xs
                        return m { theory = (theory m) { 
                                dummies = merge 
                                    (fromListWith (error "repeated definition") vs) 
                                    (dummies $ theory m) } } 
            )
        ] 
        []

    -- Todo: report an error if we create two assignments (or other events elements)
    -- with the same name
    -- Todo: guard the `insert` statements with checks for name clashes
    -- Todo: check scopes
collect_expr :: Monad m
             => [LatexDoc] 
             -> Machine 
             -> MSEitherT Error Architecture m Machine
collect_expr = visit_doc 
                --------------
                --  Events  --
                --------------
        [] [(   "\\evassignment"
            ,   CmdBlock $ \(ev, lbl, xs,()) m -> do
                        toEither $ error_list
                            [ ( not (ev `member` events m)
                              , format "event '{0}' is undeclared" ev )
                            ]
                        toEither $ error_list
                            [ ( lbl `member` action (events m ! ev)
                              , format "{0} is already used for another assignment" lbl )
                            ]
                        let old_event = events m ! ev
                        act   <- get_evt_part m old_event xs
                        let new_event = old_event { 
                                    action = insertWith 
                                        (error "name clash")  
                                        lbl act
                                        (action old_event) }
                        scope (context m) act (params old_event `merge` indices old_event)
                        return m {          
                                events  = insert ev new_event $ events m } 
            )
        ,   (   "\\evguard"
            ,   CmdBlock $ \(evt, lbl, xs,()) m -> do
                        toEither $ error_list
                            [   ( not (evt `member` events m)
                                , format "event '{0}' is undeclared" evt )
                            ]
                        let old_event = events m ! evt
                        let grds = guard old_event
                        toEither $ error_list
                            [   ( evt `member` grds
                                , format "{0} is already used for another guard" lbl )
                            ]
                        grd      <- get_evt_part m old_event xs
                        let new_event = old_event { 
                                    guard =  insert lbl grd grds  }
                        scope (context m) grd (indices old_event `merge` params old_event)
                        return m {          
                                events  = insert evt new_event $ events m } 
            )
        ,   (   "\\cschedule"
            ,   CmdBlock $ \(evt, lbl, xs,()) m -> do
                        toEither $ error_list
                            [ ( not (evt `member` events m)
                                , format "event '{0}' is undeclared" evt )
                            ]
                        let sc = case c_sched (events m ! evt) of
                                    Just x  -> x
                                    Nothing -> empty
                        toEither $ error_list
                            [ ( lbl `member` sc
                                , format "{0} is already used for another coarse schedule" lbl )
                            ]
                        let old_event = events m ! evt
                        sched <- get_evt_part m old_event xs
                        let new_event = old_event { 
                                    c_sched =  
                                        fmap (insert lbl sched) 
                                            ( c_sched old_event <|> Just empty ) }
                        scope (context m) sched (indices old_event) 
                        return m {          
                                events  = insert evt new_event $ events m } 
            )
        ,   (   "\\fschedule"
            ,   CmdBlock $ \(evt, lbl :: Label, xs,()) m -> do
                        toEither $ error_list
                            [ ( not (evt `member` events m)
                              , format "event '{0}' is undeclared" evt )
                            ]
                        let old_event = events m ! evt
                        sched <- get_evt_part m old_event xs
                        let event = old_event { 
                                    f_sched = Just sched }
                        scope (context m) sched (indices event) 
                        return m {          
                                events  = insert evt event $ events m } 
            )
                -------------------------
                --  Theory Properties  --
                -------------------------
        ,   (   "\\assumption"
            ,   CmdBlock $ \(lbl,xs,()) m -> do
                        let th = theory m
                        toEither $ error_list
                            [ ( lbl `member` fact th
                              , format "{0} is already used for another assertion" lbl )
                            ]
                        axm <- get_assert m xs
                        return m { 
                            theory = th { fact = insert lbl axm $ fact th } } 
            )
                --------------------------
                --  Program properties  --
                --------------------------
        ,   (   "\\initialization"
            ,   CmdBlock $ \(lbl,xs,()) m -> do
                        initp         <- get_assert m xs
                        toEither $ error_list
                            [ ( lbl `member` inits m
                              , format "{0} is already used for another invariant" lbl )
                            ]
                        return m {
                                inits = insert lbl initp $ inits m } 
            )
        ,   (   "\\invariant"
            ,   CmdBlock $ \(lbl,xs,()) m -> do
                        toEither $ error_list
                            [ ( lbl `member` inv (props m)
                              , format "{0} is already used for another invariant" lbl )
                            ]
                        invar         <- get_assert m xs
                        return m { 
                            props = (props m) { 
                                inv = insert lbl invar $ inv $ props m } } 
            )
        ,   (   "\\transient"      
            ,   CmdBlock $ \(ev, lbl, xs,()) m -> do
                        toEither $ error_list
                            [ ( not (ev `member` events m)
                              , format "event '{0}' is undeclared" ev )
                            ]
                        toEither $ error_list
                            [   ( lbl `member` transient (props m)
                                , format "{0} is already used for another program property" lbl )
                            ]
                        tr            <- get_assert m xs
                        let prop = Transient (free_vars (context m) tr) tr ev
                        let old_prog_prop = transient $ props m
                        let new_props     = insert lbl prop $ old_prog_prop
                        return m {
                            props = (props m) {
                                transient = new_props } } 
            )
        ,   (   "\\constraint"
            ,   CmdBlock $ \(lbl,xs,()) m -> do
                        toEither $ error_list
                            [ ( lbl `member` constraint (props m)
                              , format "{0} is already used for another invariant" lbl )
                            ]
                        pre           <- get_assert m xs
                        return m { 
                            props = (props m) { 
                                constraint = insert lbl (Co (elems $ free_vars (context m) pre) pre) 
                                    $ constraint $ props m } } 
            )
        ,   (   "\\safety"
            ,   CmdBlock $ \(lbl, pCt, qCt,()) m -> do
                    let prop = safety $ props m
                    (p,q)    <- toEither (do
                        p    <- fromEither ztrue $ get_assert m pCt
                        q    <- fromEither ztrue $ get_assert m qCt
                        error_list 
                            [   ( lbl `member` prop
                                , format "safety property {0} already exists" lbl )
                            ] 
                        return (p,q))
                    let ctx = context m
                    let dum = free_vars ctx p `union` free_vars ctx q
                    let new_prop = Unless (M.elems dum) p q
                    return m { props = (props m) 
                        { safety = insert lbl new_prop $ prop 
                        , constraint = insert lbl 
                            (Co (M.elems dum) (zimplies (zand p $ znot q) $ primed (variables m) (zor p q)))
                            (constraint $ props m) } } 
            )
        ,   (   "\\progress"
            ,   CmdBlock $ \(lbl, pCt, qCt,()) m -> do
                    let prop = progress $ props m
                    (p,q)    <- toEither (do
                        p    <- fromEither ztrue $ get_assert m pCt
                        q    <- fromEither ztrue $ get_assert m qCt
                        error_list 
                            [   ( lbl `member` prop
                                , format "progress property {0} already exists" lbl )
                            ] 
                        return (p,q))
                    let ctx = context m
                    let dum = S.fromList (elems $ free_vars ctx p) 
                                `S.union` S.fromList (elems $ free_vars ctx q)
                    let new_prop = LeadsTo (S.elems dum) p q
                    return m { props = (props m) 
                        { progress   = insert lbl new_prop $ prop 
                        , derivation = insert lbl (Rule Add) $ derivation $ props m
                        } } 
            )
        ]

scope :: (Monad m, R.MonadReader (Int,Int) m)
      => Context -> Expr -> Map String Var 
      -> EitherT [Error] m ()
scope ctx xp vs = do
    let fv          = keysSet $ free_vars ctx xp
    let decl_v      = keysSet vs
    let undecl_v    = S.toList (fv `S.difference` decl_v)
    (i,j)           <- R.ask
    if fv `S.isSubsetOf` decl_v
    then return ()
    else left [(format "Undeclared variables: {0}" 
                (intercalate ", " undecl_v), i,j)]

collect_proofs :: Monad m 
               => [LatexDoc] 
               -> Machine
               -> MSEitherT Error Architecture m Machine
collect_proofs = visit_doc
        [   (   "proof"
            ,   EnvBlock $ \(po,()) xs m -> do
                    let lbl = composite_label [ _name m, po ]
                    toEither $ error_list 
                        [   ( lbl `member` proofs (props m)
                            , format "a proof for {0} already exists" lbl )
                        ] 
                    p           <- collect_proof_step empty m xs
                    return m { 
                        props = (props m) { 
                            proofs = insert lbl p $ 
                                    proofs $ props m } } 
            )
        ] [ (   "\\refine"
            ,   CmdBlock $ \(goal,String rule,hyps,hint,()) m -> do
                    toEither $ error_list
                        [   ( not (goal `member` (progress $ props m))
                            , format "the goal is an undefined progress property {0}" goal )
                        ]
                    let prog = progress $ props m
                    let saf  = safety $ props m
                    li@(i,j)      <- lift $ ask
                    r <- parse_rule (map toLower rule) (RuleParserParameter m prog saf goal hyps hint)
                    return m { props = (props m) { derivation = insert goal r $ derivation $ props m } } 
            )
        ]

parse_machine :: FilePath -> IO (Either [Error] [Machine])
parse_machine fn = do
        ct <- readFile fn
        return $ list_machines ct
        