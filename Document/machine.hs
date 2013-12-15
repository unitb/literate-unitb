{-# LANGUAGE BangPatterns, FlexibleContexts, TupleSections, ScopedTypeVariables #-}
module Document.Machine where

    --
    -- Modules
    --
import Document.Expression
import Document.Visitor
import Document.Proof -- hiding ( context )
import Document.Refinement hiding ( parse_rule )

import Latex.Parser

import Logic.Const
import Logic.Expr
import Logic.ExpressionStore ( ExprStore )

import SummaryGen

import UnitB.AST
import UnitB.PO

import Theories.SetTheory
import Theories.FunctionTheory

import Z3.Z3 

    --
    -- Libraries
    --
import           Control.Monad hiding ( guard )
import           Control.Monad.Trans.State ( runStateT )
import qualified Control.Monad.Reader.Class as R
import           Control.Monad.Trans
import           Control.Monad.Trans.Either
import           Control.Monad.Trans.RWS as RWS
import           Control.Monad.Trans.State ( StateT )

import           Data.Char
import           Data.Functor.Identity
import           Data.Graph
import           Data.Map  as M hiding ( map, foldl, (\\) )
import           Data.Maybe as M ( maybeToList, isJust, isNothing ) 
import qualified Data.Maybe as M
import           Data.List as L hiding ( union, insert, inits )
import qualified Data.Set as S

import Utilities.Format
import Utilities.Syntactic

list_file_obligations :: FilePath
                       -> IO (Either [Error] [(Machine, Map Label Sequent)])
list_file_obligations fn = do
        ct <- readFile fn
        return $ list_proof_obligations fn ct

list_proof_obligations :: FilePath -> String
                       -> Either [Error] [(Machine, Map Label Sequent)]
list_proof_obligations fn ct = do
        xs <- list_machines fn ct
        forM xs $ \x -> do
            y <- proof_obligation x
            return (x,y)

list_machines :: FilePath -> String 
              -> Either [Error] [Machine]
list_machines fn ct = do
        xs <- latex_structure fn ct
        ms <- all_machines xs
        return $ map snd $ toList $ machines ms
        
parse_rule :: (Monad m)
           => String
           -> RuleParserParameter
           -> EitherT [Error] (RWST LineInfo [Error] System m) Rule
parse_rule rule param = do
    li <- lift $ ask
    case M.lookup rule refinement_parser of
        Just f -> EitherT $ mapRWST (\x -> return (runIdentity x)) $
            runEitherT $ f rule param
        Nothing -> left [Error (format "invalid refinement rule: {0}" rule) li]

refinement_parser :: Map String (
                  String
               -> RuleParserParameter
               -> EitherT [Error] (RWS LineInfo [Error] System) Rule)
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

check_acyclic :: (Monad m) => String 
              -> [(Label,Label)] 
              -> LineInfo
              -> EitherT [Error] (RWST b [Error] d m) ()
check_acyclic x es li = do
        let cs = cycles es
        toEither $ mapM_ (cycl_err_msg x) cs
    where
        cycle_msg x ys = format msg (x :: String) $ intercalate ", " (map show ys)
            where
                msg = "A cycle exists in the {0}: {1}"
        cycl_err_msg _ (AcyclicSCC _) = return ()
        cycl_err_msg x (CyclicSCC vs) = tell [Error (cycle_msg x vs) li]

trickle_down
        :: Monad m
        => Map Label Label 
        -> Map String a 
        -> (a -> a -> Either [String] a) 
        -> LineInfo
        -> EitherT [Error] m (Map String a)
trickle_down s ms f li = do
            let rs = map (\(AcyclicSCC v) -> v) $ cycles $ toList s
            foldM (\ms n -> 
                    case M.lookup n s of
                        Just anc  -> do
                            m <- hoistEither $ either 
                                (Left . map (\x -> Error x li)) Right 
                                $ f (ms ! show n) (ms ! show anc)
                            return $ insert (show n) m ms
                        Nothing -> return ms
                    ) ms rs

all_machines :: [LatexDoc] -> Either [Error] System
all_machines xs = do
        ms <- x
        return $ s { machines = ms }
    where
        (x,s,_) = runRWS (runEitherT $ read_document xs) () empty_system

produce_summaries :: System -> IO ()
produce_summaries sys = 
        void $ runStateT (do
            let ms = machines sys
            forM_ (M.elems ms) $ \m -> 
                forM_ (toList $ events m) $ \(lbl,evt) -> do
--                    liftIO $ putStrLn $ format "{0} - {1}" (_name m) lbl
                    xs <- focus' (summary lbl evt :: (StateT ExprStore IO) String)
                    liftIO $ writeFile (show (_name m) ++ "_" ++ rename lbl ++ ".tex") xs
            ) sys
    where
        rename lbl = map f $ show lbl
        f ':' = '-'
        f x   = x
        
read_document xs = do
            ms <- foldM gather empty xs 
            lift $ RWS.modify (\s -> s { 
                machines = ms })
            ms <- toEither $ foldM (f type_decl) ms xs
            refs  <- lift $ RWS.gets ref_struct
            let li = line_info xs
            check_acyclic "refinement structure" (toList refs) li
--            ms <- trickle_down refs ms merge_types
            ms <- trickle_down refs ms merge_struct li

                -- take actual generic parameter from `type_decl'
            ms <- toEither $ foldM (f imports) ms xs
            ms <- trickle_down refs ms merge_import li
    
                -- take the types from `imports' and `type_decl`
            ms <- toEither $ foldM (f declarations) ms xs
            ms <- trickle_down refs ms merge_decl li
                
                -- use the `declarations' of variables to check the
                -- type of expressions
            ms <- toEither $ foldM (f collect_expr) ms xs
            ms <- trickle_down refs ms merge_exprs li
                
                -- use the label of expressions from `collect_expr' 
                -- in hints.
            ms <- toEither $ foldM (f collect_proofs) ms xs
            ms <- trickle_down refs ms merge_proofs li
            toEither $ forM_ (M.elems ms) 
                $ deduct_schedule_ref_struct li
            s  <- lift $ RWS.gets proof_struct
--            let !() = unsafePerformIO $ print s
            check_acyclic "proof of liveness" s li
            return ms
    where
        gather ms (Env n _ c li)     
                | n == "machine"    = do
                    (name,_) <- with_line_info li $ get_1_lbl c
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

type_decl :: [LatexDoc] -> Machine -> MSEither Error System Machine
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
                        sys   <- lift $ gets machines
                        li    <- lift $ ask
                        unless (show mch `member` sys) $ left [Error (format "Machine {0} refines a non-existant machine: {1}" (_name m) mch) li]
                        when (_name m `member` anc) $ left [Error (format "Machines can only refine one other machine") li]
                        lift $ modify $ \x -> x { ref_struct = insert (_name m) mch $ ref_struct x }
                        return m
               )
            ]

imports :: Monad m 
        => [LatexDoc] 
        -> Machine 
        -> MSEitherT Error System m Machine 
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
             -> MSEitherT Error System m Machine
declarations = visit_doc []
        [   (   "\\variable"
            ,   CmdBlock $ \(xs,()) m -> do
                        vs <- get_variables (context m) xs
                        let inter = S.fromList (map fst vs) `S.intersection` keysSet (variables m)
                        toEither $ error_list 
                            [ ( not $ S.null inter
                              , format "repeated declaration: {0}" (intercalate ", " $ S.toList inter ))
                            ]
                        return m { variables = fromList vs `union` variables m} 
            )
        ,   (   "\\indices"
            ,   CmdBlock $ \(evt,xs,()) m -> do
                        vs <- get_variables (context m) xs
                        toEither $ error_list
                            [ ( not (evt `member` events m) 
                              , format "event '{0}' is undeclared" evt )
                            ]
                        let old_event = events m ! evt
                            var_names = map fst vs
                            inter = S.fromList var_names `S.intersection` 
                                    ( keysSet (params old_event) `S.union` keysSet (indices old_event) )
                        toEither $ error_list
                            [ ( not $ S.null inter
                              , format "repeated declaration: {0}" (intercalate ", " $ S.toList inter ) )
                            ]
                        let new_event = old_event { 
                            indices = fromList vs `union` indices old_event }
                        return m { events = insert evt new_event $ events m } 
            )
        ,   (   "\\param"
            ,   CmdBlock $ \(evt,xs,()) m -> do
                        vs <- get_variables (context m) xs
                        toEither $ error_list
                            [ ( not (evt `member` events m) 
                              , format "event '{0}' is undeclared" evt )
                            ]
                        let old_event = events m ! evt
                            var_names = map fst vs
                            inter = S.fromList var_names `S.intersection` 
                                    ( keysSet (params old_event) `S.union` keysSet (indices old_event) )
                        toEither $ error_list
                            [ ( not $ S.null inter
                              , format "repeated declaration: {0}" (intercalate ", " $ S.toList inter ) )
                            ]
                        let new_event = old_event { 
                            params = fromList vs `union` params old_event }
                        return m { events = insert evt new_event $ events m } 
            )
        ,   (   "\\constant"
            ,   CmdBlock $ \(xs,()) m -> do
                        vs <- get_variables (context m) xs
                        return m { theory = (theory m) { 
                                consts = merge 
                                    (fromListWith (error "repeated definition") vs) 
                                    (consts $ theory m) } } 
            )
        ,   (   "\\dummy"
            ,   CmdBlock $ \(xs,()) m -> do
                        vs <- get_variables (context m) xs
                        return m { theory = (theory m) { 
                                dummies = merge 
                                    (fromListWith (error "repeated definition") vs) 
                                    (dummies $ theory m) } } 
            )
        ]

tr_hint :: Monad m
        => Machine
        -> Label
        -> [LatexDoc]
        -> ( [(String,Expr)], Maybe Label )
        -> RWST LineInfo [Error] System m ( [(String,Expr)], Maybe Label )
tr_hint m lbl = visit_doc []
        [ ( "\\index"
          , CmdBlock $ \(String x, xs, ()) (ys,z) -> do
                let evt = events m ! lbl
                expr <- get_expr m xs
                toEither $ error_list 
                    [ ( not $ x `member` indices evt 
                      , format "'{0}' is not an index of '{1}'" x lbl )
                    ]
                return $ ((x,expr):ys,z))
        , ( "\\lt"
          , CmdBlock $ \(prog,()) (ys,z) -> do
--                let progs = progress (props m)
                toEither $ error_list 
                    [ ( not $ isNothing z
                      , format "Only one progress property needed for '{0}'" lbl )
                    ]
--                let prop = progs ! prog
                return (ys,Just prog))
        ]
    

    -- Todo: report an error if we create two assignments (or other events elements)
    -- with the same name
    -- Todo: guard the `insert` statements with checks for name clashes
    -- Todo: check scopes
collect_expr :: Monad m
             => [LatexDoc] 
             -> Machine 
             -> MSEitherT Error System m Machine
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
                            grds = guard old_event
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
                        let sc = sched (events m ! evt)
                        toEither $ error_list
                            [ ( lbl `member` sc
                                , format "{0} is already used for another schedule" lbl )
                            ]
                        let old_event = events m ! evt
                        sch <- get_evt_part m old_event xs
                        let new_event = old_event { 
                                    sched = insert lbl sch
                                            ( sched old_event ) }
                        scope (context m) sch (indices old_event) 
                        return m {          
                                events  = insert evt new_event $ events m } 
            )
        ,   (   "\\fschedule"
            ,   CmdBlock $ \(evt, lbl :: Label, xs,()) m -> do
                        toEither $ error_list
                            [ ( not (evt `member` events m)
                                , format "event '{0}' is undeclared" evt )
                            ]
                        let sc = sched (events m ! evt)
                        toEither $ error_list
                            [ ( lbl `member` sc
                                , format "{0} is already used for another schedule" lbl )
                            ]
                        let old_event = events m ! evt
                        sch <- get_evt_part m old_event xs
                        let new_event = old_event { 
                                    sched = insert lbl sch
                                            ( sched old_event ) }
                        scope (context m) sch (indices old_event) 
                        return m {          
                                events  = insert evt new_event $ events m } 
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
            ,   CmdBlock $ \(ev, n, lbl, xs,()) m -> do
                        toEither $ error_list
                            [ ( not (ev `member` events m)
                              , format "event '{0}' is undeclared" ev )
                            , ( lbl `member` transient (props m)
                              , format "{0} is already used for another program property" lbl )
                            ]
                        tr            <- get_assert m xs
                        let prop = Transient (free_vars (context m) tr) tr ev n empty Nothing
                            old_prog_prop = transient $ props m
                            new_props     = insert lbl prop $ old_prog_prop
                        return m {
                            props = (props m) {
                                transient = new_props } } 
            )
        ,   (   "\\transientB"      
            ,   CmdBlock $ \(ev, n, lbl, hint, xs,()) m -> do
                        toEither $ error_list
                            [ ( not (ev `member` events m)
                              , format "event '{0}' is undeclared" ev )
                            ]
                        toEither $ error_list
                            [   ( lbl `member` transient (props m)
                                , format "{0} is already used for another program property" lbl )
                            ]
                        tr            <- get_assert m xs
                        (hints,lt)    <- toEither $ tr_hint m ev hint ([],Nothing)
                        let prop = Transient (free_vars (context m) tr) tr ev n (fromList hints) lt
                            old_prog_prop = transient $ props m
                            new_props     = insert lbl prop $ old_prog_prop
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
                    let new_prop = Unless (M.elems dum) p q Nothing
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

scope :: (Monad m, R.MonadReader LineInfo m)
      => Context -> Expr -> Map String Var 
      -> EitherT [Error] m ()
scope ctx xp vs = do
    let fv          = keysSet $ free_vars ctx xp
    let decl_v      = keysSet vs
    let undecl_v    = S.toList (fv `S.difference` decl_v)
    li             <- R.ask
    if fv `S.isSubsetOf` decl_v
    then return ()
    else left [Error (format "Undeclared variables: {0}" 
                      (intercalate ", " undecl_v)) li]

remove_ref ('\\':'r':'e':'f':'{':xs) = remove_ref xs
remove_ref ('}':xs) = remove_ref xs
remove_ref (x:xs)   = x:remove_ref xs
remove_ref []       = []

collect_proofs :: Monad m 
               => [LatexDoc] 
               -> Machine
               -> MSEitherT Error System m Machine
collect_proofs = visit_doc
        [   (   "proof"
            ,   EnvBlock $ \(po,()) xs m -> do
                    let po_lbl = label $ remove_ref $ concatMap flatten po
                    let lbl = composite_label [ _name m, po_lbl ]
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
                        [   ( not (goal `member` (progress (props m) `union` progress (inh_props m)))
                            , format "the goal is an undefined progress property {0}" goal )
                        ]
                    let prog = progress (props m) `union` progress (inh_props m)
                        saf  = safety (props m) `union` safety (inh_props m)
--                    li@(i,j)      <- lift $ ask
                    r <- parse_rule (map toLower rule) (RuleParserParameter m prog saf goal hyps hint)
                    return m { props = (props m) { derivation = insert goal r $ derivation $ props m } } 
            )
        ,   (   "\\safetyB"
            ,   CmdBlock $ \(lbl, evt, pCt, qCt,()) m -> do
                    toEither $ error_list
                        [ ( not (evt `member` events m)
                            , format "event '{0}' is undeclared" evt )
                        ]
                    let event = events m ! evt
                        prop = safety $ props m
                    (p,q)    <- toEither (do
                        p    <- fromEither ztrue $ get_assert m pCt
                        q    <- fromEither ztrue $ get_assert m qCt
                        error_list 
                            [   ( lbl `member` prop
                                , format "safety property {0} already exists" lbl )
                            ] 
                        return (p,q))
                    let ctx = context m
                    let dum =       free_vars ctx p 
                            `union` free_vars ctx q
                            `union` params event 
                            `union` indices event
                    let new_prop = Unless (M.elems dum) p q (Just evt)
                    return m { props = (props m) 
                        { safety = insert lbl new_prop $ prop 
                        , constraint = insert lbl 
                            (Co (M.elems dum) 
                                (zor 
                                    (zimplies (zand p $ znot q) $ primed (variables m) (zor p q))
                                    (zall $  (elems $ guard event)
                                    	  ++ (elems $ action event))))                                    
                            (constraint $ props m) } } 
            )
        ,   (   "\\replace"
            ,   CmdBlock $ \(evt,n,del,add,keep,prog,saf,()) m -> do
                    toEither $ error_list
                        [ ( not (evt `member` events m)
                            , format "event '{0}' is undeclared" evt )
                        ]
                    let old_event = events m ! evt
                        sc        = sched old_event
                        lbls      = (S.elems $ add `S.union` del `S.union` keep)
                        progs     = progress (props m) `union` progress (inh_props m)
                        safs      = safety (props m) `union` safety (inh_props m)
                    toEither $ do
                        error_list $ flip map lbls $ \lbl ->
                            ( not $ lbl `member` sc
                                , format "'{0}' is not a valid schedule" lbl )
                        error_list
                            [ ( not $ prog `member` progs
                              , format "'{0}' is not a valid progress property" prog )
                            , ( not $ saf `member` safs
                              , format "'{0}' is not a valid safety property" saf )
                            ]
                        error_list 
                            [ ( n `member` sched_ref old_event
                              , format "event '{0}', schedule '{1}' already exists" evt n )
                            ]
                    let rule      = (replace evt (prog,progs!prog) (saf,safs!saf)) 
                                    { remove = del
                                    , add = add
                                    , keep = keep }
                        new_event = old_event { sched_ref = insert n rule 
                                        $ sched_ref old_event }
                        po_lbl    = composite_label [evt,label "SCH",label $ show n]
--                    add_proof_edge po_lbl [prog,saf]
                    return m 
                      { events = insert evt new_event $ events m
                      , props = (props m) { 
                            derivation = 
                                insert po_lbl (Rule (n,rule))
                            $ derivation (props m) } 
                      }
            )
        ,   (   "\\weakento"
            ,   CmdBlock $ \(evt :: Label,n :: Int,del :: S.Set Label,add :: S.Set Label,()) m -> do
                    toEither $ error_list
                        [ ( not (evt `member` events m)
                            , format "event '{0}' is undeclared" evt )
                        ]
                    let old_event = events m ! evt
                        sc        = sched old_event
                        lbls      = (S.elems $ add `S.union` del)
                    toEither $ do
                        error_list $ flip map lbls $ \lbl ->
                            ( not $ lbl `member` sc
                                , format "'{0}' is not a valid schedule" lbl )
                        error_list 
                            [ ( n `member` sched_ref old_event
                              , format "event '{0}', schedule '{1}' already exists" evt n )
                            ]
                    let rule      = (weaken evt)
                                    { remove = del
                                    , add = add }
                        new_event = old_event 
                                    { sched_ref = insert n rule 
                                        $ sched_ref old_event }
                        po_lbl    = composite_label [evt,label "SCH",label $ show n]
                    return m 
                      { events = insert evt new_event $ events m
                      , props = (props m) { 
                            derivation = 
                                insert po_lbl (Rule (n,rule))
                            $ derivation (props m) } 
                      }
            )
        ,   (   "\\replacefine"
            ,   CmdBlock $ \(evt, n, keep, old, new, prog, ()) m -> do
                    toEither $ error_list
                        [ ( not (evt `member` events m)
                            , format "event '{0}' is undeclared" evt )
                        ]
                    let old_event = events m ! evt
                        sc        = sched old_event
                        lbls      = new:(maybeToList old ++ S.elems keep)
                        progs     = progress (props m) `union` progress (inh_props m)
                    toEither $ do
                        error_list $ flip map lbls $ \lbl ->
                            ( not $ lbl `member` sc
                                , format "'{0}' is not a valid schedule" lbl )
                        error_list
                            [ ( not $ prog `member` progs
                              , format "'{0}' is not a valid progress property" prog )
                            ]
                        error_list 
                            [ ( n `member` sched_ref old_event
                              , format "event '{0}', schedule '{1}' already exists" evt n )
                            ]
                    let old_exp   = maybe ztrue (sc !) old
                        rule      = (replace_fine evt old_exp new (sc ! new) (prog,progs!prog))
                                    { keep = keep }
                        new_event = old_event 
                                    { sched_ref = insert n rule 
                                        $ sched_ref old_event }
                        po_lbl    = composite_label [evt,label "SCH",label $ show n]
--                    add_proof_edge po_lbl [prog]
                    return m 
                      { events = insert evt new_event $ events m
                      , props = (props m) { 
                            derivation = 
                                insert po_lbl (Rule (n,rule))
                            $ derivation (props m) } 
                      }
            )
        ]

    -- 
deduct_schedule_ref_struct li m = do
        forM_ (toList $ events m) check_sched
        forM_ (toList $ transient $ props m) check_trans
    where
        check_trans (lbl,Transient _ _ evt n _ lt)  = do
                add_proof_edge lbl [g evt n]
                if n `member` sched_ref (events m ! evt) then do
                    let (_,f_sch) = list_schedules (events m ! evt) ! n
                        progs = progress (props m) `union` progress (inh_props m) 
                    unless (maybe True (flip member progs) lt)
                        $ tell [Error (format "'{0}' is not a progress property" $ M.fromJust lt) li]
                    unless (isJust f_sch == isJust lt)
                        $ if isJust f_sch
                        then tell [Error (format fmt0 lbl evt) li]
                        else tell [Error (format fmt1 lbl evt) li]
                    add_proof_edge lbl $ maybeToList lt
                else tell [Error (format fmt2 evt n lbl) li]
            where
                fmt0 =    "transient predicate {0}: a leads-to property is required for "
                       ++ "transient predicates relying on events "
                       ++ "({1}) with a fine schedule"
                fmt1 =    "transient predicate {0}: a leads-to property is only required "
                       ++ "for events ({1}) with a fine schedule"
                fmt2 =    "transient predicate {2}: event '{0}' "
                       ++ "doesn't have a schedule number {1}"
        check_sched (lbl,evt) = do
                mapM_ f $ zip xs $ drop 1 ys
                mapM_ h $ zip xs $ drop 1 xs
            where
                xs = map (g lbl) $ keys $ sched_ref evt
                ys = elems $ sched_ref evt
        f (lbl,cs) = 
            case rule cs of
                Weaken -> return ()
                Replace (prog,_) (saf,_) -> 
                    add_proof_edge lbl [prog,saf]
                ReplaceFineSch _ _ _ (prog,_) ->
                    add_proof_edge lbl [prog]
        g lbl x = composite_label [lbl, label "SCH", label $ show x]
        h (x,y) = add_proof_edge x [y]

parse_system :: FilePath -> IO (Either [Error] System)
parse_system fn = runEitherT $ do
        xs <- EitherT $ parse_latex_document fn
        hoistEither $ all_machines xs
        
--        ct <- readFile fn
--        return $ do
--                xs <- latex_structure ct
--                all_machines xs

parse_machine :: FilePath -> IO (Either [Error] [Machine])
parse_machine fn = runEitherT $ do
        xs <- EitherT $ parse_latex_document fn
        ms <- hoistEither $ all_machines xs
        return $ map snd $ toList $ machines ms








        