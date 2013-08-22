{-# LANGUAGE BangPatterns #-}
module Document.Machine where

    -- Modules
import Document.Expression
import Document.Visitor
import Document.Proof

import Latex.Parser

import UnitB.AST
import UnitB.PO
import UnitB.SetTheory
import UnitB.FunctionTheory
import UnitB.Genericity

import Z3.Z3 

    -- Libraries
import Control.Applicative hiding ( empty )
import Control.Monad hiding ( guard )

import Data.Char
import Data.Map  as M hiding ( map, foldl, (\\) )
import Data.List as L hiding ( union, insert, inits )
import qualified Data.Set as S

import System.IO
import System.IO.Unsafe

import Utilities.Format
import Utilities.Syntactic

list_file_obligations fn = do
        ct <- readFile fn
        return $ list_proof_obligations ct

list_proof_obligations ct = do
        xs <- list_machines ct
        forM xs (\x -> do
            y <- proof_obligation x
            return (x,y))

list_machines :: String -> Either [Error] [Machine]
list_machines ct = do
        xs <- latex_structure ct
        ms <- all_machines xs
        return $ map snd $ toList $ ms

all_machines :: [LatexDoc] -> Either [Error] (Map String Machine)
all_machines xs = do
        ms <- L.foldl gather (Right empty) xs
        ms <- toEither $ L.foldl (f type_decl) (MRight ms) xs

            -- take actual generic parameter from `type_decl'
        ms <- toEither $ L.foldl (f imports) (MRight ms) xs

            -- take the types from `imports' and `type_decl`
        ms <- toEither $ L.foldl (f declarations) (MRight ms) xs
            
            -- use the `declarations' of variables to check the
            -- type of expressions
        ms <- toEither $ L.foldl (f collect_expr) (MRight ms) xs
            
            -- use the label of expressions from `collect_expr' 
            -- in hints.
        ms <- toEither $ L.foldl (f collect_proofs) (MRight ms) xs
        return ms
    where
        gather em (Env n _ c _)     
                | n == "machine"    = do
                    ms          <- em
                    (name,cont) <- get_1_lbl c
                    let m        = empty_machine name
                    return (insert name m ms)
                | otherwise         = L.foldl gather em c
        gather em x                 = fold_doc gather em x
        f pass em (Env n _ c _)     
                | n == "machine"    = do
                    ms          <- em
                    fromEither ms (do
                        (name,cont) <- get_1_lbl c
                        m           <- toEither $ pass cont (ms ! name)
                        return (insert name m ms))
                | otherwise         = L.foldl (f pass) em c
        f pass em x                 = fold_doc (f pass) em x

type_decl :: [LatexDoc] -> Machine -> MEither Error Machine
type_decl = visit_doc []
            [  (  "\\newset"
               ,  Cmd2Args (\(name, tag) m (i,j) -> do
                    let th = theory m
                    let new_sort = Sort tag name 0
                    let new_type = USER_DEFINED new_sort []
                    toEither $ error_list (i,j)
                        [ ( tag `member` types th
                          , format "a sort with name '{0}' is already declared" tag )
                        , ( tag `member` consts th
                          , format "a constant with name '{0}' is already declared" tag )
                        ]
                    let hd = th 
                            {  types = insert 
                                    tag
                                    new_sort
                                    (types th) 
                            ,  consts = insert tag (Var name $ set_type new_type) $ consts th
                            }
                    return m { theory = hd } )
               )
            ,  (  "\\newevent"
               ,  Cmd1Args (\(evt,()) m (i,j) -> do 
                        let lbl = label evt
                        toEither $ error_list (i,j)
                            [ ( lbl `member` events m
                              , format "event '{0}' is already defined" evt )
                            ]
                        return m { events = insert lbl (empty_event) $ events m } )
               )
            ]

imports :: [LatexDoc] -> Machine -> MEither Error Machine 
imports = visit_doc 
            [   ( "use:set"
                , Env1Args (\(cset,()) _ m (i,j) -> do
                    let th = theory m
                    toEither $ error_list (i,j) 
                        [ ( not (cset `member` types th)
                          , format "Carrier set {0} undefined" cset )
                        ]
                    return m { theory = th {
                                extends = set_theory (USER_DEFINED (types th ! cset) []) : extends th } } )
                )
            ,   ( "use:fun"
                , Env2Args (\(dset, rset) _ m (i,j) -> do
                    let th = theory m
                    toEither $ error_list (i,j) 
                        [   ( not (dset `member` types th)
                            , format "Carrier set {0} undefined" dset )
                        ,   ( not (rset `member` types th)
                            , format "Carrier set {0} undefined" rset )
                        ]
                    let dtype = USER_DEFINED (types th ! dset) []
                    let rtype = USER_DEFINED (types th ! rset) []
                    return m { theory = th {
                                extends = function_theory dtype rtype : extends th } } )
                )
            ]
            []

    -- Todo: detect when the same variable is declared twice
    -- in the same declaration block.
declarations :: [LatexDoc] -> Machine -> MEither Error Machine
declarations = visit_doc 
        [   (   "variable"
            ,   Env0Args (\() xs m (i,j) -> do
                        vs          <- get_variables (context m) xs
                        let inter = S.fromList (map fst vs) `S.intersection` keysSet (variables m)
                        toEither $ error_list (i,j) 
                            [ ( not $ S.null inter
                              , format "repeated declaration: {0}" (intercalate ", " $ S.toList inter ))
                            ]
                        return m { variables = fromList vs `union` variables m} )
            )
        ,   (   "indices"
            ,   Env1Args (\(evt,()) xs m (i,j) -> do
                        vs <- get_variables (context m) xs
                        toEither $ error_list (i,j)
                            [ ( not (label evt `member` events m) 
                              , format "event '{0}' is undeclared" evt )
                            ]
                        let old_event = events m ! label evt
                        let var_names = map fst vs
                        let inter = S.fromList var_names `S.intersection` keysSet (indices old_event)
                        toEither $ error_list (i,j)
                            [ ( not $ S.null inter
                              , format "repeated declaration: {0}" (intercalate ", " $ S.toList inter ) )
                            ]
                        let new_event = old_event { 
                            indices = fromList vs `union` indices old_event }
                        return m { events = insert (label evt) new_event $ events m } )
            )
        ,   (   "constant"
            ,   Env0Args (\() xs m (i,j) -> do
                        vs              <- get_variables (context m) xs
                        return m { theory = (theory m) { 
                                consts = merge 
                                    (fromListWith (error "repeated definition") vs) 
                                    (consts $ theory m) } } )
            )
        ,   (   "dummy"
            ,   Env0Args (\() xs m (i,j) -> do
                        vs              <- get_variables (context m) xs
                        return m { theory = (theory m) { 
                                dummies = merge 
                                    (fromListWith (error "repeated definition") vs) 
                                    (dummies $ theory m) } } )
            )
        ] 
        []

    -- Todo: report an error if we create two assignments (or other events elements)
    -- with the same name
    -- Todo: guard the `insert` statements with checks for name clashes
    -- Todo: check scopes
collect_expr :: [LatexDoc] -> Machine -> MEither Error Machine
collect_expr = visit_doc 
                --------------
                --  Events  --
                --------------
        [] [(   "\\evassignment"
            ,   Cmd2Args1Blocks (\(ev, lbl, xs) m li@(i,j) -> do
                        toEither $ error_list (i,j)
                            [ ( not (label ev `member` events m)
                              , format "event '{0}' is undeclared" ev )
                            ]
                        toEither $ error_list (i,j)
                            [ ( label lbl `member` action (events m ! label ev)
                              , format "{0} is already used for another assignment" lbl )
                            ]
                        let old_event = events m ! label ev
                        act <- get_evt_part m old_event xs (i,j)
                        let new_event = old_event { 
                                    action = insertWith 
                                        (error "name clash")  
                                        (label lbl) act
                                        (action old_event) }
                        scope (context m) act (params old_event `merge` indices old_event) li
                        return m {          
                                events  = insert (label ev) new_event $ events m } ) 
            )
        ,   (   "\\evguard"
            ,   Cmd2Args1Blocks (\(evt, lbl, xs) m li@(i,j) -> do
                        toEither $ error_list (i,j)
                            [   ( not (label evt `member` events m)
                                , format "event '{0}' is undeclared" evt )
                            ]
                        let old_event = events m ! label evt
                        let grds = guard old_event
                        toEither $ error_list (i,j)
                            [   ( label evt `member` grds
                                , format "{0} is already used for another guard" lbl )
                            ]
                        grd <- get_evt_part m old_event xs (i,j)
                        let new_event = old_event { 
                                    guard =  insert (label lbl) grd grds  }
                        scope (context m) grd (indices old_event `merge` params old_event) li
                        return m {          
                                events  = insert (label evt) new_event $ events m } )
            )
        ,   (   "\\cschedule"
            ,   Cmd2Args1Blocks (\(evt, lbl, xs) m li@(i,j) -> do
                        toEither $ error_list (i,j)
                            [ ( not (label evt `member` events m)
                                , format "event '{0}' is undeclared" evt )
                            ]
                        let sc = case c_sched (events m ! label evt) of
                                    Just x  -> x
                                    Nothing -> empty
                        toEither $ error_list (i,j)
                            [ ( label evt `member` sc
                                , format "{0} is already used for another coarse schedule" lbl )
                            ]
                        let old_event = events m ! label evt
                        sched <- get_evt_part m old_event xs li
                        let new_event = old_event { 
                                    c_sched =  
                                        fmap (insert (label lbl) sched) 
                                            ( c_sched old_event <|> Just empty ) }
                        scope (context m) sched (indices old_event) li
                        return m {          
                                events  = insert (label evt) new_event $ events m } )
            )
        ,   (   "\\fschedule"
            ,   Cmd2Args1Blocks (\(evt, lbl, xs) m li@(i,j) -> do
                        toEither $ error_list (i,j)
                            [ ( not (label evt `member` events m)
                              , format "event '{0}' is undeclared" evt )
                            ]
                        let old_event = events m ! label evt
                        sched <- get_evt_part m old_event xs li
                        let event = old_event { 
                                    f_sched = Just sched }
                        scope (context m) sched (indices event) li
                        return m {          
                                events  = insert (label evt) event $ events m } )
            )
                -------------------------
                --  Theory Properties  --
                -------------------------
        ,   (   "\\assumption"
            ,   Cmd1Args1Blocks (\(lbl,xs) m (i,j) -> do
                        let th = theory m
                        toEither $ error_list (i,j)
                            [ ( label lbl `member` fact th
                              , format "{0} is already used for another assertion" lbl )
                            ]
                        axm <- get_assert m xs (i,j)
                        return m { 
                            theory = th { fact = insert (label lbl) axm $ fact th } } ) 
            )
                --------------------------
                --  Program properties  --
                --------------------------
        ,   (   "\\initialization"
            ,   Cmd1Args1Blocks (\(lbl,xs) m (i,j) -> do
                        initp         <- get_assert m xs (i,j)
                        toEither $ error_list (i,j)
                            [ ( label lbl `member` inits m
                              , format "{0} is already used for another invariant" lbl )
                            ]
                        return m {
                                inits = insert (label lbl) initp $ inits m } )
            )
        ,   (   "\\invariant"
            ,   Cmd1Args1Blocks (\(lbl,xs) m (i,j) -> do
                        toEither $ error_list (i,j)
                            [ ( label lbl `member` inv (props m)
                              , format "{0} is already used for another invariant" lbl )
                            ]
                        invar         <- get_assert m xs (i,j)
                        return m { 
                            props = (props m) { 
                                inv = insert (label lbl) invar $ inv $ props m } } )
            )
        ,   (   "\\transient"      
            ,   Cmd2Args1Blocks (\(ev, lbl, xs) m (i,j) -> do
                        toEither $ error_list (i,j)
                            [ ( not (label ev `member` events m)
                              , format "event '{0}' is undeclared" ev )
                            ]
                        toEither $ error_list (i,j)
                            [   ( label lbl `member` transient (props m)
                                , format "{0} is already used for another program property" lbl )
                            ]
                        tr <- get_assert m xs (i,j)
                        let prop = Transient (free_vars (context m) tr) tr $ label ev
                        let old_prog_prop = transient $ props m
                        let new_props     = insert (label lbl) prop $ old_prog_prop
                        return m {
                            props = (props m) {
                                transient = new_props } } )
            )
        ,   (   "\\constraint"
            ,   Cmd1Args1Blocks (\(lbl,xs) m (i,j) -> do
                        toEither $ error_list (i,j)
                            [ ( label lbl `member` constraint (props m)
                              , format "{0} is already used for another invariant" lbl )
                            ]
                        pre             <- get_assert m xs (i,j)
                        return m { 
                            props = (props m) { 
                                constraint = insert (label lbl) (Co (elems $ free_vars (context m) pre) pre) 
                                    $ constraint $ props m } } )
            )
        ,   (   "\\safety"
            ,   Cmd1Args2Blocks (\(lbl, pCt, qCt) m (i,j) -> do
                    let prop = safety $ props m
                    (p,q) <- toEither (do
                        p <- fromEither ztrue $ get_assert m pCt (i,j)
                        q <- fromEither ztrue $ get_assert m qCt (i,j)
                        error_list (i,j) 
                            [   ( label lbl `member` prop
                                , format "safety property {0} already exists" lbl )
                            ] 
                        return (p,q))
                    let dum = free_vars (context m) p `union` free_vars (context m) q
                    let new_prop = Unless (M.elems dum) p q
                    return m { props = (props m) 
                        { safety = insert (label lbl) new_prop $ prop 
                        , constraint = insert (label lbl) 
                            (Co (M.elems dum) (zimplies (zand p $ znot q) $ primed (variables m) (zor p q)))
                            (constraint $ props m) } } )
            )
        ,   (   "\\progress"
            ,   Cmd1Args2Blocks (\(lbl, pCt, qCt) m (i,j) -> do
                    let prop = progress $ props m
                    (p,q) <- toEither (do
                        p <- fromEither ztrue $ get_assert m pCt (i,j)
                        q <- fromEither ztrue $ get_assert m qCt (i,j)
                        error_list (i,j) 
                            [   ( label lbl `member` prop
                                , format "progress property {0} already exists" lbl )
                            ] 
                        return (p,q))
                    let dum = free_vars (context m) p `union` free_vars (context m) q
                    let new_prop = LeadsTo (M.elems dum) p q
                    return m { props = (props m) 
                        { progress   = insert (label lbl) new_prop $ prop 
                        , derivation = insert (label lbl) Add $ derivation $ props m
                        } } )
            )
        ]
    where
        scope :: Context -> Expr -> Map String Var -> (Int,Int) -> Either [Error] ()
        scope ctx xp vs (i,j) = do
            let fv          = keysSet $ free_vars ctx xp
            let decl_v      = keysSet vs
            let undecl_v    = S.toList (fv `S.difference` decl_v)
            if fv `S.isSubsetOf` decl_v
            then return ()
            else Left [(format "Undeclared variables: {0}" (intercalate ", " undecl_v), i,j)]

trim xs = reverse $ f $ reverse $ f xs
    where
        f = dropWhile isSpace

comma_sep :: String -> [String]
comma_sep [] = []
comma_sep xs = trim ys : comma_sep (drop 1 zs)
    where
        (ys,zs) = break (== ',') xs

collect_proofs :: [LatexDoc] -> Machine -> MEither Error Machine
collect_proofs = visit_doc
        [   (   "proof"
            ,   Env1Args (\(po,()) xs m (i,j) -> do
                    let lbl = composite_label [ _name m, label po ]
                    toEither $ error_list (i,j) 
                        [   ( lbl `member` proofs (props m)
                            , format "a proof for {0} already exists" lbl )
                        ] 
                    p <- collect_proof_step empty m xs (i,j)
                    return m { 
                        props = (props m) { 
                            proofs = insert lbl p $ 
                                    proofs $ props m } } )
            )
        ] [ (   "\\refine"
            ,   Cmd2Args2Blocks (\(goal,rule,hyps,hint) m (i,j) -> do
                    let goal_lbl = label goal
                    let hyps_lbls = map label $ comma_sep (concatMap flatten hyps)
                    toEither $ error_list (i,j)
                        [   ( not (goal_lbl `member` (progress $ props m))
                            , format "the goal is an undefined progress property {0}, {1}" goal_lbl $ keys $ progress $ props m )
                        ]
                    let prog = progress $ props m
                    let saf  = safety $ props m
                    r <- case map toLower rule of
                        "discharge" -> do
                            toEither $ error_list (i,j)
                                [   ( 1 > length hyps_lbls || length hyps_lbls > 2
                                    , format "too many hypotheses in the application of the rule: {0}" 
                                        $ intercalate "," $ map show hyps_lbls)
                                ]
                            if length hyps_lbls == 2 then do
                                let [h0,h1] = hyps_lbls
                                toEither $ error_list (i,j)
                                    [   ( not (goal_lbl `member` prog)
                                        , format "refinement ({0}): {1} should be a progress property" rule goal_lbl )
                                    ,   ( not (h0 `member` transient (props m))
                                        , format "refinement ({0}): {1} should be a transient predicate" rule h0 )
                                    ,   ( not (h1 `member` safety (props m))
                                        , format "refinement ({0}): {1} should be a safety property" rule h0 )
                                    ]
                                let p0 = prog ! goal_lbl
                                let p1 = transient (props m) ! h0
                                let p2 = safety (props m) ! h1
                                return (Discharge p0 p1 $ Just p2)
                            else do -- length hyps_lbls == 1
                                let [h0] = hyps_lbls
                                toEither $ error_list (i,j)
                                    [   ( not (goal_lbl `member` prog)
                                        , format "refinement ({0}): {1} should be a progress property" rule goal_lbl )
                                    ,   ( not (h0 `member` transient (props m))
                                        , format "refinement ({0}): {1} should be a transient predicate" rule h0 )
                                    ]
                                let p0 = prog ! goal_lbl
                                let p1 = transient (props m) ! h0
                                return (Discharge p0 p1 Nothing)
                        "monotonicity" -> do
                            toEither $ error_list (i,j)
                                [   ( length hyps_lbls /= 1
                                    , format "too many hypotheses in the application of the rule: {0}" 
                                        $ intercalate "," $ map show hyps_lbls)
                                ]
                            let [h0] = hyps_lbls
                            toEither $ error_list (i,j)
                                [   ( not (goal_lbl `member` prog)
                                    , format "refinement ({0}): {1} should be a progress property" rule goal_lbl )
                                ,   ( not (h0 `member` prog)
                                    , format "refinement ({0}): {1} should be a progress property" rule h0 )
                                ]
                            let p0 = prog ! goal_lbl
                            let p1 = prog ! h0
                            return (Monotonicity p0 p1)
                        "disjunction" -> do
                            toEither $ error_list (i,j)
                                [   ( length hyps_lbls /= 1
                                    , format "too many hypotheses in the application of the rule: {0}" 
                                        $ intercalate "," $ map show hyps_lbls)
                                ]
                            let [h0] = hyps_lbls
                            toEither $ error_list (i,j)
                                [   ( not (h0 `member` progress (props m))
                                    , format "refinement ({0}): {1} should be a progress property" rule h0 )
                                ]
                            return (Disjunction h0)
                        "trading" -> do
                            toEither $ error_list (i,j)
                                [   ( length hyps_lbls /= 1
                                    , format "too many hypotheses in the application of the rule: {0}" 
                                        $ intercalate "," $ map show hyps_lbls)
                                ]
                            let [h0] = hyps_lbls
                            toEither $ error_list (i,j)
                                [   ( not (goal_lbl `member` prog)
                                    , format "refinement ({0}): {1} should be a progress property" rule goal_lbl )
                                ,   ( not (h0 `member` prog)
                                    , format "refinement ({0}): {1} should be a progress property" rule h0 )
                                ]
                            let p0 = prog ! goal_lbl
                            let p1 = prog ! h0
                            return (NegateDisjunct p0 p1)
                        "transitivity" -> do
                            toEither $ error_list (i,j)
                                [   ( length hyps_lbls /= 2
                                    , format "too many hypotheses in the application of the rule: {0}" 
                                        $ intercalate "," $ map show hyps_lbls)
                                ]
                            let [h0,h1] = hyps_lbls
                            toEither $ error_list (i,j)
                                [   ( not (goal_lbl `member` progress (props m))
                                    , format "refinement ({0}): {1} should be a progress property" rule goal_lbl )
                                ,   ( not (h0 `member` progress (props m))
                                    , format "refinement ({0}): {1} should be a progress property" rule h0 )
                                ,   ( not (h1 `member` progress (props m))
                                    , format "refinement ({0}): {1} should be a progress property" rule h1 )
                                ]
                            let p0 = prog ! goal_lbl
                            let p1 = prog ! h0
                            let p2 = prog ! h1
                            return (Transitivity p0 p1 p2)
                        "psp" -> do
                            toEither $ error_list (i,j)
                                [   ( length hyps_lbls /= 2
                                    , format "too many hypotheses in the application of the rule: {0}" 
                                        $ intercalate "," $ map show hyps_lbls)
                                ]
                            let [h0,h1] = hyps_lbls
                            toEither $ error_list (i,j)
                                [   ( not (goal_lbl `member` prog)
                                    , format "refinement ({0}): {1} should be a progress property" rule goal_lbl )
                                ,   ( not (h0 `member` prog)
                                    , format "refinement ({0}): {1} should be a progress property" rule h0 )
                                ,   ( not (h1 `member` saf)
                                    , format "refinement ({0}): {1} should be a safety property" rule h1 )
                                ]
                            let p0 = prog ! goal_lbl
                            let p1 = prog ! h0
                            let p2 = saf ! h1
                            return (PSP p0 p1 p2)
                        "induction" -> do
                            toEither $ error_list (i,j)
                                [   ( length hyps_lbls /= 1
                                    , format "too many hypotheses in the application of the rule: {0}" 
                                        $ intercalate "," $ map show hyps_lbls)
                                ]
                            let [h0] = hyps_lbls
                            toEither $ error_list (i,j)
                                [   ( not (goal_lbl `member` prog)
                                    , format "refinement ({0}): {1} should be a progress property" rule goal_lbl )
                                ,   ( not (h0 `member` prog)
                                    , format "refinement ({0}): {1} should be a progress property" rule h0 )
                                ]
                            (dir,var,bound) <- case find_cmd_arg 3 ["\\var"] hint of
                                Just (_,_,[var,dir,bound],_) -> do
                                        var   <- get_expr m var   (i,j)
                                        bound <- get_expr m bound (i,j)
                                        dir  <- case map toLower $ concatMap flatten dir of
                                            "up"   -> return Up
                                            "down" -> return Down
                                            _      -> Left [("expecting a direction for the variant",i,j)]
                                        var <- either 
                                            (\x -> Left [(x,i,j)]) 
                                            Right
                                            $ zcast int 
                                            $ Right var
                                        bound <- either
                                            (\x -> Left [(x,i,j)])
                                            Right
                                            $ zcast int
                                            $ Right bound
                                        return (dir,var,bound)
                                Nothing -> Left [("expecting a variant", i,j)]
                            let pr0@(LeadsTo fv0 p0 q0) = prog ! goal_lbl
                            let pr1@(LeadsTo fv1 p1 q1) = prog ! h0
                            dum <- case fv1 \\ fv0 of
                                [v] -> return v
                                _   -> Left [(   "inductive formula should have one free "
                                              ++ "variable to record the variant",i,j)]                    
                            return (Induction pr0 pr1 (IntegerVariant dum var bound dir))
                        _ -> Left [(format "invalid refinement rule: {0}" $ map toLower rule,i,j)]
                    return m { props = (props m) { derivation = insert goal_lbl r $ derivation $ props m } } ))
        ]

parse_machine :: FilePath -> IO (Either [Error] [Machine])
parse_machine fn = do
        ct <- readFile fn
        return $ list_machines ct
        