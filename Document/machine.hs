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

import Z3.Z3 

    -- Libraries
import Control.Applicative hiding ( empty )
import Control.Monad hiding ( guard )

import Data.Char
import Data.Map hiding ( map, foldl )
import Data.List as L hiding ( union, insert, inits )
import qualified Data.Set as S

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
                            [   ( label lbl `member` program_prop (props m)
                                , format "{0} is already used for another program property" lbl )
                            ]
                        tr <- get_assert m xs (i,j)
                        let prop = Transient (free_vars (context m) tr) tr $ label ev
                        let old_prog_prop = program_prop $ props m
                        let new_props     = insert (label lbl) prop $ old_prog_prop
                        return m {
                            props = (props m) {
                                program_prop = new_props } } )
            )
        ,   (   "\\constraint"
            ,   Cmd1Args1Blocks (\(lbl,xs) m (i,j) -> do
                        toEither $ error_list (i,j)
                            [ ( label lbl `member` program_prop (props m)
                              , format "{0} is already used for another invariant" lbl )
                            ]
                        pre             <- get_assert m xs (i,j)
                        return m { 
                            props = (props m) { 
                                program_prop = insert (label lbl) (Co (elems $ free_vars (context m) pre) pre) 
                                    $ program_prop $ props m } } )
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
                    let new_prop = Unless [] p q
                    return m { props = (props m) 
                        { safety = insert (label lbl) new_prop $ prop } } )
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

parse_machine :: FilePath -> IO (Either [Error] [Machine])
parse_machine fn = do
        ct <- readFile fn
        return $ list_machines ct
        