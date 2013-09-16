{-# LANGUAGE BangPatterns, FlexibleContexts #-}
module Document.Machine where

    -- Modules
import Document.Expression
import Document.Visitor
import Document.Proof
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
import Control.Applicative hiding ( empty )
import Control.Monad hiding ( guard )
import qualified Control.Monad.Reader.Class as R
import Control.Monad.Trans
import Control.Monad.Trans.RWS as RWS
import Control.Monad.Trans.Either

import Data.Char
import Data.Functor.Identity
import Data.Graph
import Data.Map  as M hiding ( map, foldl, (\\) )
import Data.List as L hiding ( union, insert, inits )
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
        
cycles xs = stronglyConnComp $ map f $ groupBy eq $ sort xs
    where
        eq (x,_) (y,_) = x == y
        f xs = (fst $ head xs, fst $ head xs, map snd xs)

parse_rule :: (Monad m)
           => String
           -> RuleParserParameter
           -> EitherT [Error] (RWST (Int,Int) [Error] [(Label, Label)] m) Rule
parse_rule rule param = do
    (i,j) <- lift $ ask
    case M.lookup rule refinement_parser of
        Just f -> EitherT $ mapRWST (\x -> return (runIdentity x)) $
            runEitherT $ f rule param
        Nothing -> left [(format "invalid refinement rule: {0}" rule,i,j)]

refinement_parser :: Map String (
                  String
               -> RuleParserParameter
               -> EitherT [Error] (RWS (Int, Int) [Error] [(Label, Label)]) Rule)
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

all_machines :: [LatexDoc] -> Either [Error] (Map String Machine)
all_machines xs = let { (x,_,_) = runRWS (runEitherT $ do
            ms <- foldM gather empty xs 
            ms <- toEither $ foldM (f type_decl) ms xs
                -- take actual generic parameter from `type_decl'
            ms <- toEither $ foldM (f imports) ms xs
    
                -- take the types from `imports' and `type_decl`
            ms <- toEither $ foldM (f declarations) ms xs
                
                -- use the `declarations' of variables to check the
                -- type of expressions
            ms <- toEither $ foldM (f collect_expr) ms xs
                
                -- use the label of expressions from `collect_expr' 
                -- in hints.
            ms <- toEither $ inject [] $ do
                    ms <- foldM (f collect_proofs) ms xs
                    s  <- RWS.get
                    let cs = cycles s
                    mapM cycl_err_msg cs
                    return ms
            return ms) () () }
        in x
    where
        cycl_err_msg (AcyclicSCC v) = return ()
        cycl_err_msg (CyclicSCC vs) = tell [("A cycle exists in the proof of liveness: " ++ intercalate "," (map show vs),0,0)]
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

type_decl :: [LatexDoc] -> Machine -> MEither Error Machine
type_decl = visit_doc []
            [  (  "\\newset"
               ,  Cmd2Args $ \(name, tag) m -> do
                    let th = theory m
                    let new_sort = Sort tag name 0
                    let new_type = USER_DEFINED new_sort []
                    toEither $ error_list
                        [ ( tag `member` types th
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
               ,  Cmd1Args $ \(evt,()) m -> do 
                        let lbl = label evt
                        toEither $ error_list
                            [ ( lbl `member` events m
                              , format "event '{0}' is already defined" evt )
                            ]
                        return m { events = insert lbl (empty_event) $ events m } 
               )
            ]

imports :: Monad m 
        => [LatexDoc] 
        -> Machine 
        -> MEitherT Error m Machine 
imports = visit_doc 
            [   ( "use:set"
                , Env1Args $ \(cset,()) _ m -> do
                    let th = theory m
                    toEither $ error_list
                        [ ( not (cset `member` types th)
                          , format "Carrier set {0} undefined" cset )
                        ]
                    return m { theory = th {
                                extends = set_theory (USER_DEFINED (types th ! cset) []) : extends th } } 
                )
            ,   ( "use:fun"
                , Env2Args $ \(dset, rset) _ m -> do
                    let th = theory m
                    toEither $ error_list 
                        [   ( not (dset `member` types th)
                            , format "Carrier set {0} undefined" dset )
                        ,   ( not (rset `member` types th)
                            , format "Carrier set {0} undefined" rset )
                        ]
                    let dtype = USER_DEFINED (types th ! dset) []
                    let rtype = USER_DEFINED (types th ! rset) []
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
             -> MEitherT Error m Machine
declarations = visit_doc 
        [   (   "variable"
            ,   Env0Args $ \() xs m -> do
                        vs <- get_variables (context m) xs
                        let inter = S.fromList (map fst vs) `S.intersection` keysSet (variables m)
                        toEither $ error_list 
                            [ ( not $ S.null inter
                              , format "repeated declaration: {0}" (intercalate ", " $ S.toList inter ))
                            ]
                        return m { variables = fromList vs `union` variables m} 
            )
        ,   (   "indices"
            ,   Env1Args $ \(evt,()) xs m -> do
                        vs <- get_variables (context m) xs
                        toEither $ error_list
                            [ ( not (label evt `member` events m) 
                              , format "event '{0}' is undeclared" evt )
                            ]
                        let old_event = events m ! label evt
                        let var_names = map fst vs
                        let inter = S.fromList var_names `S.intersection` keysSet (indices old_event)
                        toEither $ error_list
                            [ ( not $ S.null inter
                              , format "repeated declaration: {0}" (intercalate ", " $ S.toList inter ) )
                            ]
                        let new_event = old_event { 
                            indices = fromList vs `union` indices old_event }
                        return m { events = insert (label evt) new_event $ events m } 
            )
        ,   (   "constant"
            ,   Env0Args $ \() xs m -> do
                        vs <- get_variables (context m) xs
                        return m { theory = (theory m) { 
                                consts = merge 
                                    (fromListWith (error "repeated definition") vs) 
                                    (consts $ theory m) } } 
            )
        ,   (   "dummy"
            ,   Env0Args $ \() xs m -> do
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
             -> MEitherT Error m Machine
collect_expr = visit_doc 
                --------------
                --  Events  --
                --------------
        [] [(   "\\evassignment"
            ,   Cmd2Args1Blocks $ \(ev, lbl, xs) m -> do
                        toEither $ error_list
                            [ ( not (label ev `member` events m)
                              , format "event '{0}' is undeclared" ev )
                            ]
                        toEither $ error_list
                            [ ( label lbl `member` action (events m ! label ev)
                              , format "{0} is already used for another assignment" lbl )
                            ]
                        let old_event = events m ! label ev
                        act   <- get_evt_part m old_event xs
                        let new_event = old_event { 
                                    action = insertWith 
                                        (error "name clash")  
                                        (label lbl) act
                                        (action old_event) }
                        scope (context m) act (params old_event `merge` indices old_event)
                        return m {          
                                events  = insert (label ev) new_event $ events m } 
            )
        ,   (   "\\evguard"
            ,   Cmd2Args1Blocks $ \(evt, lbl, xs) m -> do
                        toEither $ error_list
                            [   ( not (label evt `member` events m)
                                , format "event '{0}' is undeclared" evt )
                            ]
                        let old_event = events m ! label evt
                        let grds = guard old_event
                        toEither $ error_list
                            [   ( label evt `member` grds
                                , format "{0} is already used for another guard" lbl )
                            ]
                        grd      <- get_evt_part m old_event xs
                        let new_event = old_event { 
                                    guard =  insert (label lbl) grd grds  }
                        scope (context m) grd (indices old_event `merge` params old_event)
                        return m {          
                                events  = insert (label evt) new_event $ events m } 
            )
        ,   (   "\\cschedule"
            ,   Cmd2Args1Blocks $ \(evt, lbl, xs) m -> do
                        toEither $ error_list
                            [ ( not (label evt `member` events m)
                                , format "event '{0}' is undeclared" evt )
                            ]
                        let sc = case c_sched (events m ! label evt) of
                                    Just x  -> x
                                    Nothing -> empty
                        toEither $ error_list
                            [ ( label evt `member` sc
                                , format "{0} is already used for another coarse schedule" lbl )
                            ]
                        let old_event = events m ! label evt
                        sched <- get_evt_part m old_event xs
                        let new_event = old_event { 
                                    c_sched =  
                                        fmap (insert (label lbl) sched) 
                                            ( c_sched old_event <|> Just empty ) }
                        scope (context m) sched (indices old_event) 
                        return m {          
                                events  = insert (label evt) new_event $ events m } 
            )
        ,   (   "\\fschedule"
            ,   Cmd2Args1Blocks $ \(evt, lbl, xs) m -> do
                        toEither $ error_list
                            [ ( not (label evt `member` events m)
                              , format "event '{0}' is undeclared" evt )
                            ]
                        let old_event = events m ! label evt
                        sched <- get_evt_part m old_event xs
                        let event = old_event { 
                                    f_sched = Just sched }
                        scope (context m) sched (indices event) 
                        return m {          
                                events  = insert (label evt) event $ events m } 
            )
                -------------------------
                --  Theory Properties  --
                -------------------------
        ,   (   "\\assumption"
            ,   Cmd1Args1Blocks $ \(lbl,xs) m -> do
                        let th = theory m
                        toEither $ error_list
                            [ ( label lbl `member` fact th
                              , format "{0} is already used for another assertion" lbl )
                            ]
                        axm <- get_assert m xs
                        return m { 
                            theory = th { fact = insert (label lbl) axm $ fact th } } 
            )
                --------------------------
                --  Program properties  --
                --------------------------
        ,   (   "\\initialization"
            ,   Cmd1Args1Blocks $ \(lbl,xs) m -> do
                        initp         <- get_assert m xs
                        toEither $ error_list
                            [ ( label lbl `member` inits m
                              , format "{0} is already used for another invariant" lbl )
                            ]
                        return m {
                                inits = insert (label lbl) initp $ inits m } 
            )
        ,   (   "\\invariant"
            ,   Cmd1Args1Blocks $ \(lbl,xs) m -> do
                        toEither $ error_list
                            [ ( label lbl `member` inv (props m)
                              , format "{0} is already used for another invariant" lbl )
                            ]
                        invar         <- get_assert m xs
                        return m { 
                            props = (props m) { 
                                inv = insert (label lbl) invar $ inv $ props m } } 
            )
        ,   (   "\\transient"      
            ,   Cmd2Args1Blocks $ \(ev, lbl, xs) m -> do
                        toEither $ error_list
                            [ ( not (label ev `member` events m)
                              , format "event '{0}' is undeclared" ev )
                            ]
                        toEither $ error_list
                            [   ( label lbl `member` transient (props m)
                                , format "{0} is already used for another program property" lbl )
                            ]
                        tr            <- get_assert m xs
                        let prop = Transient (free_vars (context m) tr) tr $ label ev
                        let old_prog_prop = transient $ props m
                        let new_props     = insert (label lbl) prop $ old_prog_prop
                        return m {
                            props = (props m) {
                                transient = new_props } } 
            )
        ,   (   "\\constraint"
            ,   Cmd1Args1Blocks $ \(lbl,xs) m -> do
                        toEither $ error_list
                            [ ( label lbl `member` constraint (props m)
                              , format "{0} is already used for another invariant" lbl )
                            ]
                        pre           <- get_assert m xs
                        return m { 
                            props = (props m) { 
                                constraint = insert (label lbl) (Co (elems $ free_vars (context m) pre) pre) 
                                    $ constraint $ props m } } 
            )
        ,   (   "\\safety"
            ,   Cmd1Args2Blocks $ \(lbl, pCt, qCt) m -> do
                    let prop = safety $ props m
                    (p,q)    <- toEither (do
                        p    <- fromEither ztrue $ get_assert m pCt
                        q    <- fromEither ztrue $ get_assert m qCt
                        error_list 
                            [   ( label lbl `member` prop
                                , format "safety property {0} already exists" lbl )
                            ] 
                        return (p,q))
                    let ctx = context m
                    let dum = free_vars ctx p `union` free_vars ctx q
                    let new_prop = Unless (M.elems dum) p q
                    return m { props = (props m) 
                        { safety = insert (label lbl) new_prop $ prop 
                        , constraint = insert (label lbl) 
                            (Co (M.elems dum) (zimplies (zand p $ znot q) $ primed (variables m) (zor p q)))
                            (constraint $ props m) } } 
            )
        ,   (   "\\progress"
            ,   Cmd1Args2Blocks $ \(lbl, pCt, qCt) m -> do
                    let prop = progress $ props m
                    (p,q)    <- toEither (do
                        p    <- fromEither ztrue $ get_assert m pCt
                        q    <- fromEither ztrue $ get_assert m qCt
                        error_list 
                            [   ( label lbl `member` prop
                                , format "progress property {0} already exists" lbl )
                            ] 
                        return (p,q))
                    let ctx = context m
                    let dum = S.fromList (elems $ free_vars ctx p) 
                                `S.union` S.fromList (elems $ free_vars ctx q)
                    let new_prop = LeadsTo (S.elems dum) p q
                    return m { props = (props m) 
                        { progress   = insert (label lbl) new_prop $ prop 
                        , derivation = insert (label lbl) (Rule Add) $ derivation $ props m
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

trim xs = reverse $ f $ reverse $ f xs
    where
        f = dropWhile isSpace

comma_sep :: String -> [String]
comma_sep [] = []
comma_sep xs = trim ys : comma_sep (drop 1 zs)
    where
        (ys,zs) = break (== ',') xs

collect_proofs :: Monad m 
               => [LatexDoc] 
               -> Machine
               -> MSEitherT Error [(Label,Label)] m Machine
collect_proofs = visit_doc
        [   (   "proof"
            ,   Env1Args $ \(po,()) xs m -> do
                    let lbl = composite_label [ _name m, label po ]
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
            ,   Cmd2Args2Blocks $ \(goal,rule,hyps,hint) m -> do
                    let goal_lbl = label goal
                    let hyps_lbls = map label $ comma_sep (concatMap flatten hyps)
                    toEither $ error_list
                        [   ( not (goal_lbl `member` (progress $ props m))
                            , format "the goal is an undefined progress property {0}" goal_lbl )
                        ]
                    let prog = progress $ props m
                    let saf  = safety $ props m
                    li@(i,j)      <- lift $ ask
                    r <- parse_rule (map toLower rule) (RuleParserParameter m prog saf goal_lbl hyps_lbls hint)
                    return m { props = (props m) { derivation = insert goal_lbl r $ derivation $ props m } } 
            )
        ]

parse_machine :: FilePath -> IO (Either [Error] [Machine])
parse_machine fn = do
        ct <- readFile fn
        return $ list_machines ct
        