{-# LANGUAGE Arrows, RecordWildCards #-}
module Document.Context where

    -- Module
import Document.Expression
import Document.Visitor
import Document.Proof
import Document.Pipeline
import Document.Phase
import Document.Scope

import Latex.Parser

import Logic.Expr
import Logic.Operator
import Logic.Proof hiding ( with_line_info )

import UnitB.PO
import UnitB.Syntax as AST

import Logic.Theories.Arithmetic
import Logic.Theories.FunctionTheory
import Logic.Theories.IntervalTheory
import Logic.Theories.PredCalc
import Logic.Theories.SetTheory

    -- Libraries
import Control.Applicative
import Control.Arrow hiding (left)

import Control.Monad.Trans
import Control.Monad.Trans.Reader ( runReaderT )
import Control.Monad.Trans.RWS
import Control.Monad.Trans.Either

import Data.List as L ( map, lookup )
import Data.Map as M
import Data.String.Utils

import Utilities.Error
import Utilities.Syntactic

run_phase1_types :: Pipeline MM 
                        (CMap TheoryP0)
                        (CMap TheoryP1)
run_phase1_types = proc p0 -> do
        ts <- set_decl   -< p0
        it <- imp_theory -< p0
        let t = M.map fst <$> ts
            sets = M.map snd <$> ts
            types  = t  >>= make_all_tables ([printf|Multiple sets with the name %s|])
            imp_th = it >>= make_all_tables ([printf|Theory imported multiple times %s|])
        (types,imp_th,sets) <- triggerP -< (types,imp_th,sets)
        let imp_th' = M.map (M.map fst) imp_th
            f th = M.unions $ L.map AST.types $ M.elems th
            -- basic = fromList [ ("arithmetic",arithmetic)
            --                  , ("basic",basic_theory) ]
            all_types = M.intersectionWith (\ts th -> M.map fst ts `union` f th) types imp_th'
        returnA -< make_phase1 <$> M.map (M.map fst) types 
                               <.> all_types
                               <.> imp_th'
                               <.> sets

type CPipeline ph a = Pipeline MM (CMap ph) (Maybe (CMap a))

make_phase1 :: Map Name Sort
            -> Map Name Sort
            -> Map Name Theory
            -> [(Name,PostponedDef)] 
            -> TheoryP1
make_phase1 _pTypes _pAllTypes _pImports _pSetDecl = TheoryP1 { .. }
    where
        _t0 = TheoryP0 ()

set_decl :: CPipeline TheoryP0 
            ( [(String,Sort,LineInfo)]
            , [(String,PostponedDef)] )
set_decl = contextCmd "\\newset" $ \(String name, String tag) _m _ -> do
            let new_sort = Sort tag name 0
                new_type = Gen $ USER_DEFINED new_sort []
                new_def  = makeDef [] name [] (set_type new_type)
                                    $ zlift (set_type new_type) ztrue
            li <- lift ask
            return ([(tag,new_sort,li)],[(tag,(new_def,Local,li))])

imp_theory :: CPipeline TheoryP0 [(String, Theory, LineInfo)]
imp_theory = contextCmd "\\with" $ \(One (String th_name)) _m _ -> do
        let th = [ ("sets"       , set_theory)
                 , ("functions"  , function_theory)
                 , ("arithmetic" , arithmetic)
                 , ("predcalc"   , pred_calc)
                 , ("intervals"  , interval_theory) ]
            msg = "Undefined theory: {0} "
                -- add suggestions
        li <- lift ask
        case th_name `L.lookup` th of
            Nothing -> raise $ Error (format msg th_name) li
            Just th -> return [(th_name,th,li)]

ctx_type_decl :: String -> [LatexNode] -> Theory -> MSEither Theory
ctx_type_decl _ = visit_doc []
            [  (  "\\newset"
               ,  CmdBlock $ \(String name, String tag) th -> do
                    let new_sort = Sort tag name 0
                        new_type = Gen $ USER_DEFINED new_sort []
                    toEither $ error_list
                        [ ( tag `member` all_types th
                          , format "a sort with name '{0}' is already declared" tag )
                        , ( tag `member` consts th
                          , format "a constant with name '{0}' is already declared" tag )
                        ]
                    let dummy = Var "x@@" new_type
                        new_const = Var name $ set_type new_type
                    return th 
                            {  types = insert 
                                    tag
                                    new_sort
                                    (types th) 
                            ,  consts = insert tag new_const $ consts th
                            ,  fact = insert 
                                    (label (tag ++ "-def"))
                                    (($fromJust) $ mzforall [dummy] mztrue 
                                        (zelem 
                                            (Right $ Word dummy) 
                                            (Right $ Word new_const)))
                                    (fact th)
                            }
               )
            ]

    -- Todo: detect when the same variable is declared twice
    -- in the same declaration block.
ctx_declarations :: String
                 -> [LatexNode] 
                 -> Theory 
                 -> MSEither Theory
ctx_declarations _ = visit_doc []
        [   (   "\\constant"
            ,   CmdBlock $ \(One xs) th -> do
                        vs <- get_variables 
                            (theory_ctx th) 
                            xs
                        return th { 
                                consts = merge 
                                    (fromListWith (error "repeated definition") vs) 
                                    (consts th) } 
            )
        ,   (   "\\dummy"
            ,   CmdBlock $ \(One xs) th -> do
                        vs <- get_variables 
                            (theory_ctx th) 
                            xs
                        return th { 
                                dummies = merge 
                                    (fromListWith (error "repeated definition") vs) 
                                    (dummies th) }
            )
        ,   (   "\\precedence"
            ,   CmdBlock $ \(One ops) th -> do
                    li <- lift ask
                    let msg   = "invalid operator: '{0}'"
                        f x   = (name x, x)
                        notat = notation th
                        xs    = L.map f $ new_ops $ th_notation th
                        g (String x) = maybe (left [Error (format msg x) li])
                                    return $ L.lookup (strip x) xs
                    ops <- toEither $ mapM (mapM $ fromEither ($myError "") . g) ops
--                    traceM $ show ops
--                    traceM $ show $ prec notat
                    return th {
                        notation = notat {
                            prec = ops : prec notat } }
            )
        ]

ctx_operators :: [LatexNode] -> Theory 
              -> MSEither Theory
ctx_operators = visit_doc [] []
--        [   (   "\\operator"
--            ,   CmdBlock $ \(String name,optype,()) th -> do
--                        li <- lift $ ask
--                        [(v,var)] <- get_variables 
--                            (theory_ctx S.empty th) 
--                            (th_notation th) optype
--                        case var of
--                            Var _ (USER_DEFINED s [USER_DEFINED p [t0, t1],t2])
--                                |    s == fun_sort 
--                                  && p == pair_sort -> do    
--                                    let fun           = mk_fun [] v [t0,t1] t2
--                                        mk_expr e0 e1 = typ_fun2 fun e0 e1
--                                        notat         = notation th
--                                        oper          = BinOperator name v mk_expr
--                                    return th { 
--                                            notation = notat { 
--                                                new_ops = Right oper : (new_ops notat)
--                                            } } 
--                            Var _ t -> left [Error (format "Invalid type for binary operator: {0}" t) li]
--            )
--        ]

ctx_imports :: String
        -> [LatexNode] 
        -> Theory 
        -> MSEither Theory
ctx_imports _ = visit_doc []
            [   ( "\\with"
                , CmdBlock $ \(One (String th_name)) th -> do
                    let all_th = [ ("sets"       , set_theory)
                                 , ("functions"  , function_theory)
                                 , ("arithmetic" , arithmetic)
                                 , ("predcalc"   , pred_calc)
                                 , ("intervals"  , interval_theory) ]
                        msg = "Undefined theory: {0} "
                            -- add suggestions
                    li <- lift $ ask
                    case th_name `L.lookup` all_th of
                        Nothing -> left [Error (format msg th_name) li]
                        Just new_th -> 
                            return th {
                                        extends = insert th_name new_th 
                                            $ extends th }
                )
        ,   (   "\\operator"
            ,   CmdBlock $ \(String name,optype) th -> do
                        li <- lift $ ask
                        var <- get_variables 
                            (theory_ctx th) 
                            optype
                        case var of
                            [(v,Var _ (Gen (USER_DEFINED s [Gen (USER_DEFINED p [t0, t1]),t2])))]
                                |    s == fun_sort 
                                  && p == pair_sort -> do    
                                    let fun           = mk_fun [] v [t0,t1] t2
                                        mk_expr e0 e1 = typ_fun2 fun e0 e1
                                        notat         = notation th
                                        oper          = BinOperator v name mk_expr
                                    return th 
                                        { notation = notat
                                            { new_ops = Right oper : (new_ops notat)
                                            , prec = [[Right apply],[Right oper],[Right equal]] : prec notat
                                            }
                                        , funs = insert v fun $ funs th
                                        }
                            [(v,Var _ (Gen (USER_DEFINED s [t0, t1])))]
                                | s == fun_sort -> do
                                    let fun         = mk_fun [] v [t0] t1
                                        mk_expr e0  = typ_fun1 fun e0
                                        notat       = notation th
                                        oper        = UnaryOperator v name mk_expr
                                    return th
                                        { notation = notat
                                            { new_ops = Left oper : (new_ops notat)
                                            , prec = [[Right apply],[Left oper],[Right equal]] : prec notat
                                            }
                                        , funs = insert v fun $ funs th
                                        }
                            [(_,Var _ t)] -> left [Error (format "Invalid type for binary operator: {0}" t) li]
                            vs -> left [Error (format "Invalid binary operator declaration: {0}" $ L.map fst vs) li]
            )
        ]

ctx_collect_expr :: String -> [LatexNode] -> Theory
                 -> MSEither Theory
ctx_collect_expr name = visit_doc 
        [] [(   "\\axiom"
            ,   CmdBlock $ \(lbl, xs) th -> do
                        toEither $ error_list
                            [ ( (lbl `member` fact th)
                              , format "a statement named '{0}' is already declared" lbl )
                            ]
                        thm   <- get_predicate' 
--                            (empty_theory { extends = singleton "" th }) 
                            (empty_theory { extends = insert name th $ extends th }) 
                            (theory_ctx th) xs
                        return th { fact = insert lbl thm $ fact th }
            )
        ,   (   "\\theorem"
            ,   CmdBlock $ \(lbl, xs) th -> do
                        toEither $ error_list
                            [ ( (lbl `member` fact th)
                              , format "a statement named '{0}' is already declared" lbl )
                            ]
--                        traceM $ show $ assoc' $ th_notation th
                        thm   <- get_predicate' 
--                            (empty_theory { extends = singleton "" th }) 
                            (empty_theory { extends = insert name th $ extends th }) 
                            (theory_ctx th) xs
                        return th 
                            { fact = insert lbl thm $ fact th
                            , theorems = insert lbl Nothing $ theorems th }
            )
        ]

ctx_collect_proofs :: String -> [LatexNode] -> Theory
                   -> MSEither Theory
ctx_collect_proofs name = visit_doc
        [   (   "proof"
            ,   EnvBlock $ \(One po) xs th -> do 
                        -- This should be moved to its own phase
                    let po_lbl = label $ remove_ref $ concatMap flatten po
                        lbl = composite_label [ po_lbl ]
                        thm = last $ to_list lbl
                    li <- lift $ ask
                    pos <- hoistEither $ theory_po th
--                            (left [Error (format "proof obligation does not exist: {0}" lbl) li])
--                            return
                    s  <- bind
                        (format "proof obligation does not exist: {0} {1}" lbl 
                                $ M.keys pos)
                        (M.lookup lbl pos)
                    let new_th = (empty_theory { extends = insert name th $ extends th }) 
                        notat = th_notation new_th
                    p <- mapEitherT (\cmd -> runReaderT cmd notat)
                        $ run_visitor li xs collect_proof_step
                    -- p <- runReaderT (
                    --         runEitherT $
                    --         run_visitor li xs 
                    --         collect_proof_step
                    --         ) notat
                    -- p        <- EitherT $ return p
                    (p,lbls) <- EitherT $ return $ runTacticWithTheorems li s 
                            (fact th `intersection` theorems th) p
                    new_thms <- bind
                        (format "a proof for {0} already exists" lbl)
                        $ insert_new lbl (Just p) $ theorems th
                    return th 
                        { theorems   = new_thms
                        , thm_depend = [ (thm,dep) | dep <- lbls ] ++ thm_depend th } 
            )
        ] []
