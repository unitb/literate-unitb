module Document.Context where

    -- Module
import Document.Expression
import Document.Visitor
import Document.Proof

import Latex.Parser

import Logic.Classes
import Logic.Genericity
import Logic.Const
import Logic.Expr
import Logic.Label
import Logic.Operator
import Logic.Tactics hiding ( with_line_info )

import UnitB.AST
import UnitB.PO

import Theories.SetTheory
import Theories.FunctionTheory
import Theories.Arithmetic

    -- Libraries
import Control.Monad.Trans
import Control.Monad.Trans.Reader ( runReaderT )
import Control.Monad.Trans.RWS
import Control.Monad.Trans.Either

import           Data.List as L ( map, lookup )
import           Data.Map as M
import qualified Data.Set as S
import           Data.String.Utils

import Utilities.Format
import Utilities.Syntactic

ctx_type_decl :: String -> [LatexDoc] -> Theory -> MSEither Error System Theory
ctx_type_decl _ = visit_doc []
            [  (  "\\newset"
               ,  CmdBlock $ \(String name, String tag,()) th -> do
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
                    return th 
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
               )
            ]

    -- Todo: detect when the same variable is declared twice
    -- in the same declaration block.
ctx_declarations :: Monad m
                 => String
                 -> [LatexDoc] 
                 -> Theory 
                 -> MSEitherT Error System m Theory
ctx_declarations _ = visit_doc []
        [   (   "\\constant"
            ,   CmdBlock $ \(xs,()) th -> do
                        vs <- get_variables 
                            (theory_ctx S.empty th) 
                            (th_notation th) xs
                        return th { 
                                consts = merge 
                                    (fromListWith (error "repeated definition") vs) 
                                    (consts th) } 
            )
        ,   (   "\\dummy"
            ,   CmdBlock $ \(xs,()) th -> do
                        vs <- get_variables 
                            (theory_ctx S.empty th) 
                            (th_notation th) xs
                        return th { 
                                dummies = merge 
                                    (fromListWith (error "repeated definition") vs) 
                                    (dummies th) }
            )
        ,   (   "\\precedence"
            ,   CmdBlock $ \(ops,()) th -> do  -- with_tracingM $ do
                    li <- lift $ ask
                    let f x   = (name x, x)
                        notat = notation th
                        xs    = L.map f $ new_ops notat
                        g (String x) = maybe (left [Error ("invalid operator: '" ++ x ++ "'") li])
                                    return $ L.lookup (strip x) xs
                    ops <- toEither $ mapM (mapM $ fromEither undefined . g) ops
--                    traceM $ show ops
--                    traceM $ show $ prec notat
                    return th {
                        notation = notat {
                            prec = ops : prec notat } }
            )
        ]

ctx_operators :: Monad m
              => [LatexDoc] 
              -> Theory 
              -> MSEitherT Error System m Theory
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
--                                    let fun           = Fun [] v [t0,t1] t2
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

ctx_imports :: Monad m 
        => String
        -> [LatexDoc] 
        -> Theory 
        -> MSEitherT Error System m Theory
ctx_imports _ = visit_doc []
            [   ( "\\with"
                , CmdBlock $ \(String th_name,()) th -> do
                    toEither $ error_list
                        [ ( not (th_name `elem` ["sets","functions","arithmetic"])
                          , format "Undefined theory {0} " th_name )
                        ]
                    let new_th = case th_name of
                                "sets"       -> set_theory
                                "functions"  -> function_theory
                                "arithmetic" -> arithmetic
                                _ -> error "imports"
                    return th {
                                extends = insert th_name new_th $ extends th }
                )
        ,   (   "\\operator"
            ,   CmdBlock $ \(String name,optype,()) th -> do
                        li <- lift $ ask
                        var <- get_variables 
                            (theory_ctx S.empty th) 
                            (th_notation th) optype
                        case var of
                            [(v,Var _ (USER_DEFINED s [USER_DEFINED p [t0, t1],t2]))]
                                |    s == fun_sort 
                                  && p == pair_sort -> do    
                                    let fun           = Fun [] v [t0,t1] t2
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
                            [(_,Var _ t)] -> left [Error (format "Invalid type for binary operator: {0}" t) li]
                            vs -> left [Error (format "Invalid binary operator declaration: {0}" $ L.map fst vs) li]
            )
        ]

ctx_collect_expr :: Monad m
                 => String
                 -> [LatexDoc] 
                 -> Theory
                 -> MSEitherT Error System m Theory
ctx_collect_expr name = visit_doc 
        [] [(   "\\axiom"
            ,   CmdBlock $ \(lbl, xs,()) th -> do
                        toEither $ error_list
                            [ ( (lbl `member` fact th)
                              , format "a statement named '{0}' is already declared" lbl )
                            ]
                        thm   <- get_predicate' 
--                            (empty_theory { extends = singleton "" th }) 
                            (empty_theory { extends = insert name th $ extends th }) 
                            (theory_ctx S.empty th) xs
                        return th { fact = insert lbl thm $ fact th }
            )
        ,   (   "\\theorem"
            ,   CmdBlock $ \(lbl, xs,()) th -> do
                        toEither $ error_list
                            [ ( (lbl `member` fact th)
                              , format "a statement named '{0}' is already declared" lbl )
                            ]
--                        traceM $ show $ assoc' $ th_notation th
                        thm   <- get_predicate' 
--                            (empty_theory { extends = singleton "" th }) 
                            (empty_theory { extends = insert name th $ extends th }) 
                            (theory_ctx S.empty th) xs
                        return th 
                            { fact = insert lbl thm $ fact th
                            , theorems = insert lbl Nothing $ theorems th }
            )
        ]

ctx_collect_proofs :: Monad m 
                   => String
                   -> [LatexDoc] 
                   -> Theory
                   -> MSEitherT Error System m Theory
ctx_collect_proofs name = visit_doc
        [   (   "proof"
            ,   EnvBlock $ \(po,()) xs th -> do 
                        -- This should be moved to its own phase
                    let po_lbl = label $ remove_ref $ concatMap flatten po
                        lbl = composite_label [ po_lbl ]
                        thm = last $ to_list lbl
                    toEither $ error_list 
                        [   ( lbl `member` theorems th
                            , format "a proof for {0} already exists" lbl )
                        ] 
                    li <- lift $ ask
                    pos <- hoistEither $ theory_po th
--                            (left [Error (format "proof obligation does not exist: {0}" lbl) li])
--                            return
                    s  <- maybe 
                            (left [Error (format "proof obligation does not exist: {0} {1}" lbl 
                                $ M.keys pos) li])
                            return
                            (M.lookup lbl pos)
                    let new_th = (empty_theory { extends = insert name th $ extends th }) 
                    p <- runReaderT (
                            runEitherT $
                            run_visitor li xs $ 
                            collect_proof_step (empty_pr new_th) 
                            ) new_th
                    p        <- EitherT $ return p
                    (p,lbls) <- EitherT $ return $ runTacticWithTheorems li s 
                            (fact th `intersection` theorems th) p
                    return th 
                        { theorems   = insert lbl (Just p) $ theorems th 
                        , thm_depend = [ (thm,dep) | dep <- lbls ] ++ thm_depend th } 
            )
        ] []
