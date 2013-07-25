module Document.Tests.TrainStation
    ( test_case, test )
where

import Control.Monad

import Data.List ( sort )
import Data.Map hiding ( map )
import qualified Data.Map as M
--import Data.Maybe

import Document.Document as Doc

import Tests.UnitTest

import UnitB.AST
import UnitB.PO
import UnitB.Theory
import UnitB.SetTheory
import UnitB.FunctionTheory
import UnitB.Calculation

import Utilities.Format hiding (test,test_case)

import Z3.Z3

test_case = Case "train station example" test True

test = test_cases [
            (Case "test 0, syntax" case0 $ Right [machine0])
            , (StringCase "test 1, verification" case1 result1)
            , (StringCase "test 2, proof obligation, INIT/fis" case2 result2)
            , (StringCase "test 3, proof obligation, leave/fis" case3 result3)
            , (StringCase "test 4, proof obligation, leave/sch" case4 result4)
            , (StringCase "test 5, proof obligation, leave/en/tr0" case5 result5)
            , (StringCase "test 6, proof obligation, leave/neg/tr0" case6 result6)
            , (Case "test 7, undeclared symbol" case7 result7)
            , (Case "test 8, undeclared event (wrt transient)" case8 result8)
            , (Case "test 9, undeclared event (wrt c sched)" case9 result9)
            , (Case "test 10, undeclared event (wrt indices)" case10 result10)
            , (Case "test 11, undeclared event (wrt assignment)" case11 result11)
            , (StringCase "test 12, proof obligation leave/INV/inv2" case12 result12)
            ]

train_sort :: Sort
train_sort = Sort "\\TRAIN" "TRAIN" 0
train_type :: Type
train_type = USER_DEFINED train_sort []

loc_sort :: Sort
loc_sort = Sort "\\LOC" "LOC" 0
loc_type :: Type
loc_type = USER_DEFINED loc_sort []

blk_sort :: Sort
blk_sort = Sort "\\BLK" "BLK" 0
blk_type :: Type
blk_type = USER_DEFINED blk_sort []

(train,train_var) = (var "TRAIN" $ set_type train_type)
(loc_cons,loc_var)   = (var "LOC" $ set_type loc_type)
(ent,ent_var)   = (var "ent" $ loc_type)
(ext,ext_var)   = (var "ext" $ loc_type)
(plf,plf_var)   = (var "plf" $ loc_type)

(block, block_var) = var "BLK" $ set_type blk_type

machine0 = (empty_machine "m0") 
    {  theory = empty_theory 
            {  extends = 
                    [  function_theory train_type blk_type
                    ,  set_theory blk_type
                    ,  set_theory loc_type
                    ,  set_theory train_type ]
            ,  types   = symbol_table [fun_sort, train_sort, loc_sort, set_sort, blk_sort]
            ,  dummies = singleton "t" $ Var "t" $ train_type 
            ,  fact    = singleton (label "axm0") (fromJust (loc_cons `mzeq` zset_enum [ent,plf,ext]) )
            ,  consts  = fromList
                    [  ("\\TRAIN", train_var)
                    ,  ("\\LOC", loc_var)
                    ,  ("\\BLK", block_var)
                    ,  ("ent", ent_var)
                    ,  ("ext", ext_var)
                    ,  ("plf", plf_var)
                    ]
            }
    ,  inits = map fromJust [loc `mzeq` Right zempty_fun, in_var `mzeq` Right zempty_set]
    ,  variables = symbol_table [in_decl,loc_decl]
    ,  events = fromList [(label "enter", empty_event), (label "leave", leave_evt)]
    ,  props = props0
    }
props0 = empty_property_set
    {  program_prop = singleton (label "tr0") 
            (Transient 
                (singleton "t" $ Var "t" train_type) 
                (fromJust (t `zelem` in_var)) (label "leave") )
    ,  inv = fromList [
--            (label "inv2",fromJust (loc `zelem` (in_var `ztfun` block)))
            (label "inv2",fromJust (zdom loc `mzeq` in_var))
            ]
    }

leave_evt = empty_event {
        indices = symbol_table [t_decl],
        c_sched = Just $ singleton (label "c0") (fromJust (t `zelem` in_var)),
        action = fromList [
            (label "a0", (fromJust (in_var' `mzeq` (in_var `zsetdiff` zmk_set t))))
            ] }

(t, t_decl) = var "t" train_type
(in_var, in_var', in_decl) = prog_var "in" (set_type train_type)
(loc, loc', loc_decl) = prog_var "loc" (fun_type train_type blk_type)
    
train_decl b = 
        [ "(declare-sort BLK 0)"
        , "(declare-sort LOC 0)"
        , "(declare-sort TRAIN 0)"
        , "(define-sort pfun (a b) (Array a b))"
        , "(declare-sort set 1)"
        , "(declare-const BLK (set BLK))"
        , "(declare-const LOC (set LOC))"
        , "(declare-const TRAIN (set TRAIN))"
        , "(declare-const ent LOC)"
        , "(declare-const ext LOC)"
        ] ++ var_decl ++
        [ "(declare-const plf LOC)"
        ] -- ++ set_decl_smt2
    where
        var_decl
            | b     =
                [  "(declare-const in (set TRAIN))"
                ,  "(declare-const in@prime (set TRAIN))"
                ,  "(declare-const loc (pfun TRAIN BLK))"
                ,  "(declare-const loc@prime (pfun TRAIN BLK))"
                ]
            | not b = 
                [  "(declare-const in (set TRAIN))"
                ,  "(declare-const loc (pfun TRAIN BLK))"
                ]

set_decl_smt2 = 
        [  "(declare-fun apply@@TRAIN@@BLK ((pfun TRAIN BLK) TRAIN) BLK)"
        ,  "(declare-fun dom-rest@@TRAIN@@BLK ((set TRAIN) (pfun TRAIN BLK)) (pfun TRAIN BLK))"
        ,  "(declare-fun dom-subst@@TRAIN@@BLK ((set TRAIN) (pfun TRAIN BLK)) (pfun TRAIN BLK))"
        ,  "(declare-fun dom@@TRAIN@@BLK ((pfun TRAIN BLK)) (set TRAIN))"
        ,  "(declare-fun elem@@BLK (BLK (set BLK)) Bool)"
        ,  "(declare-fun elem@@LOC (LOC (set LOC)) Bool)"
        ,  "(declare-fun elem@@TRAIN (TRAIN (set TRAIN)) Bool)"
        ,  "(declare-fun elem@Open@@pfun@@TRAIN@@BLK@Close ((pfun TRAIN BLK) (set (pfun TRAIN BLK))) Bool)"
        ,  "(declare-fun empty-fun@@TRAIN@@BLK () (pfun TRAIN BLK))"
        ,  "(declare-fun empty-set@@BLK () (set BLK))"
        ,  "(declare-fun empty-set@@LOC () (set LOC))"
        ,  "(declare-fun empty-set@@TRAIN () (set TRAIN))"
        ,  "(declare-fun empty-set@Open@@pfun@@TRAIN@@BLK@Close () (set (pfun TRAIN BLK)))"
        ,  "(declare-fun mk-fun@@TRAIN@@BLK (TRAIN BLK) (pfun TRAIN BLK))"
        ,  "(declare-fun mk-set@@BLK (BLK) (set BLK))"
        ,  "(declare-fun mk-set@@LOC (LOC) (set LOC))"
        ,  "(declare-fun mk-set@@TRAIN (TRAIN) (set TRAIN))"
        ,  "(declare-fun mk-set@Open@@pfun@@TRAIN@@BLK@Close ((pfun TRAIN BLK)) (set (pfun TRAIN BLK)))"
        ,  "(declare-fun ovl@@TRAIN@@BLK ((pfun TRAIN BLK) (pfun TRAIN BLK)) (pfun TRAIN BLK))"
        ,  "(declare-fun set-diff@@BLK ((set BLK) (set BLK)) (set BLK))"
        ,  "(declare-fun set-diff@@LOC ((set LOC) (set LOC)) (set LOC))"
        ,  "(declare-fun set-diff@@TRAIN ((set TRAIN) (set TRAIN)) (set TRAIN))"
        ,  "(declare-fun set-diff@Open@@pfun@@TRAIN@@BLK@Close ((set (pfun TRAIN BLK)) (set (pfun TRAIN BLK))) (set (pfun TRAIN BLK)))"
        ,  "(declare-fun tfun@@TRAIN@@BLK ((set TRAIN) (set BLK)) (set (pfun TRAIN BLK)))"
        ,  "(declare-fun bunion@@BLK ((set BLK) (set BLK)) (set BLK))"
        ,  "(declare-fun bunion@@LOC ((set LOC) (set LOC)) (set LOC))"
        ,  "(declare-fun bunion@@TRAIN ((set TRAIN) (set TRAIN)) (set TRAIN))"
        ,  "(declare-fun bunion@Open@@pfun@@TRAIN@@BLK@Close ((set (pfun TRAIN BLK)) (set (pfun TRAIN BLK))) (set (pfun TRAIN BLK)))"
        ]    

set_facts :: (String,String) -> [(String,String)]
set_facts (x0,x1) = map (\(x,y) -> (format x x1, format y x0 x1))
        [   ( "0{0}"
            , "(forall ((x {0}) (y {0}))" ++
                       " (= (elem@{1} x (mk-set@{1} y))" ++
                          " (= x y)))"
            )
        ,   ( "1{0}"
            , "(forall ((x {0}) (s1 (set {0})) (s2 (set {0})))" ++
                        " (= (elem@{1} x (set-diff@{1} s1 s2))" ++
                           " (and (elem@{1} x s1)" ++
                                " (not (elem@{1} x s2)))))"
            )
        ]

fun_facts :: (String,String) -> (String,String) -> [(String,String)]
fun_facts (x0,x1) (y0,y1) = map (\(x,y) -> (format x x1 y1, format y x0 x1 y0 y1)) $
                            zip (map ((++ "{0}{1}") . show) [0..]) 
        [ "(forall ((f1 (pfun {0} {2})) (f2 (pfun {0} {2})))"
                     ++ " (= (bunion@{1} (dom@{1}@{3} f1)"
                        ++                " (dom@{1}@{3} f2))"
                        ++ " (dom@{1}@{3} (ovl@{1}@{3} f1 f2))))"
        , "(= (dom@{1}@{3}" ++
                " empty-fun@{1}@{3})" ++ 
                " empty-set@{1})"
        , "(forall ((s2 (set {2})))" ++
                        " (elem@Open@@pfun@{1}@{3}@Close" ++
                                " empty-fun@{1}@{3}" ++ 
                                " (tfun@{1}@{3} empty-set@{1} s2)))"
        ]

comp_facts = map (\x -> "(assert " ++ x ++ ")") $
            map snd $ sort (   concatMap set_facts 
                                [   ("TRAIN","@TRAIN")
                                ,   ("BLK","@BLK")
                                ,   ("LOC","@LOC")
                                ,   ("(pfun TRAIN BLK)", "Open@@pfun@@TRAIN@@BLK@Close")
                                ]
                            ++ concatMap (uncurry fun_facts) [(("TRAIN","@TRAIN"),("BLK","@BLK"))] )
--        [ "(forall ((x BLK) (y BLK))" ++
--                       " (= (elem@@BLK x (mk-set@@BLK y))" ++
--                          " (= x y)))"
--        , "(forall ((x LOC) (y LOC))" ++
--                       " (= (elem@@LOC x (mk-set@@LOC y))" ++
--                          " (= x y)))"
--        , "(forall ((x TRAIN) (y TRAIN))" ++
--                       " (= (elem@@TRAIN x (mk-set@@TRAIN y))" ++
--                          " (= x y)))"
--        , "(forall ((x (pfun TRAIN BLK)) (y (pfun TRAIN BLK)))" ++
--                       " (= (elem@@TRAIN x (mk-set@@TRAIN y))" ++
--                          " (= x y)))"
--        , "(forall ((f1 (pfun TRAIN BLK)) (f2 (pfun TRAIN BLK)))"
--                     ++ " (= (bunion@@TRAIN (dom@@TRAIN@@BLK f1)"
--                        ++                " (dom@@TRAIN@@BLK f2))"
--                        ++ " (dom@@TRAIN@@BLK (ovl@@TRAIN@@BLK f1 f2))))"
--        , "(forall ((x BLK) (s1 (set BLK)) (s2 (set BLK)))" ++
--                        " (= (elem@@BLK x (set-diff@@BLK s1 s2))" ++
--                           " (and (elem@@BLK x s1)" ++
--                                " (not (elem@@BLK x s2)))))"
--        , "(forall ((x LOC) (s1 (set LOC)) (s2 (set LOC)))" ++
--                        " (= (elem@@LOC x (set-diff@@LOC s1 s2))" ++
--                           " (and (elem@@LOC x s1)" ++
--                                " (not (elem@@LOC x s2)))))"
--        , "(forall ((x TRAIN) (s1 (set TRAIN)) (s2 (set TRAIN)))" ++
--                        " (= (elem@@TRAIN x (set-diff@@TRAIN s1 s2))" ++
--                           " (and (elem@@TRAIN x s1)" ++
--                                " (not (elem@@TRAIN x s2)))))"
--        , "(forall ((x (pfun TRAIN BLK)) (s1 (set (pfun TRAIN BLK))) (s2 (set (pfun TRAIN BLK))))" ++
--                        " (= (elem@@TRAIN x (set-diff@@TRAIN s1 s2))" ++
--                           " (and (elem@@TRAIN x s1)" ++
--                                " (not (elem@@TRAIN x s2)))))"
--        , "(forall ((s2 (set BLK)))" ++
--                        " (elem@Open@@pfun@@TRAIN@@BLK@Close" ++
--                                " empty-fun@@TRAIN@@BLK" ++ 
--                                " (tfun@@TRAIN@@BLK empty-set@@TRAIN s2)))"
--        , "(forall ((s2 (set BLK)))" ++
--                        " (elem@Open@@pfun@@TRAIN@@BLK@Close" ++
--                                " empty-fun@@TRAIN@@BLK" ++ 
--                                " (tfun@@TRAIN@@BLK empty-set@@TRAIN s2)))"
--        ]
        


path0 = "Tests/train-station.tex"
case0 = parse_machine path0

result1 = unlines [
        "  o  m0/INIT/FIS",
        " ooo m0/INIT/INV/inv2",
        " ooo m0/enter/FIS",
        " ooo m0/enter/INV/inv2",
        " ooo m0/enter/SCH",
        " ooo m0/leave/FIS",
        " ooo m0/leave/INV/inv2",
        " ooo m0/leave/SCH",
        " ooo m0/leave/TR/EN/tr0",
        " ooo m0/leave/TR/NEG/tr0",
        "passed 7 / 10"
        ]
case1 = do
    r <- parse_machine path0
    case r of
        Right [m] -> do
            (s,_,_) <- str_verify_machine m
            return s
        x -> return $ show x

result2 = unlines (
        train_decl False 
     ++ set_decl_smt2
     ++ comp_facts ++ -- set_decl_smt2 ++
     [  "(assert (= LOC (bunion@@LOC (bunion@@LOC (mk-set@@LOC ent) (mk-set@@LOC plf)) (mk-set@@LOC ext))))"
     ,  "(assert (not (exists ((in (set TRAIN)) (loc (pfun TRAIN BLK)))" ++ 
            " (and (= loc empty-fun@@TRAIN@@BLK) (= in empty-set@@TRAIN)))))"
     ,  "(check-sat-using (or-else " ++
         "(then qe smt) " ++
         "(then skip smt) " ++
         "(then (using-params simplify :expand-power true) smt)))"
     ] )

case2 = do
        r <- parse_machine path0
        case r of
            Right [m] -> do
                let po = proof_obligation m ! label "m0/INIT/FIS"
                let cmd = unlines $ map (show . as_tree) $ z3_code po
                return cmd
--                return $ show po
            x -> return $ show x

result3 = unlines (
     train_decl False ++ 
     [  "(declare-const t TRAIN)"
     ] ++
     set_decl_smt2 ++ 
     comp_facts ++
     [  "(assert (= LOC (bunion@@LOC (bunion@@LOC (mk-set@@LOC ent) (mk-set@@LOC plf)) (mk-set@@LOC ext))))"
--     ,  "(assert (elem@Open@@pfun@@TRAIN@@BLK@Close loc (tfun@@TRAIN@@BLK in BLK)))"
     ,  "(assert (= (dom@@TRAIN@@BLK loc) in))"
     ,  "(assert (not (exists ((in@prime (set TRAIN)) (loc@prime (pfun TRAIN BLK))) "
            ++ "(= in@prime (set-diff@@TRAIN in (mk-set@@TRAIN t))))))"
     ,  "(check-sat-using (or-else " ++
         "(then qe smt) " ++
         "(then skip smt) " ++
         "(then (using-params simplify :expand-power true) smt)))"
     ] )

case3 = do
        r <- parse_machine path0
        case r of
            Right [m] -> do
                let po = proof_obligation m ! label "m0/leave/FIS"
                let cmd = unlines $ map (show . as_tree) $ z3_code po
--                return $ show po
                return cmd
            x -> return $ show x


result4 = unlines ( 
        train_decl False ++ 
        [  "(declare-const t TRAIN)"
        ] ++
        set_decl_smt2 ++ 
        comp_facts ++
        [ "(assert (= LOC (bunion@@LOC (bunion@@LOC (mk-set@@LOC ent) (mk-set@@LOC plf))"
                                    ++" (mk-set@@LOC ext))))"
--        , "(assert (elem@Open@@pfun@@TRAIN@@BLK@Close loc (tfun@@TRAIN@@BLK in BLK)))"
        , "(assert (= (dom@@TRAIN@@BLK loc) in))"
        , "(assert (elem@@TRAIN t in))"
        , "(assert (not true))"
        , "(check-sat-using (or-else " ++
            "(then qe smt) " ++
            "(then skip smt) " ++
            "(then (using-params simplify :expand-power true) smt)))"
        ] )

case4 = do
        r <- parse_machine path0
        case r of
            Right [m] -> do
                let po = proof_obligation m ! label "m0/leave/SCH"
                let cmd = unlines $ map (show . as_tree) $ z3_code po
--                return $ show po
                return cmd
            x -> return $ show x


result5 = unlines ( 
        train_decl False ++ 
        [  "(declare-const t TRAIN)"
        ] ++
        set_decl_smt2 ++ 
        comp_facts ++
        [ "(assert (= LOC (bunion@@LOC (bunion@@LOC (mk-set@@LOC ent) (mk-set@@LOC plf))"
                                    ++" (mk-set@@LOC ext))))"
--        , "(assert (elem@Open@@pfun@@TRAIN@@BLK@Close loc (tfun@@TRAIN@@BLK in BLK)))"
        , "(assert (= (dom@@TRAIN@@BLK loc) in))"
        , "(assert (not (exists ((t TRAIN)) (=> (elem@@TRAIN t in) (elem@@TRAIN t in)))))"
        , "(check-sat-using (or-else (then qe smt) (then skip smt)"
                        ++ " (then (using-params simplify :expand-power true) smt)))"
        ] )

case5 = do
        r <- parse_machine path0
        case r of
            Right [m] -> do
                let po = proof_obligation m ! label "m0/leave/TR/EN/tr0"
                let cmd = unlines $ map (show . as_tree) $ z3_code po
                return cmd
            x -> return $ show x

result6 = unlines ( 
        train_decl True ++ 
        [  "(declare-const t TRAIN)"
        ] ++
        set_decl_smt2 ++ 
        comp_facts ++
        [  "(assert (= LOC (bunion@@LOC (bunion@@LOC (mk-set@@LOC ent) (mk-set@@LOC plf)) (mk-set@@LOC ext))))"
        ,  "(assert (elem@@TRAIN t in))"
--        ,  "(assert (elem@Open@@pfun@@TRAIN@@BLK@Close loc (tfun@@TRAIN@@BLK in BLK)))"
        ,  "(assert (= (dom@@TRAIN@@BLK loc) in))"
        ,  "(assert (elem@@TRAIN t in))"
        ,  "(assert (= in@prime (set-diff@@TRAIN in (mk-set@@TRAIN t))))"
        ,  "(assert (not (not (elem@@TRAIN t in@prime))))"
        ,  "(check-sat-using (or-else (then qe smt) (then skip smt) (then (using-params simplify :expand-power true) smt)))"
        ] )
    where
        in_prime = ["(declare-const in@prime (set TRAIN))"]
        loc_prime = ["(declare-const loc@prime (pfun TRAIN BLK))"]


case6 = do
        r <- parse_machine path0
        case r of
            Right [m] -> do
                let po = proof_obligation m ! label "m0/leave/TR/NEG/tr0"
                let cmd = unlines $ map (show . as_tree) $ z3_code po
                return cmd
            x -> return $ show x

result12 = unlines ( 
        train_decl True ++ 
        [  "(declare-const t TRAIN)"
        ] ++
        set_decl_smt2 ++ 
        comp_facts ++
        [  "(assert (= LOC (bunion@@LOC (bunion@@LOC (mk-set@@LOC ent) (mk-set@@LOC plf)) (mk-set@@LOC ext))))"
--        ,  "(assert (elem@Open@@pfun@@TRAIN@@BLK@Close loc (tfun@@TRAIN@@BLK in BLK)))"
        ,  "(assert (= (dom@@TRAIN@@BLK loc) in))"
        ,  "(assert (= in@prime (set-diff@@TRAIN in (mk-set@@TRAIN t))))"
--        ,  "(assert (not (elem@Open@@pfun@@TRAIN@@BLK@Close loc@prime (tfun@@TRAIN@@BLK in@prime BLK))))"
        ,  "(assert (not (= (dom@@TRAIN@@BLK loc@prime) in@prime)))"
        ,  "(check-sat-using (or-else (then qe smt) (then skip smt) (then (using-params simplify :expand-power true) smt)))"
        ] )
    where
        in_prime = ["(declare-const in@prime (set TRAIN))"]
        loc_prime = ["(declare-const loc@prime (pfun TRAIN BLK))"]


case12 = do
        r <- parse_machine path0
        case r of
            Right [m] -> do
                let po = proof_obligation m ! label "m0/leave/INV/inv2"
                let cmd = unlines $ map (show . as_tree) $ z3_code po
                return cmd
            x -> return $ show x

    --------------------
    -- Error handling --
    --------------------

result7 = Left [("Undeclared variables: t",52,1)]

path7 = "Tests/train-station-err0.tex"
case7 = parse_machine path7

result8 = Left [("event 'leave' is undeclared",42,1)]

path8 = "Tests/train-station-err1.tex"
case8 = parse_machine path8

result9 = Left [("event 'leave' is undeclared",50,1)]

path9 = "Tests/train-station-err2.tex"
case9 = parse_machine path9

result10 = Left [("event 'leave' is undeclared",54,1)]

path10 = "Tests/train-station-err3.tex"
case10 = parse_machine path10

result11 = Left [("event 'leave' is undeclared",58,1)]

path11 = "Tests/train-station-err4.tex"
case11 = parse_machine path11


get_proof_obl name = do
        r <- parse_machine path0
        case r of
            Right [m] -> do
                let po = proof_obligation m ! label name
                let cmd = unlines $ map (show . as_tree) $ z3_code po
                putStrLn cmd
            x -> putStrLn $ show x

list_proof_obl = do
        r <- parse_machine path0
        case r of
            Right [m] -> do
                forM_ (map show $ keys $ proof_obligation m) putStrLn
            x -> return () -- $ show x
