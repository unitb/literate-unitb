module Document.Tests.TrainStation
    ( test_case, test )
where

import Control.Monad hiding ( guard )

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
            , (Case "test 7, undeclared symbol" case7 result7)
            , (Case "test 8, undeclared event (wrt transient)" case8 result8)
            , (Case "test 9, undeclared event (wrt c sched)" case9 result9)
            , (Case "test 10, undeclared event (wrt indices)" case10 result10)
            , (Case "test 11, undeclared event (wrt assignment)" case11 result11)
            , (StringCase "test 12, proof obligation leave/INV/inv2" case12 result12)
            , (StringCase "test 13, verification, name clash between dummy and index" case13 result13)
            , (StringCase "test 14, verification, non-exhaustive case analysis" case14 result14)
            , (StringCase "test 15, verification, incorrect new assumption" case15 result15)
            , (StringCase "test 16, verification, proof by parts" case16 result16)
            , (StringCase "test 17, ill-defined types" case17 result17)
            , (StringCase "test 18, assertions have type bool" case18 result18)
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
(ent,ent_var)   = (var "ent" $ blk_type)
(ext,ext_var)   = (var "ext" $ blk_type)
(plf,plf_var)   = (var "PLF" $ set_type blk_type)

(block, block_var) = var "BLK" $ set_type blk_type

machine0 = (empty_machine "train0") 
    {  theory = empty_theory 
            {  extends = 
                    [  function_theory train_type blk_type
                    ,  set_theory blk_type
                    ,  set_theory loc_type
                    ,  set_theory train_type 
--                    ,  function_theory train_type loc_type
                    ]
            ,  types   = symbol_table [fun_sort, train_sort, loc_sort, set_sort, blk_sort]
            ,  dummies = symbol_table 
                            $ (map (\t -> Var t $ train_type) 
                                [ "t","t_0","t_1","t_2","t_3" ]
                               ++ map (\t -> Var t $ blk_type) 
                                [ "p","q" ])
            ,  fact    = fromList 
                    [ (label "axm0", axm0)
                    , (label "asm2", axm2)
                    , (label "asm3", axm3) 
                    , (label "asm4", axm4) 
                    , (label "asm5", axm5) ]
            ,  consts  = fromList
                    [  ("\\TRAIN", train_var)
                    ,  ("\\LOC", loc_var)
                    ,  ("\\BLK", block_var)
                    ,  ("ent", ent_var)
                    ,  ("ext", ext_var)
                    ,  ("PLF", plf_var)
                    ]
            }
    ,  inits = fromList $ zip (map (label . ("in" ++) . show . (1 -)) [0..])
            $ map fromJust [loc `mzeq` Right zempty_fun, in_var `mzeq` Right zempty_set]
    ,  variables = symbol_table [in_decl,loc_decl]
    ,  events = fromList [(label "enter", enter_evt), (label "leave", leave_evt)]
    ,  props = props0
    }
    where
        axm0 = fromJust (block `mzeq` (zset_enum [ent,ext] `zunion` plf)) 
        axm2 = fromJust (
                    mznot (ent `mzeq` ext)
            `mzand` mznot (ent `zelem` plf)
            `mzand` mznot (ext `zelem` plf) )
        axm3 = fromJust $
            mzforall [p_decl] $ mzimplies mztrue (
                        mznot (p `mzeq` ext)
                `mzeq`  (p `zelem` (zmk_set ent `zunion` plf)))
        axm4 = fromJust $
            mzforall [p_decl] $ mzimplies mztrue (
                        mznot (p `mzeq` ent)
                `mzeq`  (p `zelem` (zmk_set ext `zunion` plf)))
        axm5 = fromJust $
            mzforall [p_decl] $ mzimplies mztrue (
                        (mzeq p ent `mzor` mzeq p ext)
                `mzeq`  mznot (p `zelem` plf) )
      --    	\qforall{p}{}{ \neg p = ent \equiv p \in \{ext\} \bunion PLF }
props0 = empty_property_set
    {  program_prop = fromList 
            [   ( label "co0"
                , Co [t_decl] 
                    $ fromJust (mzimplies 
                        (mzand (mznot (t `zelem` in_var)) (t `zelem` in_var')) 
                        (mzeq  (zapply loc' t) ent)) )
            ,   ( label "co1"
                , Co [t_decl] 
                    $ fromJust (mzimplies 
                        (mzall [ (t `zelem` in_var), 
                                 (zapply loc t `mzeq` ent), 
                                 mznot (zapply loc t `zelem` plf)])
                        (mzand (t `zelem` in_var')
                               ((zapply loc' t `zelem` plf) `mzor` ((loc' `zapply` t) 
                               `mzeq` ent)))) )
        --    t \in in \land loc.t = ent  \land \neg loc.t \in PLF 
        -- \implies t \in in' \land (loc'.t \in PLF \lor loc'.t = ent)
            ,   ( label "tr0"
                , Transient
                    (symbol_table [t_decl])
                    (fromJust (t `zelem` in_var)) (label "leave") )
            ]
    ,  inv = fromList 
            [   (label "inv2",fromJust (zdom loc `mzeq` in_var))
            ,   (label "inv1",fromJust $ mzforall [t_decl] 
                        (mzimplies (zelem t in_var)
                            (zapply loc t `zelem` block)))
            ]
    ,  proofs = fromList
            [   ( label "train0/enter/INV/inv2"
                , ByCalc $ Calc empty_ctx ztrue ztrue [] (0,0))
            ,   ( label "train0/leave/INV/inv2"
                , ByCalc $ Calc empty_ctx ztrue ztrue [] (0,0))
            ,   ( label "train0/INIT/INV/inv2"
                , ByCalc $ Calc empty_ctx ztrue ztrue [] (0,0))
            ,   ( label "train0/enter/CO/co0"
                , ByCalc $ Calc empty_ctx ztrue ztrue [] (0,0))
            ,   ( label "train0/enter/CO/co1"
                , ByCalc $ Calc empty_ctx ztrue ztrue [] (0,0))
            ,   ( label "train0/leave/CO/co0"
                , ByCalc $ Calc empty_ctx ztrue ztrue [] (0,0))
            ,   ( label "train0/leave/CO/co1"
                , ByCalc $ Calc empty_ctx ztrue ztrue [] (0,0))
            ]
    ,  safety = fromList
            [   ( label "s0"
                , Unless [t_decl] 
                        (fromJust $ mznot (t `zelem` in_var)) 
                        (fromJust ((t `zelem` in_var) `mzand` ( (loc `zapply` t) `mzeq` ent ))) )
            ,   ( label "s1"
                , Unless [t_decl] 
                        (fromJust ((t `zelem` in_var) `mzand` ( (loc `zapply` t) `mzeq` ent )))
                        (fromJust ((t `zelem` in_var) `mzand` ( (loc `zapply` t) `zelem` plf ))) )
            ]
    }

enter_evt = empty_event
    {  indices = symbol_table [t_decl]
    ,  guard = fromList
            [  (label "grd1", fromJust $ mznot (t `zelem` in_var))
            ]
    ,  action = fromList
            [  (label "a1", (fromJust (in_var' `mzeq` (in_var `zunion` zmk_set t))))
            ,  (label "a2", (fromJust (loc' `mzeq` (loc `zovl` zmk_fun t ent))))
            ]
    }
leave_evt = empty_event 
    {  indices = symbol_table [t_decl]
    ,  c_sched = Just $ singleton (label "c0") (fromJust (t `zelem` in_var))
    ,  guard = fromList
            [  (label "grd0", fromJust $ mzand 
                                    (zapply loc t `mzeq` ext) 
                                    (t `zelem` in_var) )
            ]
    ,  action = fromList 
            [  (label "a0", (fromJust (in_var' `mzeq` (in_var `zsetdiff` zmk_set t))))
            ,  (label "a3", (fromJust (loc' `mzeq` (zmk_set t `zdomsubt` loc))))
            ] 
    }

(p, p_decl) = var "p" blk_type
(t, t_decl) = var "t" train_type
(in_var, in_var', in_decl) = prog_var "in" (set_type train_type)
(loc, loc', loc_decl) = prog_var "loc" (fun_type train_type blk_type)
    
train_decl b = 
        [ "(declare-sort BLK 0)"
        , "(declare-sort LOC 0)"
        , "(declare-sort TRAIN 0)"
        , "(define-sort pfun (a b) (Array a b))"
        , "(declare-sort set 1)"
        , "(declare-const PLF (set BLK))"
        , "(declare-const BLK (set BLK))"
        , "(declare-const LOC (set LOC))"
        , "(declare-const TRAIN (set TRAIN))"
        , "(declare-const ent BLK)"
        , "(declare-const ext BLK)"
        ] ++ var_decl ++
        [ "(declare-const p BLK)"
        , "(declare-const q BLK)"
        , "(declare-const t TRAIN)"
        , "(declare-const t_0 TRAIN)"
        , "(declare-const t_1 TRAIN)"
        , "(declare-const t_2 TRAIN)"
        , "(declare-const t_3 TRAIN)"
        ] 
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
        ,  "(declare-fun dom-subt@@TRAIN@@BLK ((set TRAIN) (pfun TRAIN BLK)) (pfun TRAIN BLK))"
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
        ,  "(declare-fun intersect@@BLK ((set BLK) (set BLK)) (set BLK))"
        ,  "(declare-fun intersect@@LOC ((set LOC) (set LOC)) (set LOC))"
        ,  "(declare-fun intersect@@TRAIN ((set TRAIN) (set TRAIN)) (set TRAIN))"
        ,  "(declare-fun intersect@Open@@pfun@@TRAIN@@BLK@Close ((set (pfun TRAIN BLK)) (set (pfun TRAIN BLK))) (set (pfun TRAIN BLK)))"
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
        [   ( "{0}0"
            , "(forall ((x {0}) (y {0}))" ++
                       " (= (elem@{1} x (mk-set@{1} y))" ++
                          " (= x y)))"
            )
        ,   ( "{0}1"
            , "(forall ((x {0}) (s1 (set {0})) (s2 (set {0})))" ++
                        " (= (elem@{1} x (set-diff@{1} s1 s2))" ++
                           " (and (elem@{1} x s1)" ++
                                " (not (elem@{1} x s2)))))"
            )
--            -- elem over intersection
--        Right axm2 = mzforall [x_decl,s1_decl,s2_decl] (
--                          (x `zelem` (s1 `zintersect` s2)) 
--                    `mzeq` ( (x `zelem` s1) `mzand` (x `zelem` s2) ))
        ,   ( "{0}2"
            , "(forall ((x {0}) (s1 (set {0})) (s2 (set {0})))"  ++
                        " (= (elem@{1} x (intersect@{1} s1 s2))" ++
                           " (and (elem@{1} x s1)"               ++
                                " (elem@{1} x s2))))"
            )
--            -- elem over union
--        Right axm3 = mzforall [x_decl,s1_decl,s2_decl] (
--                          (x `zelem` (s1 `zunion` s2)) 
--                    `mzeq` ( (x `zelem` s1) `mzor` (x `zelem` s2) ))
        ,   ( "{0}3"
            , "(forall ((x {0}) (s1 (set {0})) (s2 (set {0})))"  ++
                        " (= (elem@{1} x (bunion@{1} s1 s2))" ++
                           " (or (elem@{1} x s1)"               ++
                               " (elem@{1} x s2))))"
            )
--            -- elem over empty-set
--        Right axm4 = mzforall [x_decl,s1_decl,s2_decl] (
--                          mznot (x `zelem` Right zempty_set)  )
        ,   ( "{0}4"
            , "(forall ((x {0}) (s1 (set {0})) (s2 (set {0})))"  ++
                        " (not (elem@{1} x empty-set@{1})))"
            )
        ]



fun_facts :: (String,String) -> (String,String) -> [(String,String)]
fun_facts (x0,x1) (y0,y1) = map (\(x,y) -> (format x x1 y1, format y x0 x1 y0 y1)) $
                            zip (map (("{0}{1}" ++) . show) [0..]) 
        [ "(forall ((f1 (pfun {0} {2})) (f2 (pfun {0} {2})))"
                     ++ " (= (bunion@{1} (dom@{1}@{3} f1)"
                     ++                " (dom@{1}@{3} f2))"
                     ++    " (dom@{1}@{3} (ovl@{1}@{3} f1 f2))))"
        , "(= (dom@{1}@{3} empty-fun@{1}@{3}) empty-set@{1})"
        , "(forall ((x {0}) (y {2}))"
                     ++ " (= (dom@{1}@{3} (mk-fun@{1}@{3} x y))"
                     ++                 " (mk-set@{1} x)))"
--        , "(forall ((s2 (set {2})))"
--                     ++ " (elem@Open@@pfun@{1}@{3}@Close"
--                     ++                 " empty-fun@{1}@{3}"
--                     ++                 " (tfun@{1}@{3} empty-set@{1} s2)))"
        , "(forall ((f1 (pfun {0} {2})) (f2 (pfun {0} {2})) (x {0}))"
                     ++     " (=> (elem@{1} x (dom@{1}@{3} f2))"
                     ++         " (= (select (ovl@{1}@{3} f1 f2) x)"
                     ++            " (select f2 x))))"
--        axm6 = fromJust $ mzforall [f1_decl,f2_decl,x_decl] ( 
--                            (x `zelem` zdom f2) 
--                `mzimplies` (zapply (f1 `zovl` f2) x `mzeq` zapply f2 x))
        , "(forall ((f1 (pfun {0} {2})) (f2 (pfun {0} {2})) (x {0}))"
                     ++     " (=> (elem@{1} x (set-diff@{1} (dom@{1}@{3} f1)"
                     ++                                   " (dom@{1}@{3} f2)))"
                     ++         " (= (select (ovl@{1}@{3} f1 f2) x)"
                     ++            " (select f1 x))))"
--        axm7 = fromJust $ mzforall [f1_decl,f2_decl,x_decl] ( 
--                        (x `zelem` (zdom f2 `zsetdiff` zdom f1))
--            `mzimplies` (zapply (f1 `zovl` f2) x `mzeq` zapply f1 x))
--            -- apply and mk-fun
        , "(forall ((f1 (pfun TRAIN BLK)) (s1 (set TRAIN)))"
                     ++      " (= (dom@@TRAIN@@BLK (dom-subt@@TRAIN@@BLK s1 f1))"
                     ++         " (set-diff@@TRAIN (dom@@TRAIN@@BLK f1) s1)))"
--        axm12 = fromJust $ mzforall [f1_decl,s1_decl,x_decl] (
--                        (x `zelem` (s1 `zintersect` zdom f1))
--            `mzimplies` (zapply (s1 `zdomrest` f1) x `mzeq` zapply f1 x) )
--            -- dom-subst and apply
        , "(forall ((x {0}) (y {2}))"
                     ++      " (= (select (mk-fun@{1}@{3} x y) x) y))"
--        axm11 = fromJust $ mzforall [x_decl,y_decl] ( 
--                (zmk_fun x y `zapply` x) `mzeq` y )
--            -- dom-rest and apply
        , "(forall ((f1 (pfun {0} {2})) (s1 (set {0})) (x {0}))"
                     ++      " (=> (elem@{1} x (intersect@{1} s1 (dom@{1}@{3} f1)))"
                     ++          " (= (select (dom-rest@{1}@{3} s1 f1) x)"
                     ++             " (select f1 x))))"
--        axm13 = fromJust $ mzforall [f1_decl,s1_decl,x_decl] (
--                        (x `zelem` (zdom f1 `zsetdiff` s1))
--            `mzimplies` (zapply (s1 `zdomsubt` f1
        , "(forall ((f1 (pfun {0} {2})) (s1 (set {0})) (x {0}))"
                     ++      " (=> (elem@{1} x (set-diff@{1} (dom@{1}@{3} f1) s1))"
                     ++          " (= (select (dom-subt@{1}@{3} s1 f1) x)"
                     ++             " (select f1 x))))"
        ]

comp_facts = map (\x -> "(assert " ++ x ++ ")") $
             map snd    (   concatMap set_facts 
                                [   ("BLK","@BLK")
                                ,   ("LOC","@LOC")
                                ,   ("TRAIN","@TRAIN")
                                ]
                            ++ concatMap (uncurry fun_facts) 
                                [  (("TRAIN","@TRAIN"),("BLK","@BLK"))
                                ] 
                            ++ concatMap set_facts 
                                [   ("(pfun TRAIN BLK)", "Open@@pfun@@TRAIN@@BLK@Close")
                                ]
                            )

path0 = "Tests/train-station.tex"
case0 = parse_machine path0

result1 = unlines 
        [  "  o  train0/INIT/FIS"
        ,  "  o  train0/INIT/INV/inv1"
        ,  "  o  train0/INIT/INV/inv2/goal (422,1)"
        ,  "  o  train0/INIT/INV/inv2/hypotheses (422,1)"
        ,  "  o  train0/INIT/INV/inv2/relation (422,1)"
        ,  "  o  train0/INIT/INV/inv2/step (424,1)"
        ,  "  o  train0/INIT/INV/inv2/step (426,1)"
        ,  "  o  train0/INIT/INV/inv2/step (428,1)"
        ,  "  o  train0/SKIP/CO/co0"
        ,  "  o  train0/SKIP/CO/co1"
        ,  "  o  train0/enter/CO/co0/case 1/goal (335,1)"
        ,  "  o  train0/enter/CO/co0/case 1/hypotheses (335,1)"
        ,  "  o  train0/enter/CO/co0/case 1/relation (335,1)"
        ,  "  o  train0/enter/CO/co0/case 1/step (337,1)"
        ,  "  o  train0/enter/CO/co0/case 1/step (339,1)"
        ,  "  o  train0/enter/CO/co0/case 2/goal (347,1)"
        ,  "  o  train0/enter/CO/co0/case 2/hypotheses (347,1)"
        ,  "  o  train0/enter/CO/co0/case 2/relation (347,1)"
        ,  "  o  train0/enter/CO/co0/case 2/step (349,1)"
        ,  "  o  train0/enter/CO/co0/case 2/step (351,1)"
        ,  "  o  train0/enter/CO/co0/case 2/step (353,1)"
        ,  "  o  train0/enter/CO/co0/case 2/step (355,1)"
        ,  "  o  train0/enter/CO/co0/completeness (332,1)"
        ,  "  o  train0/enter/CO/co1/completeness (246,1)"
        ,  "  o  train0/enter/CO/co1/new assumption (223,1)"
        ,  "  o  train0/enter/CO/co1/part 1/goal (250,2)"
        ,  "  o  train0/enter/CO/co1/part 1/hypotheses (250,2)"
        ,  "  o  train0/enter/CO/co1/part 1/relation (250,2)"
        ,  "  o  train0/enter/CO/co1/part 1/step (252,2)"
        ,  "  o  train0/enter/CO/co1/part 1/step (254,2)"
        ,  "  o  train0/enter/CO/co1/part 2/case 1/goal (264,2)"
        ,  "  o  train0/enter/CO/co1/part 2/case 1/hypotheses (264,2)"
        ,  "  o  train0/enter/CO/co1/part 2/case 1/relation (264,2)"
        ,  "  o  train0/enter/CO/co1/part 2/case 1/step (266,2)"
        ,  "  o  train0/enter/CO/co1/part 2/case 1/step (268,2)"
        ,  "  o  train0/enter/CO/co1/part 2/case 2/assertion/hyp6/easy (288,2)"
        ,  "  o  train0/enter/CO/co1/part 2/case 2/main goal/goal (278,2)"
        ,  "  o  train0/enter/CO/co1/part 2/case 2/main goal/hypotheses (278,2)"
        ,  "  o  train0/enter/CO/co1/part 2/case 2/main goal/relation (278,2)"
        ,  "  o  train0/enter/CO/co1/part 2/case 2/main goal/step (280,2)"
        ,  "  o  train0/enter/CO/co1/part 2/case 2/main goal/step (282,2)"
        ,  "  o  train0/enter/CO/co1/part 2/case 2/main goal/step (284,2)"
        ,  "  o  train0/enter/CO/co1/part 2/completeness (261,2)"
        ,  "  o  train0/enter/FIS"
        ,  "  o  train0/enter/INV/inv1"
        ,  "  o  train0/enter/INV/inv2/goal (77,1)"
        ,  "  o  train0/enter/INV/inv2/hypotheses (77,1)"
        ,  "  o  train0/enter/INV/inv2/relation (77,1)"
        ,  "  o  train0/enter/INV/inv2/step (79,1)"
        ,  "  o  train0/enter/INV/inv2/step (81,1)"
        ,  "  o  train0/enter/INV/inv2/step (83,1)"
        ,  "  o  train0/enter/INV/inv2/step (85,1)"
        ,  "  o  train0/enter/INV/inv2/step (87,1)"
        ,  "  o  train0/enter/SCH"
        ,  "  o  train0/leave/CO/co0/assertion/hyp6/goal (202,1)"
        ,  "  o  train0/leave/CO/co0/assertion/hyp6/hypotheses (202,1)"
        ,  "  o  train0/leave/CO/co0/assertion/hyp6/relation (202,1)"
        ,  "  o  train0/leave/CO/co0/assertion/hyp6/step (204,1)"
        ,  "  o  train0/leave/CO/co0/assertion/hyp6/step (206,1)"
        ,  "  o  train0/leave/CO/co0/assertion/hyp6/step (208,1)"
        ,  "  o  train0/leave/CO/co0/main goal/goal (176,1)"
        ,  "  o  train0/leave/CO/co0/main goal/hypotheses (176,1)"
        ,  "  o  train0/leave/CO/co0/main goal/relation (176,1)"
        ,  "  o  train0/leave/CO/co0/main goal/step (178,1)"
        ,  "  o  train0/leave/CO/co0/main goal/step (180,1)"
        ,  "  o  train0/leave/CO/co0/main goal/step (182,1)"
        ,  "  o  train0/leave/CO/co0/main goal/step (184,1)"
        ,  "  o  train0/leave/CO/co0/new assumption (168,1)"
        ,  "  o  train0/leave/CO/co1/goal (367,1)"
        ,  "  o  train0/leave/CO/co1/hypotheses (367,1)"
        ,  "  o  train0/leave/CO/co1/relation (367,1)"
        ,  "  o  train0/leave/CO/co1/step (369,1)"
        ,  "  o  train0/leave/CO/co1/step (372,1)"
        ,  "  o  train0/leave/CO/co1/step (377,1)"
        ,  "  o  train0/leave/CO/co1/step (380,1)"
        ,  "  o  train0/leave/CO/co1/step (383,1)"
        ,  "  o  train0/leave/CO/co1/step (385,1)"
        ,  "  o  train0/leave/CO/co1/step (387,1)"
        ,  "  o  train0/leave/CO/co1/step (390,1)"
        ,  "  o  train0/leave/FIS"
        ,  "  o  train0/leave/INV/inv1"
        ,  "  o  train0/leave/INV/inv2/goal (98,1)"
        ,  "  o  train0/leave/INV/inv2/hypotheses (98,1)"
        ,  "  o  train0/leave/INV/inv2/relation (98,1)"
        ,  "  o  train0/leave/INV/inv2/step (100,1)"
        ,  "  o  train0/leave/INV/inv2/step (102,1)"
        ,  "  o  train0/leave/INV/inv2/step (104,1)"
        ,  "  o  train0/leave/INV/inv2/step (106,1)"
        ,  " xxx train0/leave/SCH"
        ,  "  o  train0/leave/TR/tr0"
        ,  "passed 89 / 90"
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
     [  "(assert (and (not (= ent ext))"
            ++      " (not (elem@@BLK ent PLF))"
            ++      " (not (elem@@BLK ext PLF))))"
     ,  "(assert (forall ((p BLK)) (=> true"
            ++      " (= (not (= p ext))"
            ++         " (elem@@BLK p (bunion@@BLK (mk-set@@BLK ent) PLF))))))"
     ,  "(assert (forall ((p BLK)) (=> true"
            ++      " (= (not (= p ent))"
            ++         " (elem@@BLK p (bunion@@BLK (mk-set@@BLK ext) PLF))))))"
     ,  "(assert (forall ((p BLK)) (=> true"
            ++      " (= (or (= p ent) (= p ext))"
            ++         " (not (elem@@BLK p PLF))))))"
     ,  "(assert (= BLK (bunion@@BLK (bunion@@BLK (mk-set@@BLK ent) (mk-set@@BLK ext)) PLF)))"
     ,  "(assert (not (exists ((in (set TRAIN)) (loc (pfun TRAIN BLK)))" ++ 
            " (and (= in empty-set@@TRAIN) (= loc empty-fun@@TRAIN@@BLK)))))"
     ,  "(check-sat-using (or-else " ++
         "(then qe smt) " ++
         "(then skip smt) " ++
         "(then (using-params simplify :expand-power true) smt)))"
     ] )

case2 = do
        pos <- list_file_obligations path0
        case pos of
            Right [(_,pos)] -> do
                let po = pos ! label "train0/INIT/FIS"
                let cmd = unlines $ map (show . as_tree) $ z3_code po
                return cmd
            x -> return $ show x

result3 = unlines (
     train_decl False ++ 
     set_decl_smt2 ++ 
     comp_facts ++
     [  "(assert (and (not (= ent ext))"
            ++      " (not (elem@@BLK ent PLF))"
            ++      " (not (elem@@BLK ext PLF))))"
     ,  "(assert (forall ((p BLK)) (=> true"
            ++      " (= (not (= p ext))"
            ++         " (elem@@BLK p (bunion@@BLK (mk-set@@BLK ent) PLF))))))"
     ,  "(assert (forall ((p BLK)) (=> true"
            ++      " (= (not (= p ent))"
            ++         " (elem@@BLK p (bunion@@BLK (mk-set@@BLK ext) PLF))))))"
     ,  "(assert (forall ((p BLK)) (=> true"
            ++      " (= (or (= p ent) (= p ext))"
            ++         " (not (elem@@BLK p PLF))))))"
     ,  "(assert (= BLK (bunion@@BLK (bunion@@BLK (mk-set@@BLK ent) (mk-set@@BLK ext)) PLF)))"
     ,  "(assert (forall ((t TRAIN))"
            ++        " (=> (elem@@TRAIN t in)"
            ++            " (elem@@BLK (select loc t) BLK))))"
     ,  "(assert (= (dom@@TRAIN@@BLK loc) in))"
     ,  "(assert (and (= (select loc t) ext) (elem@@TRAIN t in)))"
     ,  "(assert (not (exists ((in@prime (set TRAIN)) (loc@prime (pfun TRAIN BLK)))"
            ++              " (and (= in@prime (set-diff@@TRAIN in (mk-set@@TRAIN t)))"
            ++                   " (= loc@prime (dom-subt@@TRAIN@@BLK (mk-set@@TRAIN t) loc))))))"
     ,  "(check-sat-using (or-else " ++
         "(then qe smt) " ++
         "(then skip smt) " ++
         "(then (using-params simplify :expand-power true) smt)))"
     ] )

case3 = do
        pos <- list_file_obligations path0
        case pos of
            Right [(_,pos)] -> do
                let po = pos ! label "train0/leave/FIS"
                let cmd = unlines $ map (show . as_tree) $ z3_code po
                return cmd
            x -> return $ show x


result4 = unlines ( 
        train_decl False ++ 
        set_decl_smt2 ++ 
        comp_facts ++
        [ "(assert (and (not (= ent ext))"
               ++      " (not (elem@@BLK ent PLF))"
               ++      " (not (elem@@BLK ext PLF))))"
        , "(assert (forall ((p BLK)) (=> true"
               ++      " (= (not (= p ext))"
               ++         " (elem@@BLK p (bunion@@BLK (mk-set@@BLK ent) PLF))))))"
        , "(assert (forall ((p BLK)) (=> true"
               ++      " (= (not (= p ent))"
               ++         " (elem@@BLK p (bunion@@BLK (mk-set@@BLK ext) PLF))))))"
        , "(assert (forall ((p BLK)) (=> true"
               ++      " (= (or (= p ent) (= p ext))"
               ++         " (not (elem@@BLK p PLF))))))"
        , "(assert (= BLK (bunion@@BLK (bunion@@BLK (mk-set@@BLK ent) (mk-set@@BLK ext)) PLF)))"
        , "(assert (forall ((t TRAIN))"
                ++        " (=> (elem@@TRAIN t in)"
                ++            " (elem@@BLK (select loc t) BLK))))"
        , "(assert (= (dom@@TRAIN@@BLK loc) in))"
        , "(assert (elem@@TRAIN t in))"
        , "(assert (not (and (= (select loc t) ext) (elem@@TRAIN t in))))"
        , "(check-sat-using (or-else " ++
            "(then qe smt) " ++
            "(then skip smt) " ++
            "(then (using-params simplify :expand-power true) smt)))"
        ] )

case4 = do
        pos <- list_file_obligations path0
        case pos of
            Right [(_,pos)] -> do
                let po = pos ! label "train0/leave/SCH"
                let cmd = unlines $ map (show . as_tree) $ z3_code po
                return cmd
            x -> return $ show x


result5 = unlines ( 
        train_decl True ++ 
        set_decl_smt2 ++ 
        comp_facts ++
        [  "(assert (and (not (= ent ext))"
               ++      " (not (elem@@BLK ent PLF))"
               ++      " (not (elem@@BLK ext PLF))))"
        ,  "(assert (forall ((p BLK)) (=> true"
               ++      " (= (not (= p ext))"
               ++         " (elem@@BLK p (bunion@@BLK (mk-set@@BLK ent) PLF))))))"
        ,  "(assert (forall ((p BLK)) (=> true"
               ++      " (= (not (= p ent))"
               ++         " (elem@@BLK p (bunion@@BLK (mk-set@@BLK ext) PLF))))))"
        ,  "(assert (forall ((p BLK)) (=> true"
               ++      " (= (or (= p ent) (= p ext))"
               ++         " (not (elem@@BLK p PLF))))))"
        ,  "(assert (= BLK (bunion@@BLK (bunion@@BLK (mk-set@@BLK ent) (mk-set@@BLK ext)) PLF)))"
        ,  "(assert (forall ((t TRAIN))"
                ++        " (=> (elem@@TRAIN t in)"
                ++            " (elem@@BLK (select loc t) BLK))))"
        ,  "(assert (= (dom@@TRAIN@@BLK loc) in))"
        ,  "(assert (not (exists ((t@param TRAIN))"
                ++ " (and (=> (elem@@TRAIN t in) (elem@@TRAIN t@param in))"
                ++      " (=> (and (elem@@TRAIN t in)"
                ++               " (elem@@TRAIN t@param in)"
                ++               " (= (select loc t@param) ext)"
                ++               " (elem@@TRAIN t@param in)"
                ++               " (= in@prime (set-diff@@TRAIN in (mk-set@@TRAIN t@param)))"
                ++               " (= loc@prime (dom-subt@@TRAIN@@BLK (mk-set@@TRAIN t@param) loc)))"
                ++          " (not (elem@@TRAIN t in@prime)))))))"
        ,  "(check-sat-using (or-else (then qe smt) (then skip smt)"
                        ++ " (then (using-params simplify :expand-power true) smt)))"
        ] )

case5 = do
        pos <- list_file_obligations path0
        case pos of
            Right [(_,pos)] -> do
                let po = pos ! label "train0/leave/TR/tr0"
                let cmd = unlines $ map (show . as_tree) $ z3_code po
                return cmd
            x -> return $ show x

--result6 = unlines ( 
--        train_decl True ++ 
--        set_decl_smt2 ++ 
--        comp_facts ++
--        [  "(assert (= BLK (bunion@@BLK (bunion@@BLK (mk-set@@BLK ent) (mk-set@@BLK ext)) PLF)))"
--        ,  "(assert (elem@@TRAIN t in))"
--        ,  "(assert (= (dom@@TRAIN@@BLK loc) in))"
--        ,  "(assert (elem@@TRAIN t in))"
--        ,  "(assert (= in@prime (set-diff@@TRAIN in (mk-set@@TRAIN t))))"
--        ,  "(assert (= loc@prime (dom-subt@@TRAIN@@BLK (mk-set@@TRAIN t) loc)))"
--        ,  "(assert (not (not (elem@@TRAIN t in@prime))))"
--        ,  "(check-sat-using (or-else (then qe smt) (then skip smt) (then (using-params simplify :expand-power true) smt)))"
--        ] )
----    where
----        in_prime = ["(declare-const in@prime (set TRAIN))"]
----        loc_prime = ["(declare-const loc@prime (pfun TRAIN BLK))"]
--
--
--case6 = do
--        pos <- list_file_obligations path0
--        case pos of
--            Right [(_,pos)] -> do
--                let po = pos ! label "m0/leave/TR/NEG/tr0"
--                let cmd = unlines $ map (show . as_tree) $ z3_code po
--                return cmd
--            x -> return $ show x

result12 = unlines ( 
        train_decl True ++ 
        set_decl_smt2 ++ 
        comp_facts ++
        [  "(assert (and (not (= ent ext))"
            ++      " (not (elem@@BLK ent PLF))"
            ++      " (not (elem@@BLK ext PLF))))"
        ,  "(assert (forall ((p BLK)) (=> true"
            ++      " (= (not (= p ext))"
            ++         " (elem@@BLK p (bunion@@BLK (mk-set@@BLK ent) PLF))))))"
        ,  "(assert (forall ((p BLK)) (=> true"
            ++      " (= (not (= p ent))"
            ++         " (elem@@BLK p (bunion@@BLK (mk-set@@BLK ext) PLF))))))"
        ,  "(assert (forall ((p BLK)) (=> true"
            ++      " (= (or (= p ent) (= p ext))"
            ++         " (not (elem@@BLK p PLF))))))"
        ,  "(assert (= BLK (bunion@@BLK (bunion@@BLK (mk-set@@BLK ent) (mk-set@@BLK ext)) PLF)))"
        ,  "(assert (forall ((t TRAIN))"
                ++        " (=> (elem@@TRAIN t in)"
                ++            " (elem@@BLK (select loc t) BLK))))"
        ,  "(assert (= (dom@@TRAIN@@BLK loc) in))"
        ,  "(assert (and (= (select loc t) ext)"
                ++     " (elem@@TRAIN t in)))"
        ,  "(assert (= in@prime (set-diff@@TRAIN in (mk-set@@TRAIN t))))"
        ,  "(assert (= loc@prime (dom-subt@@TRAIN@@BLK (mk-set@@TRAIN t) loc)))"
        ,  "(assert (not (= (dom@@TRAIN@@BLK loc@prime) in@prime)))"
        ,  "(check-sat-using (or-else (then qe smt) (then skip smt) (then (using-params simplify :expand-power true) smt)))"
        ] )

case12 = do
--        pos <- list_file_obligations path0
--        case pos of
--            Right [(_,pos)] -> do
        
        r <- parse_machine path0
        case r of
            Right [m] -> do
                let po = raw_machine_pos m ! label "train0/leave/INV/inv2"
--                putStrLn "anus"
--                print po
--                putStrLn "buttom"
                let cmd = unlines $ map (show . as_tree) $ z3_code po
                return cmd
            x -> return $ show x

    --------------------
    -- Error handling --
    --------------------

result7 = Left [("Undeclared variables: t",52,15)]

path7 = "Tests/train-station-err0.tex"
case7 = parse_machine path7

result8 = Left [("event 'leave' is undeclared",42,15)]

path8 = "Tests/train-station-err1.tex"
case8 = parse_machine path8

result9 = Left [("event 'leave' is undeclared",51,15)]

path9 = "Tests/train-station-err2.tex"
case9 = parse_machine path9

result10 = Left [("event 'leave' is undeclared",54,1)]

path10 = "Tests/train-station-err3.tex"
case10 = parse_machine path10

result11 = Left [("event 'leave' is undeclared",59,15)]

path11 = "Tests/train-station-err4.tex"
case11 = parse_machine path11

path13 = "Tests/train-station-err5.tex"
result13 = unlines
        [  "  o  train0/INIT/FIS"
        ,  "  o  train0/INIT/INV/inv1"
        ,  "  o  train0/INIT/INV/inv2"
        ,  "  o  train0/SKIP/CO/co0"
        ,  "  o  train0/SKIP/CO/co1"
        ,  "  o  train0/enter/CO/co0/goal (220,1)"
        ,  "  o  train0/enter/CO/co0/hypotheses (220,1)"
        ,  "  o  train0/enter/CO/co0/relation (220,1)"
        ,  "  o  train0/enter/CO/co0/step (227,1)"
        ,  "  o  train0/enter/CO/co0/step (229,1)"
        ,  "  o  train0/enter/CO/co0/step (232,1)"
        ,  "  o  train0/enter/CO/co0/step (235,1)"
        ,  "  o  train0/enter/CO/co0/step (238,1)"
        ,  "  o  train0/enter/CO/co0/step (240,1)"
        ,  "  o  train0/enter/CO/co0/step (242,1)"
        ,  "  o  train0/enter/CO/co0/step (244,1)"
        ,  "  o  train0/enter/CO/co1"
        ,  "  o  train0/enter/FIS"
        ,  "  o  train0/enter/INV/inv1"
        ,  "  o  train0/enter/INV/inv2/goal (77,1)"
        ,  "  o  train0/enter/INV/inv2/hypotheses (77,1)"
        ,  "  o  train0/enter/INV/inv2/relation (77,1)"
        ,  "  o  train0/enter/INV/inv2/step (79,1)"
        ,  "  o  train0/enter/INV/inv2/step (81,1)"
        ,  "  o  train0/enter/INV/inv2/step (83,1)"
        ,  "  o  train0/enter/INV/inv2/step (85,1)"
        ,  "  o  train0/enter/INV/inv2/step (87,1)"
        ,  "  o  train0/enter/SCH"
        ,  " xxx train0/leave/CO/co0/goal (173,1)"
        ,  "  o  train0/leave/CO/co0/hypotheses (173,1)"
        ,  "  o  train0/leave/CO/co0/relation (173,1)"
        ,  " xxx train0/leave/CO/co0/step (175,1)"
        ,  "  o  train0/leave/CO/co0/step (177,1)"
        ,  "  o  train0/leave/CO/co0/step (179,1)"
        ,  " xxx train0/leave/CO/co0/step (181,1)"
        ,  "  o  train0/leave/CO/co0/step (183,1)"
        ,  "  o  train0/leave/CO/co0/step (185,1)"
        ,  " xxx train0/leave/CO/co1/goal (250,1)"
        ,  "  o  train0/leave/CO/co1/hypotheses (250,1)"
        ,  "  o  train0/leave/CO/co1/relation (250,1)"
        ,  "  o  train0/leave/CO/co1/step (252,1)"
        ,  "  o  train0/leave/CO/co1/step (255,1)"
        ,  "  o  train0/leave/CO/co1/step (260,1)"
        ,  "  o  train0/leave/CO/co1/step (263,1)"
        ,  "  o  train0/leave/CO/co1/step (266,1)"
        ,  "  o  train0/leave/CO/co1/step (268,1)"
        ,  "  o  train0/leave/CO/co1/step (270,1)"
        ,  "  o  train0/leave/CO/co1/step (273,1)"
        ,  "  o  train0/leave/FIS"
        ,  "  o  train0/leave/INV/inv1"
        ,  "  o  train0/leave/INV/inv2/goal (98,1)"
        ,  "  o  train0/leave/INV/inv2/hypotheses (98,1)"
        ,  "  o  train0/leave/INV/inv2/relation (98,1)"
        ,  "  o  train0/leave/INV/inv2/step (100,1)"
        ,  "  o  train0/leave/INV/inv2/step (102,1)"
        ,  "  o  train0/leave/INV/inv2/step (104,1)"
        ,  "  o  train0/leave/INV/inv2/step (106,1)"
        ,  " xxx train0/leave/SCH"
        ,  "  o  train0/leave/TR/tr0"
        ,  "passed 54 / 59"
        ]
        
case13 = do
    r <- parse_machine path13
    case r of
        Right [m] -> do
            (s,_,_) <- str_verify_machine m
            return s
        x -> return $ show x

path14 = "Tests/train-station-err6.tex"
result14 = unlines
        [  "  o  train0/INIT/FIS"
        ,  "  o  train0/INIT/INV/inv1"
        ,  "  o  train0/INIT/INV/inv2"
        ,  "  o  train0/SKIP/CO/co0"
        ,  "  o  train0/SKIP/CO/co1"
        ,  "  o  train0/enter/CO/co0/case 1/goal (222,1)"
        ,  "  o  train0/enter/CO/co0/case 1/hypotheses (222,1)"
        ,  "  o  train0/enter/CO/co0/case 1/relation (222,1)"
        ,  "  o  train0/enter/CO/co0/case 1/step (224,1)"
        ,  "  o  train0/enter/CO/co0/case 1/step (226,1)"
        ,  " xxx train0/enter/CO/co0/completeness (220,1)"
        ,  "  o  train0/enter/CO/co1"
        ,  "  o  train0/enter/FIS"
        ,  "  o  train0/enter/INV/inv1"
        ,  "  o  train0/enter/INV/inv2/goal (77,1)"
        ,  "  o  train0/enter/INV/inv2/hypotheses (77,1)"
        ,  "  o  train0/enter/INV/inv2/relation (77,1)"
        ,  "  o  train0/enter/INV/inv2/step (79,1)"
        ,  "  o  train0/enter/INV/inv2/step (81,1)"
        ,  "  o  train0/enter/INV/inv2/step (83,1)"
        ,  "  o  train0/enter/INV/inv2/step (85,1)"
        ,  "  o  train0/enter/INV/inv2/step (87,1)"
        ,  "  o  train0/enter/SCH"
        ,  "  o  train0/leave/CO/co0/goal (172,1)"
        ,  "  o  train0/leave/CO/co0/hypotheses (172,1)"
        ,  "  o  train0/leave/CO/co0/relation (172,1)"
        ,  "  o  train0/leave/CO/co0/step (174,1)"
        ,  "  o  train0/leave/CO/co0/step (176,1)"
        ,  "  o  train0/leave/CO/co0/step (180,1)"
        ,  "  o  train0/leave/CO/co0/step (182,1)"
        ,  "  o  train0/leave/CO/co1/goal (255,1)"
        ,  "  o  train0/leave/CO/co1/hypotheses (255,1)"
        ,  "  o  train0/leave/CO/co1/relation (255,1)"
        ,  "  o  train0/leave/CO/co1/step (257,1)"
        ,  "  o  train0/leave/CO/co1/step (260,1)"
        ,  "  o  train0/leave/CO/co1/step (265,1)"
        ,  "  o  train0/leave/CO/co1/step (268,1)"
        ,  "  o  train0/leave/CO/co1/step (271,1)"
        ,  "  o  train0/leave/CO/co1/step (273,1)"
        ,  "  o  train0/leave/CO/co1/step (275,1)"
        ,  "  o  train0/leave/CO/co1/step (278,1)"
        ,  "  o  train0/leave/FIS"
        ,  "  o  train0/leave/INV/inv1"
        ,  "  o  train0/leave/INV/inv2/goal (98,1)"
        ,  "  o  train0/leave/INV/inv2/hypotheses (98,1)"
        ,  "  o  train0/leave/INV/inv2/relation (98,1)"
        ,  "  o  train0/leave/INV/inv2/step (100,1)"
        ,  "  o  train0/leave/INV/inv2/step (102,1)"
        ,  "  o  train0/leave/INV/inv2/step (104,1)"
        ,  "  o  train0/leave/INV/inv2/step (106,1)"
        ,  " xxx train0/leave/SCH"
        ,  "  o  train0/leave/TR/tr0"
        ,  "passed 50 / 52"
        ]
        
case14 = do
    r <- parse_machine path14
    case r of
        Right [m] -> do
            (s,_,_) <- str_verify_machine m
            return s
        x -> return $ show x

path15 = "Tests/train-station-err7.tex"
result15 = unlines
        [  "  o  train0/INIT/FIS"
        ,  "  o  train0/INIT/INV/inv1"
        ,  "  o  train0/INIT/INV/inv2"
        ,  "  o  train0/SKIP/CO/co0"
        ,  "  o  train0/SKIP/CO/co1"
        ,  "  o  train0/enter/CO/co0/case 1/goal (234,1)"
        ,  "  o  train0/enter/CO/co0/case 1/hypotheses (234,1)"
        ,  "  o  train0/enter/CO/co0/case 1/relation (234,1)"
        ,  "  o  train0/enter/CO/co0/case 1/step (236,1)"
        ,  "  o  train0/enter/CO/co0/case 1/step (238,1)"
        ,  "  o  train0/enter/CO/co0/case 2/goal (246,1)"
        ,  "  o  train0/enter/CO/co0/case 2/hypotheses (246,1)"
        ,  "  o  train0/enter/CO/co0/case 2/relation (246,1)"
        ,  "  o  train0/enter/CO/co0/case 2/step (248,1)"
        ,  "  o  train0/enter/CO/co0/case 2/step (250,1)"
        ,  "  o  train0/enter/CO/co0/case 2/step (252,1)"
        ,  "  o  train0/enter/CO/co0/case 2/step (254,1)"
        ,  "  o  train0/enter/CO/co0/completeness (231,1)"
        ,  "  o  train0/enter/CO/co1"
        ,  "  o  train0/enter/FIS"
        ,  "  o  train0/enter/INV/inv1"
        ,  "  o  train0/enter/INV/inv2/goal (77,1)"
        ,  "  o  train0/enter/INV/inv2/hypotheses (77,1)"
        ,  "  o  train0/enter/INV/inv2/relation (77,1)"
        ,  "  o  train0/enter/INV/inv2/step (79,1)"
        ,  "  o  train0/enter/INV/inv2/step (81,1)"
        ,  "  o  train0/enter/INV/inv2/step (83,1)"
        ,  "  o  train0/enter/INV/inv2/step (85,1)"
        ,  "  o  train0/enter/INV/inv2/step (87,1)"
        ,  "  o  train0/enter/SCH"
        ,  "  o  train0/leave/CO/co0/goal (180,1)"
        ,  "  o  train0/leave/CO/co0/hypotheses (180,1)"
        ,  " xxx train0/leave/CO/co0/new assumption (172,1)"
        ,  "  o  train0/leave/CO/co0/relation (180,1)"
        ,  "  o  train0/leave/CO/co0/step (182,1)"
        ,  " xxx train0/leave/CO/co0/step (184,1)"
        ,  "  o  train0/leave/CO/co1/goal (266,1)"
        ,  "  o  train0/leave/CO/co1/hypotheses (266,1)"
        ,  "  o  train0/leave/CO/co1/relation (266,1)"
        ,  "  o  train0/leave/CO/co1/step (268,1)"
        ,  "  o  train0/leave/CO/co1/step (271,1)"
        ,  "  o  train0/leave/CO/co1/step (276,1)"
        ,  "  o  train0/leave/CO/co1/step (279,1)"
        ,  "  o  train0/leave/CO/co1/step (282,1)"
        ,  "  o  train0/leave/CO/co1/step (284,1)"
        ,  "  o  train0/leave/CO/co1/step (286,1)"
        ,  "  o  train0/leave/CO/co1/step (289,1)"
        ,  "  o  train0/leave/FIS"
        ,  "  o  train0/leave/INV/inv1"
        ,  "  o  train0/leave/INV/inv2/goal (98,1)"
        ,  "  o  train0/leave/INV/inv2/hypotheses (98,1)"
        ,  "  o  train0/leave/INV/inv2/relation (98,1)"
        ,  "  o  train0/leave/INV/inv2/step (100,1)"
        ,  "  o  train0/leave/INV/inv2/step (102,1)"
        ,  "  o  train0/leave/INV/inv2/step (104,1)"
        ,  "  o  train0/leave/INV/inv2/step (106,1)"
        ,  " xxx train0/leave/SCH"
        ,  "  o  train0/leave/TR/tr0"
        ,  "passed 55 / 58"
        ]
        
case15 = do
    r <- parse_machine path15
    case r of
        Right [m] -> do
            (s,_,_) <- str_verify_machine m
            return s
        x -> return $ show x

path16 = "Tests/train-station-t2.tex"
result16 = unlines 
        [  "  o  train0/INIT/FIS"
        ,  "  o  train0/INIT/INV/inv1"
        ,  "  o  train0/INIT/INV/inv2"
        ,  "  o  train0/SKIP/CO/co0"
        ,  "  o  train0/SKIP/CO/co1"
        ,  "  o  train0/enter/CO/co0/case 1/goal (292,1)"
        ,  "  o  train0/enter/CO/co0/case 1/hypotheses (292,1)"
        ,  "  o  train0/enter/CO/co0/case 1/relation (292,1)"
        ,  "  o  train0/enter/CO/co0/case 1/step (294,1)"
        ,  "  o  train0/enter/CO/co0/case 1/step (296,1)"
        ,  "  o  train0/enter/CO/co0/case 2/goal (304,1)"
        ,  "  o  train0/enter/CO/co0/case 2/hypotheses (304,1)"
        ,  "  o  train0/enter/CO/co0/case 2/relation (304,1)"
        ,  "  o  train0/enter/CO/co0/case 2/step (306,1)"
        ,  "  o  train0/enter/CO/co0/case 2/step (308,1)"
        ,  "  o  train0/enter/CO/co0/case 2/step (310,1)"
        ,  "  o  train0/enter/CO/co0/case 2/step (312,1)"
        ,  "  o  train0/enter/CO/co0/completeness (289,1)"
        ,  "  o  train0/enter/CO/co1/completeness (215,1)"
        ,  "  o  train0/enter/CO/co1/new assumption (202,1)"
        ,  "  o  train0/enter/CO/co1/part 1/goal (219,2)"
        ,  "  o  train0/enter/CO/co1/part 1/hypotheses (219,2)"
        ,  "  o  train0/enter/CO/co1/part 1/relation (219,2)"
        ,  "  o  train0/enter/CO/co1/part 1/step (221,2)"
        ,  "  o  train0/enter/CO/co1/part 1/step (223,2)"
        ,  "  o  train0/enter/CO/co1/part 2/case 1/goal (233,2)"
        ,  "  o  train0/enter/CO/co1/part 2/case 1/hypotheses (233,2)"
        ,  "  o  train0/enter/CO/co1/part 2/case 1/relation (233,2)"
        ,  "  o  train0/enter/CO/co1/part 2/case 1/step (235,2)"
        ,  "  o  train0/enter/CO/co1/part 2/case 1/step (237,2)"
        ,  "  o  train0/enter/CO/co1/part 2/case 2/goal (244,2)"
        ,  "  o  train0/enter/CO/co1/part 2/case 2/hypotheses (244,2)"
        ,  "  o  train0/enter/CO/co1/part 2/case 2/relation (244,2)"
        ,  "  o  train0/enter/CO/co1/part 2/case 2/step (246,2)"
        ,  " xxx train0/enter/CO/co1/part 2/case 2/step (248,2)"
        ,  "  o  train0/enter/CO/co1/part 2/case 2/step (250,2)"
        ,  "  o  train0/enter/CO/co1/part 2/completeness (230,2)"
        ,  "  o  train0/enter/FIS"
        ,  "  o  train0/enter/INV/inv1"
        ,  "  o  train0/enter/INV/inv2/goal (77,1)"
        ,  "  o  train0/enter/INV/inv2/hypotheses (77,1)"
        ,  "  o  train0/enter/INV/inv2/relation (77,1)"
        ,  "  o  train0/enter/INV/inv2/step (79,1)"
        ,  "  o  train0/enter/INV/inv2/step (81,1)"
        ,  "  o  train0/enter/INV/inv2/step (83,1)"
        ,  "  o  train0/enter/INV/inv2/step (85,1)"
        ,  "  o  train0/enter/INV/inv2/step (87,1)"
        ,  "  o  train0/enter/SCH"
        ,  "  o  train0/leave/CO/co0/goal (175,1)"
        ,  "  o  train0/leave/CO/co0/hypotheses (175,1)"
        ,  "  o  train0/leave/CO/co0/relation (175,1)"
        ,  "  o  train0/leave/CO/co0/step (182,1)"
        ,  "  o  train0/leave/CO/co0/step (184,1)"
        ,  "  o  train0/leave/CO/co0/step (186,1)"
        ,  "  o  train0/leave/CO/co0/step (188,1)"
        ,  "  o  train0/leave/CO/co1/goal (324,1)"
        ,  "  o  train0/leave/CO/co1/hypotheses (324,1)"
        ,  "  o  train0/leave/CO/co1/relation (324,1)"
        ,  "  o  train0/leave/CO/co1/step (326,1)"
        ,  "  o  train0/leave/CO/co1/step (329,1)"
        ,  "  o  train0/leave/CO/co1/step (334,1)"
        ,  "  o  train0/leave/CO/co1/step (337,1)"
        ,  "  o  train0/leave/CO/co1/step (340,1)"
        ,  "  o  train0/leave/CO/co1/step (342,1)"
        ,  "  o  train0/leave/CO/co1/step (344,1)"
        ,  "  o  train0/leave/CO/co1/step (347,1)"
        ,  "  o  train0/leave/FIS"
        ,  "  o  train0/leave/INV/inv1"
        ,  "  o  train0/leave/INV/inv2/goal (98,1)"
        ,  "  o  train0/leave/INV/inv2/hypotheses (98,1)"
        ,  "  o  train0/leave/INV/inv2/relation (98,1)"
        ,  "  o  train0/leave/INV/inv2/step (100,1)"
        ,  "  o  train0/leave/INV/inv2/step (102,1)"
        ,  "  o  train0/leave/INV/inv2/step (104,1)"
        ,  "  o  train0/leave/INV/inv2/step (106,1)"
        ,  " xxx train0/leave/SCH"
        ,  "  o  train0/leave/TR/tr0"
        ,  "passed 75 / 77"
        ]

case16 = do
    r <- parse_machine path16
    case r of
        Right [m] -> do
            (s,_,_) <- str_verify_machine m
            return s
        x -> return $ show x

path17 = "Tests/train-station-err8.tex"
result17 = unlines 
        [  "error (72,1): type of (dom@@a@1@2@@b@1@2 empty-fun@@a@1@2@@b@1@2) is ill-defined: set [_a@1@2]"
        ]

case17 = do
        r <- parse_machine path17
        case r of
            Right _ -> do
                return "successful verification"
            Left xs -> return $ unlines $ map f xs
    where
        f (x,i,j) = format "error {0}: {1}" (i, j) (x :: String) :: String

path18 = "Tests/train-station-err9.tex"
result18 = unlines 
        [  "error (65,15): expression has type incompatible with its type annotation:"
        ,  "  expression: (dom@@TRAIN@@BLK loc)"
        ,  "  type: set [TRAIN]"
        ,  "  type annotation: BOOL "
        ,  ""
        ,  "error (71,15): expression has type incompatible with its type annotation:"
        ,  "  expression: (bunion@@TRAIN in (mk-set@@TRAIN t))"
        ,  "  type: set [TRAIN]"
        ,  "  type annotation: BOOL "
        ,  ""
        ,  "error (116,15): expression has type incompatible with its type annotation:"
        ,  "  expression: t"
        ,  "  type: TRAIN"
        ,  "  type annotation: BOOL "
        ,  ""
        ,  "error (121,15): expression has type incompatible with its type annotation:"
        ,  "  expression: empty-set@@a"
        ,  "  type: set [_a]"
        ,  "  type annotation: BOOL "
        ,  ""
        ]

case18 = do
        r <- parse_machine path18
        case r of
            Right _ -> do
                return "successful verification"
            Left xs -> return $ unlines $ map f xs
    where
        f (x,i,j) = format "error {0}: {1}" (i, j) (x :: String) :: String

get_proof_obl name = do
        pos <- list_file_obligations path0
        case pos of
            Right [(_,pos)] -> do
                let po = pos ! label name
                let cmd = unlines $ map (show . as_tree) $ z3_code po
                putStrLn cmd
            x -> putStrLn $ show x

list_proof_obl = do
        pos <- list_file_obligations path0
        case pos of
            Right [(_,pos)] -> do   
                forM_ (map show $ keys $ pos) putStrLn
            x -> return () -- $ show x
