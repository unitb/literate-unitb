module Document.Tests.TrainStation
    ( test_case, test )
where

import Control.Monad

import Data.Map hiding ( map )
import qualified Data.Map as M
import Data.Maybe

import Document.Document as Doc

import Tests.UnitTest

import UnitB.AST
import UnitB.PO
import UnitB.Theory
import UnitB.SetTheory
import UnitB.Calculation

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
            ]

train_sort :: Sort
train_sort = Sort "\\TRAIN" "TRAIN" 0
train_type :: Type
train_type = USER_DEFINED train_sort []

loc_sort :: Sort
loc_sort = Sort "\\LOC" "LOC" 0
loc_type :: Type
loc_type = USER_DEFINED loc_sort []

train_var = (Var "TRAIN" $ set_type train_type)
loc_var   = (Var "LOC" $ set_type loc_type)
ent_var   = (Var "ent" $ loc_type)
ext_var   = (Var "ext" $ loc_type)
plf_var   = (Var "plf" $ loc_type)

train = Word train_var
loc   = Word loc_var
ent   = Word ent_var
ext   = Word ext_var
plf   = Word plf_var

--set_sort :: Sort
--set_sort = Sort "\\set" "set" 1
--set_type t = USER_DEFINED set_sort [t]

machine0 = (empty_machine "m0") 
    {   theory = empty_theory 
            {   extends = [ set_theory loc_type, set_theory train_type ]
            ,   types   = symbol_table [train_sort, loc_sort, set_sort]
            ,   dummies = singleton "t" $ Var "t" $ train_type 
            ,   fact    = singleton (label "axm0") ( (loc `zeq` fromJust (zset_enum $ map Just [ent,plf,ext])) )
            ,   consts  = fromList
                    [ ("\\TRAIN", train_var)
                    , ("\\LOC", loc_var)
                    , ("ent", ent_var)
                    , ("ext", ext_var)
                    , ("plf", plf_var)
                    ]
            }
    ,   variables = singleton "in" (Var "in" $ set_type train_type)
    ,   events = fromList [(label "enter", empty_event), (label "leave", leave_evt)]
    ,   props = props0
    }
props0 = empty_property_set {
        program_prop = singleton (label "tr0") 
            (Transient 
                (singleton "t" $ Var "t" train_type) 
                (fromJust (t `zelem` in_var)) (label "leave") )
        }

leave_evt = empty_event {
        indices = symbol_table [t_decl],
        c_sched = Just $ singleton (label "c0") (fromJust (t `zelem` in_var)),
        action = fromList [
            (label "a0", (fromJust (in_var' `mzeq` (in_var `zsetdiff` zmk_set t))))
--            (label "a0", (in_var' `zapply` t) `zeq` zfalse)
            ] }

(t, t_decl) = var "t" train_type
(in_var, in_var', in_decl) = prog_var "in" (set_type train_type)

--parse_machine path = do
--        mch <- Doc.parse_machine path
--        return (
--            do  [m] <- mch
--                return [m { theory = (theory m) 
--                    { extends = [set_theory train_type] } } ] )
--        

path0 = "Tests/train-station.tex"
case0 = parse_machine path0

result1 = unlines [
        "  o  m0/INIT/FIS",
        "  o  m0/enter/FIS",
        "  o  m0/enter/SCH",
        "  o  m0/leave/FIS",
        "  o  m0/leave/SCH",
        "  o  m0/leave/TR/EN/tr0",
        "  o  m0/leave/TR/NEG/tr0",
        "passed 7 / 7"
        ]
case1 = do
    r <- parse_machine path0
    case r of
        Right [m] -> do
            (s,_,_) <- str_verify_machine m
            return s
        x -> return $ show x

result2 = unlines (
     [  " sort: LOC, TRAIN, set [a]" ]
     ++ set_decl ++
     [  " LOC: (set LOC)"
     ,  " TRAIN: (set TRAIN)"
     ,  " ent: LOC"
     ,  " ext: LOC"
     ,  " in: (set TRAIN)"
     ,  " plf: LOC"
     ] ++ map (" " ++) set_facts ++
     [  " (= LOC (bunion@@LOC (bunion@@LOC (mk-set@@LOC ent) (mk-set@@LOC plf)) (mk-set@@LOC ext)))"
     ,  "|----",
        " (exists ((in (set TRAIN))) true)"] )

case2 = do
        r <- parse_machine path0
        case r of
            Right [m] -> do
                let po = proof_obligation m ! label "m0/INIT/FIS"
                let cmd = unlines $ map (show . as_tree) $ z3_code po
                return $ show po
            x -> return $ show x

result3 = unlines (
     [  " sort: LOC, TRAIN, set [a]" ]
     ++ set_decl ++
     [  " LOC: (set LOC)"
     ,  " TRAIN: (set TRAIN)"
     ,  " ent: LOC"
     ,  " ext: LOC"
     ,  " in: (set TRAIN)"
     ,  " plf: LOC"
     ,  " t: TRAIN"
     ] ++ map (" " ++) set_facts ++
     [  " (= LOC (bunion@@LOC (bunion@@LOC (mk-set@@LOC ent) (mk-set@@LOC plf)) (mk-set@@LOC ext)))"
     ,  "|----",
        " (exists ((in@prime (set TRAIN))) "
            ++ "(= in@prime (set-diff@@TRAIN in (mk-set@@TRAIN t))))"] )

case3 = do
        r <- parse_machine path0
        case r of
            Right [m] -> do
                let po = proof_obligation m ! label "m0/leave/FIS"
                let cmd = unlines $ map (show . as_tree) $ z3_code po
                return $ show po
--                return cmd
            x -> return $ show x

set_decl = 
        [  " elem@@LOC: LOC x (set LOC) -> Bool"
        ,  " elem@@TRAIN: TRAIN x (set TRAIN) -> Bool"
        ,  " mk-set@@LOC: LOC -> (set LOC)"
        ,  " mk-set@@TRAIN: TRAIN -> (set TRAIN)"
        ,  " set-diff@@LOC: (set LOC) x (set LOC) -> (set LOC)"
        ,  " set-diff@@TRAIN: (set TRAIN) x (set TRAIN) -> (set TRAIN)"
        ,  " bunion@@LOC: (set LOC) x (set LOC) -> (set LOC)"
        ,  " bunion@@TRAIN: (set TRAIN) x (set TRAIN) -> (set TRAIN)"
        ]    
    
set_decl_smt2 = 
        [  "(declare-fun elem@@LOC (LOC (set LOC)) Bool)"
        ,  "(declare-fun elem@@TRAIN (TRAIN (set TRAIN)) Bool)"
        ,  "(declare-fun mk-set@@LOC (LOC) (set LOC))"
        ,  "(declare-fun mk-set@@TRAIN (TRAIN) (set TRAIN))"
        ,  "(declare-fun set-diff@@LOC ((set LOC) (set LOC)) (set LOC))"
        ,  "(declare-fun set-diff@@TRAIN ((set TRAIN) (set TRAIN)) (set TRAIN))"
        ,  "(declare-fun bunion@@LOC ((set LOC) (set LOC)) (set LOC))"
        ,  "(declare-fun bunion@@TRAIN ((set TRAIN) (set TRAIN)) (set TRAIN))"
        ]    

set_facts = 
        [ "(forall ((x LOC) (y LOC))" ++
                       " (= (elem@@LOC x (mk-set@@LOC y))" ++
                          " (= x y)))"
        , "(forall ((x TRAIN) (y TRAIN))" ++
                       " (= (elem@@TRAIN x (mk-set@@TRAIN y))" ++
                          " (= x y)))"
        , "(forall ((x LOC) (s1 (set LOC)) (s2 (set LOC)))" ++
                        " (= (elem@@LOC x (set-diff@@LOC s1 s2))" ++
                           " (and (elem@@LOC x s1)" ++
                                " (not (elem@@LOC x s2)))))"
        , "(forall ((x TRAIN) (s1 (set TRAIN)) (s2 (set TRAIN)))" ++
                        " (= (elem@@TRAIN x (set-diff@@TRAIN s1 s2))" ++
                           " (and (elem@@TRAIN x s1)" ++
                                " (not (elem@@TRAIN x s2)))))"
        ]
        
train_decl = 
        [ "(declare-sort LOC 0)"
        , "(declare-sort TRAIN 0)"
        , "(declare-sort set 1)"
        , "(declare-const LOC (set LOC))"
        , "(declare-const TRAIN (set TRAIN))"
        , "(declare-const ent LOC)"
        , "(declare-const ext LOC)"
        , "(declare-const in (set TRAIN))"
        , "(declare-const plf LOC)"
        , "(declare-const t TRAIN)"
        ] ++ set_decl_smt2 ++
--        "(declare-const t TRAIN)"
--        , "(declare-const t TRAIN)"
--        , "(declare-fun elem (TRAIN (set TRAIN)) Bool)"
--        , "(declare-fun mk-set (TRAIN) (set TRAIN))"
--        , "(declare-fun set-diff ((set TRAIN) (set TRAIN)) (set TRAIN))"
--        , "(declare-fun bunion ((set TRAIN) (set TRAIN)) (set TRAIN))"
--        [ "(declare-const ent LOC)"
--        , "(declare-const ext LOC)"
--        , "(declare-const in (set TRAIN))"
--        , "(declare-const plf LOC)"
----        "(declare-const t TRAIN)"
--        , "(declare-const t TRAIN)"
        map (\x -> "(assert " ++ x ++ ")") set_facts

result4 = unlines ( train_decl ++ 
        [ "(assert (= LOC (bunion@@LOC (bunion@@LOC (mk-set@@LOC ent) (mk-set@@LOC plf))"
                                    ++" (mk-set@@LOC ext))))"
        , "(assert (elem@@TRAIN t in))"
        , "(assert (not true))"
        , "(check-sat-using (or-else " ++
            "(then qe smt) " ++
            "(then skip smt) " ++
            "(then (using-params simplify :expand-power true) smt)))"
        ] )

--        " sort: TRAIN",
--        " in: (Array TRAIN Bool)",
----        " t: TRAIN",
--        " (select in t)",
--        "|----",
--        " true"]

case4 = do
        r <- parse_machine path0
        case r of
            Right [m] -> do
                let po = proof_obligation m ! label "m0/leave/SCH"
                let cmd = unlines $ map (show . as_tree) $ z3_code po
--                return $ show po
                return cmd
            x -> return $ show x


result5 = unlines ( train_decl ++
      [ "(assert (= LOC (bunion@@LOC (bunion@@LOC (mk-set@@LOC ent) (mk-set@@LOC plf))"
                                    ++" (mk-set@@LOC ext))))"
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

result6 = unlines ( take 8 train_decl ++ in_prime ++ drop 8 train_decl ++
        [  "(assert (= LOC (bunion@@LOC (bunion@@LOC (mk-set@@LOC ent) (mk-set@@LOC plf)) (mk-set@@LOC ext))))"
        ,  "(assert (elem@@TRAIN t in))"
        ,  "(assert (elem@@TRAIN t in))"
        ,  "(assert (= in@prime (set-diff@@TRAIN in (mk-set@@TRAIN t))))"
        ,  "(assert (not (not (elem@@TRAIN t in@prime))))"
        ,  "(check-sat-using (or-else (then qe smt) (then skip smt) (then (using-params simplify :expand-power true) smt)))"
        ] )
    where
        in_prime = ["(declare-const in@prime (set TRAIN))"]


case6 = do
        r <- parse_machine path0
        case r of
            Right [m] -> do
                let po = proof_obligation m ! label "m0/leave/TR/NEG/tr0"
                let cmd = unlines $ map (show . as_tree) $ z3_code po
                return cmd
            x -> return $ show x

    --------------------
    -- Error handling --
    --------------------

result7 = Left ("Undeclared variables: t",52,1)

path7 = "Tests/train-station-err0.tex"
case7 = parse_machine path7

result8 = Left ("event 'leave' is undeclared",42,1)

path8 = "Tests/train-station-err1.tex"
case8 = parse_machine path8

result9 = Left ("event 'leave' is undeclared",50,1)

path9 = "Tests/train-station-err2.tex"
case9 = parse_machine path9

result10 = Left ("event 'leave' is undeclared",54,1)

path10 = "Tests/train-station-err3.tex"
case10 = parse_machine path10

result11 = Left ("event 'leave' is undeclared",58,1)

path11 = "Tests/train-station-err4.tex"
case11 = parse_machine path11


get_proof_obl name = do
        r <- parse_machine path0
        case r of
            Right [m] -> do
                let po = proof_obligation m ! label name
                let cmd = unlines $ map (show . as_tree) $ z3_code po
--                return $ show po
                putStrLn cmd
            x -> putStrLn $ show x

list_proof_obl = do
        r <- parse_machine path0
        case r of
            Right [m] -> do
--                let po = proof_obligation m ! label name
--                let cmd = unlines $ map (show . as_tree) $ z3_code po
----                return $ show po
--                return $ show $ keys $ proof_obligation m
                forM_ (map show $ keys $ proof_obligation m) putStrLn
            x -> return () -- $ show x
