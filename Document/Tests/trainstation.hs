module Document.Tests.TrainStation
    ( test_case )
where

import Data.Map hiding ( map )
import qualified Data.Map as M
import Document.Document

import Tests.UnitTest

import UnitB.AST
import UnitB.PO

import Z3.Calculation
import Z3.Const
import Z3.Def
import Z3.Z3

test_case = Case "train station example" test True

--test :: IO Bool
test = test_cases [
            (Case "test 0, syntax" case0 $ Right [machine0])
            , (StringCase "test 1, verification" case1 result1)
            , (StringCase "test 2, proof obligation, INIT/fis" case2 result2)
            , (StringCase "test 3, proof obligation, leave/fis" case3 result3)
            , (StringCase "test 4, proof obligation, leave/sch" case4 result4)
            , (StringCase "test 5, proof obligation, leave/en/tr0" case5 result5)
            , (StringCase "test 6, proof obligation, leave/neg/tr0" case6 result6)
            , (Case "test 7, undeclared symbol" case7 result7)
            ]

trainType = USER_DEFINED "TRAIN"

machine0 = (empty_machine "m0") {
        theory = empty_theory { 
                types = fromList [("\\TRAIN", Sort "\\TRAIN" "TRAIN")], 
                dummies = singleton "t" $ Var "t" $ trainType },
        variables = singleton "in" (Var "in" $ SET trainType),
        events = fromList [(label "enter", empty_event), (label "leave", leave_evt)],
        props = props0
    }
props0 = empty_property_set {
        program_prop = singleton (label "tr0") 
            (Transient 
                (singleton "t" $ Var "t" trainType) 
                (t `zelem` in_var) (label "leave") )
        }

leave_evt = empty_event {
        indices = symbol_table [t_decl],
        c_sched = Just $ singleton (label "c0") (t `zelem` in_var),
        action = fromList [(label "a0", (in_var' `zapply` t) `zeq` zfalse)] }

(t, t_decl) = var "t" trainType
(in_var, in_var', in_decl) = prog_var "in" (SET trainType)

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
        "passed 6 / 7"
        ]
case1 = do
    r <- parse_machine path0
    case r of
        Right [m] -> do
            (s,_,_) <- str_verify_machine m
            return s
        x -> return $ show x

result2 = unlines [
        " sort: TRAIN",
        " in: (Array TRAIN Bool)",
        "|----",
        " (exists ((in (Array TRAIN Bool))) true)"]

case2 = do
        r <- parse_machine path0
        case r of
            Right [m] -> do
                let po = proof_obligation m ! label "m0/INIT/FIS"
                let cmd = unlines $ map (show . as_tree) $ z3_code po
                return $ show po
            x -> return $ show x

result3 = unlines [
        " sort: TRAIN",
        " in: (Array TRAIN Bool)",
        " t: TRAIN",
        "|----",
        " (exists ((in@prime (Array TRAIN Bool))) (= (select in@prime t) false))"]

case3 = do
        r <- parse_machine path0
        case r of
            Right [m] -> do
                let po = proof_obligation m ! label "m0/leave/FIS"
                let cmd = unlines $ map (show . as_tree) $ z3_code po
                return $ show po
--                return cmd
            x -> return $ show x
            
result4 = unlines 
        [ "(declare-sort TRAIN)"
        , "(declare-const in (Array TRAIN Bool))"
--        "(declare-const t TRAIN)"
        , "(declare-const t TRAIN)"
        , "(assert (select in t))"
        , "(assert (not true))"
        , "(check-sat-using (or-else " ++
            "(then qe smt) " ++
            "(then skip smt) " ++
            "(then (using-params simplify :expand-power true) smt)))"
        ]

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


result5 = unlines [
        "(declare-sort TRAIN)",
        "(declare-const in (Array TRAIN Bool))",
--        "(declare-const t TRAIN)",
        "(declare-const t TRAIN)",
        "(assert (not (exists ((t TRAIN)) (=> (select in t) (select in t)))))",
        "(check-sat-using (or-else (then qe smt) (then skip smt) (then (using-params simplify :expand-power true) smt)))"
    ]

case5 = do
        r <- parse_machine path0
        case r of
            Right [m] -> do
                let po = proof_obligation m ! label "m0/leave/TR/EN/tr0"
                let cmd = unlines $ map (show . as_tree) $ z3_code po
--                return $ show po
                return cmd
            x -> return $ show x

result6 = unlines [
        "(declare-sort TRAIN)",
        "(declare-const in (Array TRAIN Bool))",
        "(declare-const in@prime (Array TRAIN Bool))",
        "(declare-const t TRAIN)",
--        "(declare-const t TRAIN)",
        "(assert (select in t))",
        "(assert (select in t))",
        "(assert (= (select in@prime t) false))",
--        "(assert false)",
        "(assert (not (not (select in@prime t))))",
        "(check-sat-using (or-else (then qe smt) (then skip smt) (then (using-params simplify :expand-power true) smt)))"
    ]

case6 = do
        r <- parse_machine path0
        case r of
            Right [m] -> do
                let po = proof_obligation m ! label "m0/leave/TR/NEG/tr0"
                let cmd = unlines $ map (show . as_tree) $ z3_code po
--                return $ show po
                return cmd
            x -> return $ show x

result7 = Left "(\"Undeclared variables: t\",50,1)"

path7 = "Tests/train-station-err0.tex"
case7 = parse_machine path7