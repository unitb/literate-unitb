module Document.Tests.Cubes ( test_case ) where

import Data.Map hiding ( map )
--import qualified Data.Map as M
import Document.Document

import Tests.UnitTest

import UnitB.AST
import UnitB.PO

import Z3.Calculation
import Z3.Const
import Z3.Def
import Z3.Z3

test_case = Case "table of cubes example" test True

test = test_cases
       [ (Case "test 0 (syntax)" 
             case6 $ Right [machine6]),
         (StringCase "test 1 (verification)" 
             case7 result7),
         (StringCase "test 2 (init/fis po)" 
             case8 result8),
         (StringCase "proof of inv0" 
             case9 result9),
         (StringCase "empty proof"
             case10 result10) ]

var_a = Var "a" INT
var_b = Var "b" INT
var_c = Var "c" INT
var_n = Var "n" INT

var_a' = Var "a@prime" INT
var_b' = Var "b@prime" INT
var_c' = Var "c@prime" INT
var_n' = Var "n@prime" INT

machine6 = (empty_machine "m0") {
        variables = fromList $ map as_pair [var_a,var_b,var_c,var_n],
        inits = [
                (c `zeq` z6),
                (b `zeq` z1),
                (n `zeq` z0) `zand` (a `zeq` z0) ],
        props = prop_set6,
        events = singleton (label "evt") event6_evt }
    where
        a = Word var_a
        b = Word var_b
        c = Word var_c
        n = Word var_n
        z0 = zint 0
        z1 = zint 1
        z6 = zint 6

prop_set6 = empty_property_set {
        proofs = fromList [ 
                    (label "m0/evt/INV/inv0", calc),
                    (label "m0/evt/INV/inv1", calc),
                    (label "m0/evt/INV/inv2", calc) ],
        inv = fromList $ zip 
                (map label ["inv0","inv1","inv2"]) 
                [ (a `zeq` (n `zpow` z3)),
                  (b `zeq` ( (zint 3 `ztimes` (n `zpow` zint 2))
                     `zplus` (zint 3 `ztimes` n)
                     `zplus` zint 1) ), 
                  (c `zeq` ((z6 `ztimes` n) `zplus` z6)) ] }
    where
        a = Word var_a
        b = Word var_b
        c = Word var_c
        n = Word var_n
        z3 = zint 3
        z6 = zint 6
        calc = Calc (step_ctx machine6) ztrue ztrue [] (0,0)

event6_evt = empty_event {
        action = fromList $ zip 
            (map label ["a1", "a0", "a2", "a3"])
            [ a' `zeq` (a `zplus` b), 
              n' `zeq` (n `zplus` zint 1),
              b' `zeq` (b `zplus` c),
              c' `zeq` (c `zplus` zint 6) ] }
    where
        a  = Word var_a
        a' = Word var_a'
        n  = Word var_n
        n' = Word var_n'
        b  = Word var_b
        b' = Word var_b'
        c  = Word var_c
        c' = Word var_c'
    
path6    = "Tests/integers.tex"
case6    = parse_machine path6

result7 = unlines [
        "  o  m0/INIT/FIS",
        "  o  m0/INIT/INV/inv0",
        "  o  m0/INIT/INV/inv1",
        "  o  m0/INIT/INV/inv2",
        "  o  m0/evt/FIS",
        "  o  m0/evt/INV/inv0",
        "  o  m0/evt/INV/inv1",
        "  o  m0/evt/INV/inv2",
        "  o  m0/evt/SCH",
        "passed 9 / 9"]

case7 = do
    r <- parse_machine path6
    case r of
        Right [m] -> do
            (s,_,_)   <- str_verify_machine m
            return s
        x -> return $ show x

path8   = "Tests/integers_t8.tex"
result8 = unlines [
        " sort: ",
        " x: Int",
        "|----",
        " (exists ((x Int)) true)"]

case8 = do
        r <- parse_machine path8
        case r of
            Right [m] -> do
                let po = proof_obligation m ! label "m0/INIT/FIS"
                return $ show po
            x -> return $ show x

pos = do
    r <- parse_machine path6
    case r of
        Right [m] -> do
            let po = proof_obligation m ! label "m0/evt/INV/inv0"
            return $ show po
        x -> return $ show x

result9 = unlines [
        "m0/evt/INV/inv0:",
        "(= (^ n@prime 3) a@prime)",
        "----",
        "    (^ n@prime 3)",
        "      | (= n@prime (+ n 1))",
        "    (^ (+ n 1) 3)",
        "    (+ (+ (+ (^ n 3) (* 3 (^ n 2)))" ++
                 " (* 3 n))" ++
              " 1)",
        "      | (= a (^ n 3))",
        "    (+ (+ (+ a (* 3 (^ n 2)))" ++
                 " (* 3 n))" ++
              " 1)",
        "      | (= b (+ (+ (* 3 (^ n 2)) (* 3 n)) 1))",
        "    (+ a b)",
        "      | (= a@prime (+ a b))",
        "    a@prime"
    ]
case9 = do
        r <- parse_machine path6
        case r of
            Right [m] -> do
                case toList $ proofs $ props m of
                    (lbl,calc):xs -> 
                        return (show lbl ++ ":\n" ++ show_proof calc)
                    xs       -> return (
                                      "error: found "
                                   ++ show (length xs) 
                                   ++ " proofs")
            x -> return $ show x

result10 = unlines [
        " xxx m0/INIT/FIS",
        "     incorrect proof: ",
        "         cannot prove a relationship " ++
                 "between the first and the last line: (31,1)",
        "     proof does not match proof obligation: (31,1)",
        "passed 0 / 1"]
case10 = do
    r <- parse_machine path8
    case r of
        Right [m] -> do
            (s,_,_)   <- str_verify_machine m
            return s
        x -> return $ show x
