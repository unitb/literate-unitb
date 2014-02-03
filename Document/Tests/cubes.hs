module Document.Tests.Cubes ( test_case, test ) where

--import qualified Data.Map as M
import Document.Document

import Tests.UnitTest

import Logic.Classes
import Logic.Const
import Logic.Expr
import Logic.Label
import Logic.Calculation

import UnitB.AST
import UnitB.PO

    -- Libraries
import Data.Map hiding ( map )
import Data.Typeable

import Utilities.Syntactic

test_case = Case "table of cubes example" test True

test = test_cases
        [ (Case "test 0 (syntax)" 
                case6 $ Right [machine6])
        , (StringCase "test 1 (verification)" 
                case7 result7)
        , (StringCase "test 2 (init/fis po)" 
             case8 result8)
        , (StringCase "proof of inv0" 
             case9 result9)
        , (StringCase "empty proof"
             case10 result10) 
        ]

var_a = Var "a" int
var_b = Var "b" int
var_c = Var "c" int
var_n = Var "n" int

var_a' = Var "a@prime" int
var_b' = Var "b@prime" int
var_c' = Var "c@prime" int
var_n' = Var "n@prime" int

machine6 = (empty_machine "m0") 
        {  variables = fromList $ map as_pair [var_a,var_b,var_c,var_n]
        ,  inits = fromList
                [ (label "in2", c `zeq` z6)
                , (label "in1", b `zeq` z1)
                , (label "init0", (n `zeq` z0) `zand` (a `zeq` z0) )
                ]
        ,  props = prop_set6
        ,  events = singleton (label "evt") event6_evt 
        }
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
        calc = Proof $ Calc (step_ctx machine6) ztrue ztrue [] (LI "" 1 1)

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

result7 = unlines 
      [ "  o  m0/INIT/FIS/a"
      , "  o  m0/INIT/FIS/b"
      , "  o  m0/INIT/FIS/c"
      , "  o  m0/INIT/FIS/n"
      , "  o  m0/INIT/INV/inv0"
      , "  o  m0/INIT/INV/inv1"
      , "  o  m0/INIT/INV/inv2"
      , "  o  m0/evt/FIS/a@prime"
      , "  o  m0/evt/FIS/b@prime"
      , "  o  m0/evt/FIS/c@prime"
      , "  o  m0/evt/FIS/n@prime"
      , "  o  m0/evt/INV/inv0/goal (62,1)"
      , "  o  m0/evt/INV/inv0/hypotheses (62,1)"
      , "  o  m0/evt/INV/inv0/relation (62,1)"
      , "  o  m0/evt/INV/inv0/step (64,1)"
      , "  o  m0/evt/INV/inv0/step (66,1)"
      , "  o  m0/evt/INV/inv0/step (68,1)"
      , "  o  m0/evt/INV/inv0/step (70,1)"
      , "  o  m0/evt/INV/inv0/step (72,1)"
      , "  o  m0/evt/INV/inv1/goal (139,1)"
      , "  o  m0/evt/INV/inv1/hypotheses (139,1)"
      , "  o  m0/evt/INV/inv1/relation (139,1)"
      , "  o  m0/evt/INV/inv1/step (141,1)"
      , "  o  m0/evt/INV/inv1/step (143,1)"
      , "  o  m0/evt/INV/inv1/step (145,1)"
      , "  o  m0/evt/INV/inv1/step (147,1)"
      , "  o  m0/evt/INV/inv1/step (149,1)"
      , "  o  m0/evt/INV/inv1/step (151,1)"
      , "  o  m0/evt/INV/inv2/goal (178,1)"
      , "  o  m0/evt/INV/inv2/hypotheses (178,1)"
      , "  o  m0/evt/INV/inv2/relation (178,1)"
      , "  o  m0/evt/INV/inv2/step (180,1)"
      , "  o  m0/evt/INV/inv2/step (182,1)"
      , "  o  m0/evt/INV/inv2/step (184,1)"
      , "  o  m0/evt/INV/inv2/step (186,1)"
      , "  o  m0/evt/SCH"
      , "passed 36 / 36"]

case7 = do
    r <- parse_machine path6
    case r of
        Right [m] -> do
            (s,_,_)   <- str_verify_machine m
            return s
        x -> return $ show x

path8   = "Tests/integers_t8.tex"
result8 = unlines [
        " sort: , , ",
        " x: Int",
        "|----",
        " (exists ((x Int)) (and true true))"]

case8 = do
        m <- parse_machine path8
        let r = (do 
                [m] <- m
                pos  <- proof_obligation m
                return (pos ! label "m0/INIT/FIS/x"))
        case r of
            Right po -> 
                return $ show po
            x -> 
                return $ show x

--pos = do
--        m <- parse_machine path8
--        let r = (do 
--                [m] <- m
--                pos  <- proof_obligation m
--                return (pos ! label "m0/evt/INV/inv0"))
--        case r of
--            Right po -> 
--                return $ show po
--            x -> 
--                return $ show x

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
                    (lbl,Proof calc):_ -> 
                        case cast calc of
                            Just calc ->
                                return (show lbl ++ ":\n" ++ show_proof calc)
                            _         ->
                                return (
                                      "error: incorrect proof type" ++ show (typeOf calc))
                    xs       -> return (
                                      "error: found "
                                   ++ show (length xs) 
                                   ++ " proofs")
            x -> return $ show x

path10   = "Tests/integers_t10.tex"
result10 = "Left [Error \"type error: a calculation must include at least one reasoning step\" (31,1)]"
case10 = do
    r <- parse_machine path10
    case r of
        Right [m] -> do
            (s,_,_)   <- str_verify_machine m
            return s
        x -> return $ show x
