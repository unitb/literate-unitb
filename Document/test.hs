module Document.Test where

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

test_case = ("Unit-B Document", test, True)

var_x = Var "x" INT
var_y = Var "y" INT

var_x' = Var "x_prime" INT
var_y' = Var "y_prime" INT

inc_event_m0 = empty_event { 
    action = fromList [
                (label "a0",Word var_x' `zeq` (Word var_x `zplus` zint 2)) ] }

inc_event_m1 = empty_event { 
        c_sched = Just $ fromList [((label "c0"), x `zeq` y)],
        f_sched = Just (x `zeq` y),
        action  = fromList [
                    (label "a0",Word var_x' `zeq` (Word var_x `zplus` zint 2)),
                    (label "a1",Word var_y' `zeq` (Word var_y `zplus` zint 1)) ] }
    where
        x = Word var_x
        y = Word var_y

m0_machine = (empty_machine "m0") { 
        props = m0_props,
        events = singleton (label "inc") inc_event_m0,
        variables = fromList [("x", var_x), ("y", var_y)] }

m1_machine = (empty_machine "m0") { 
        props = m1_props,
        events = singleton (label "inc") inc_event_m1,
        variables = fromList [("x", var_x), ("y", var_y)] }

m0_props = empty_property_set {
        inv = singleton (label "inv0") (x `zeq` (zint 2 `ztimes` y)) }
    where
        x = Word var_x
        y = Word var_y

m1_props = m0_props {
        program_prop = fromList [
            (label "tr0", Transient [] (x `zeq` y) (label "inc")),
            (label "c0", Co [] ( (x `zeq` z1) `zimplies` (x' `zeq` z2) )) ],
        inv = insert (label "inv1") (x `zeq` (x `ztimes` (y `zplus` z1))) (inv m0_props) }
    where
        x  = Word var_x
        y  = Word var_y
        x' = Word var_x'
        y' = Word var_y'
        z1 = zint 1
        z2 = zint 2

test :: IO Bool
test = test_cases [
        (Case "small machine, test 0" 
            case0 $ 
            Right $ [m0_machine]),
        (Case "small machine, test 1 (separate machine blocks)" 
            case1 $ 
            Right $ [m1_machine]),
        (StringCase "small machine, test 2 (verification, one failure)" 
            case2 result2),
        (StringCase "small machine, test 3 (verification)" 
            case3 result3),
        (StringCase "small machine, test 4 (proof obligation, invariance)" 
            case4 result4),
        (StringCase "small machine, test 5 (co, 'skip' proof obligation)" 
            case5 result5),
        (Case "table of cubes, test 0 (syntax)" 
            case6 $ Right [machine6]),
--        (StringCase "table of cubes, test 1 (verification)" 
--            case7 result7),
--        (StringCase "table of cubes, test 2 (init/fis po)" 
--            case8 result8),
        (StringCase "table of cubes, proof of inv0" 
            case9 result9) 
        ]

path0 = "Tests/small_machine_t0.tex"
case0 = do
    ct <- readFile path0
    parse_machine path0
    
path1 = "Tests/small_machine_t1.tex"
case1 = do
    ct <- readFile path1
    parse_machine path1

result2 = (unlines [
        " o m0/INIT/FIS",
        " o m0/INIT/INV/inv0",
        " o m0/INIT/INV/inv1",
        " o m0/inc/FIS" ,
        " o m0/inc/INV/inv0",
        " x m0/inc/INV/inv1",
        " o m0/inc/SCH",
        " x m0/inc/TR/EN/tr0",
        " o m0/inc/TR/NEG/tr0",
        "passed 7 / 9"
    ])

path2 = "Tests/small_machine_t2.tex"
case2 = do
    ct  <- readFile path2
    r <- parse_machine path2
    case r of
        Right [m] -> do
            (s,_,_)   <- str_verify_machine m
            return s
        x -> return $ show x

result3 = (unlines [
        " o m0/INIT/FIS",
        " o m0/INIT/INV/inv0",
        " x m0/SKIP/CO/c0",
        " o m0/inc/CO/c0",
        " o m0/inc/FIS" ,
        " o m0/inc/INV/inv0",
        " o m0/inc/SCH",
        " o m0/inc/TR/EN/tr0",
        " o m0/inc/TR/NEG/tr0",
        "passed 8 / 9"
    ])

path3 = "Tests/small_machine.tex"
case3 = do
    ct  <- readFile path3
    r <- parse_machine path3
    case r of
        Right [m] -> do
            (s,_,_)   <- str_verify_machine m
            return s
        x -> return $ show x

result4 = unlines [
        " x: Int",
        " x_prime: Int",
        " y: Int",
        " y_prime: Int",
        " (= x (* 2 y))",
        " (= x_prime (+ x 2))",
        " (= y_prime (+ y 1))",
        "|----",
        " (= x_prime (* 2 y_prime))"]
case4 = do
        ct <- readFile path3
        r <- parse_machine path3
        case r of
            Right [m] -> do
                let po = proof_obligation m ! label "m0/inc/INV/inv0"
                return $ show po
            x -> return $ show x

result5 = unlines [
        " x: Int",
        " x_prime: Int",
        " y: Int",
        " y_prime: Int",
        " (= x (* 2 y))",
        " (= x_prime x)",
        " (= y_prime y)",
        "|----",
        " (=> (= x 2) (= x_prime 4))"]
case5 = do
        r <- parse_machine path3
        case r of
            Right [m] -> do
                let po = proof_obligation m ! label "m0/SKIP/CO/c0"
                return $ show po
            x -> return $ show x

var_a = Var "a" INT
var_b = Var "b" INT
var_c = Var "c" INT
var_n = Var "n" INT

var_a' = Var "a_prime" INT
var_b' = Var "b_prime" INT
var_c' = Var "c_prime" INT
var_n' = Var "n_prime" INT

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
        calc = Calc (step_ctx m1_machine) ztrue ztrue []

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
        " o m0/INIT/FIS",
        " o m0/INIT/INV/inv0",
        " o m0/INIT/INV/inv1",
        " o m0/evt/FIS",
        " o m0/evt/INV/inv0",
        " x m0/evt/INV/inv1",
        " o m0/evt/SCH",
        "passed 5 / 7"]

case7 = do
    r <- parse_machine path6
    case r of
        Right [m] -> do
            (s,_,_)   <- str_verify_machine m
            return s
        x -> return $ show x

path8   = "Tests/integers_t8.tex"
result8 = unlines [
        "|----",
        " true"]

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
        "(= (^ n_prime 3) a_prime)",
        "----",
        "    (^ n_prime 3)",
        "      | (= n_prime (+ n 1))",
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
        "      | (= a_prime (+ a b))",
        "    a_prime"
    ]
case9 = do
        r <- parse_machine path6
        case r of
            Right [m] -> do
                case toList $ proofs $ props m of
                    (lbl,calc):xs -> 
                        return (show lbl ++ ":\n" ++ show_proof calc)
                    xs       -> return ("error: found " ++ show (length xs) ++ " proofs")
            x -> return $ show x