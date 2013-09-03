module Document.Tests.SmallMachine
    ( test_case, test ) 
where

    -- Modules
import UnitB.AST
import UnitB.PO
import UnitB.Calculation

import Z3.Z3

    -- Libraries
import Data.Map hiding ( map )
import qualified Data.Map as M
import Document.Document

import Tests.UnitTest

import Utilities.Syntactic

test_case = Case "small machine example" test True

test = test_cases [
        (Case "test 0" 
            case0 $ 
            Right $ [m0_machine]),
        (Case "test 1 (separate machine blocks)" 
            case1 $ 
            Right $ [m1_machine]),
        (StringCase "test 2 (verification, one failure)" 
            case2 result2),
        (StringCase "test 3 (verification)" 
            case3 result3),
        (StringCase "test 4 (proof obligation, invariance)" 
            case4 result4),
        (StringCase "test 5 (co, 'skip' proof obligation)" 
            case5 result5) ]


path0 = "Tests/small_machine_t0.tex"
case0 = do
    ct <- readFile path0
    parse_machine path0
    
path1 = "Tests/small_machine_t1.tex"
case1 = do
    ct <- readFile path1
    parse_machine path1

result2 = (unlines [
        "  o  m0/INIT/FIS",
        "  o  m0/INIT/INV/inv0",
        "  o  m0/INIT/INV/inv1",
        "  o  m0/inc/FIS" ,
        "  o  m0/inc/INV/inv0",
        " xxx m0/inc/INV/inv1",
        "  o  m0/inc/SCH",
        " xxx m0/inc/TR/tr0",
--        "  o  m0/inc/TR/NEG/tr0",
        "passed 6 / 8"
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
        "  o  m0/INIT/FIS",
        "  o  m0/INIT/INV/inv0",
        " xxx m0/SKIP/CO/c0",
        "  o  m0/inc/CO/c0",
        "  o  m0/inc/FIS" ,
        "  o  m0/inc/INV/inv0",
        "  o  m0/inc/SCH",
        "  o  m0/inc/TR/tr0",
        "passed 7 / 8"
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
        " sort: , , , pfun [a,b], set [a]",
        " x: Int",
        " x@prime: Int",
        " y: Int",
        " y@prime: Int",
        " (= x (* 2 y))",
        " (= x@prime (+ x 2))",
        " (= y@prime (+ y 1))",
        "|----",
        " (= x@prime (* 2 y@prime))"]

show_po lbl = do
        m <- parse_machine path3
        r <- return (do
            [m] <- m
            po <- proof_obligation m 
            return (po ! lbl) )
        case r of
            Right po -> do
                return $ show po
            Left x -> return $ show_err x


case4 = show_po $ label "m0/inc/INV/inv0"

result5 = unlines [
        " sort: , , , pfun [a,b], set [a]",
        " x: Int",
        " x@prime: Int",
        " y: Int",
        " y@prime: Int",
        " (= x (* 2 y))",
        " (= x@prime x)",
        " (= y@prime y)",
        "|----",
        " (=> (= x 2) (= x@prime 4))"]

case5 = show_po $ label "m0/SKIP/CO/c0"

var_x = Var "x" int
var_y = Var "y" int

var_x' = Var "x@prime" int
var_y' = Var "y@prime" int

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

m1_props = m0_props
        { transient = fromList [
            (label "tr0", Transient empty (x `zeq` y) (label "inc")) ]
        , constraint = fromList [
            (label "c0", Co [] ( (x `zeq` z1) `zimplies` (x' `zeq` z2) )) ]
        , inv = insert (label "inv1") (x `zeq` (x `ztimes` (y `zplus` z1))) (inv m0_props)
        }
    where
        x  = Word var_x
        y  = Word var_y
        x' = Word var_x'
        y' = Word var_y'
        z1 = zint 1
        z2 = zint 2
