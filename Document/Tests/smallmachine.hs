module Document.Tests.SmallMachine
    ( test_case, test ) 
where

    -- Modules
import Document.Document

import Logic.Const
import Logic.Expr
import Logic.Label

import UnitB.AST
import UnitB.PO

    -- Libraries
import           Data.Map hiding ( map )
import qualified Data.Set as S ( singleton )

import Tests.UnitTest

import Utilities.Syntactic

test_case :: TestCase
test_case = Case "small machine example" test True

test :: IO Bool
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
            case5 result5),
        (StringCase "test 6 (verification, coarse schedule stronger than guard)" 
            case6 result6),
        (StringCase "test 7 (schedulability proof obligation)" 
            case7 result7),
        (StringCase "test 8 (schedulability without selecting schedules (trivially true))" 
            case8 result8),
        (StringCase "test 9 (coarse schedule weakening, PO)" 
            case9 result9),
        (StringCase "test 10 (transient PO, enablement)" 
            case10 result10), 
        (StringCase "test 11 (transient PO, negation)" 
            case11 result11)  ]

path0 :: String
path0 = "Tests/small_machine_t0.tex"

case0 :: IO (Either [Error] [Machine])
case0 = do
    parse_machine path0
    
path1 :: String
path1 = "Tests/small_machine_t1.tex"

case1 :: IO (Either [Error] [Machine])
case1 = do
    parse_machine path1

result2 :: String
result2 = (unlines 
	  [ "  o  m0/INIT/FIS/x"
      , "  o  m0/INIT/FIS/y"
      , "  o  m0/INIT/INV/inv0"
      , "  o  m0/INIT/INV/inv1"
      , "  o  m0/inc/FIS/x@prime" 
      , "  o  m0/inc/FIS/y@prime" 
      , "  o  m0/inc/INV/inv0"
      , " xxx m0/inc/INV/inv1"
      , "  o  m0/inc/SCH"
      , "  o  m0/inc/SCH/m0/0/REF/replace/prog/lhs"
      , "  o  m0/inc/SCH/m0/0/REF/replace/prog/rhs"
      , "  o  m0/inc/SCH/m0/0/REF/replace/str"
      , " xxx m0/inc/TR/tr0/EN"
      , "  o  m0/inc/TR/tr0/EN/leadsto/lhs"
      , "  o  m0/inc/TR/tr0/EN/leadsto/rhs"
      , "  o  m0/inc/TR/tr0/NEG"
      , " xxx m0/prog0/REF/add"
      , "passed 14 / 17"
    ])

path2 :: String
path2 = "Tests/small_machine_t2.tex"
case2 :: IO String
case2 = do
    r <- parse_machine path2
    case r of
        Right [m] -> do
            (s,_,_)   <- str_verify_machine m
            return s
        x -> return $ show x

result3 :: String
result3 = (unlines 
      [ "  o  m0/INIT/FIS/x"
      , "  o  m0/INIT/FIS/y"
      , "  o  m0/INIT/INV/inv0"
      , " xxx m0/SKIP/CO/c0"
      , "  o  m0/inc/CO/c0"
      , "  o  m0/inc/FIS/x@prime" 
      , "  o  m0/inc/FIS/y@prime" 
      , "  o  m0/inc/INV/inv0"
      , "  o  m0/inc/SCH"
      , "  o  m0/inc/SCH/m0/0/REF/weaken"
      , "  o  m0/inc/TR/tr0/EN"
      , "  o  m0/inc/TR/tr0/NEG"
      , "passed 11 / 12"
    ])

path3 :: String
path3 = "Tests/small_machine.tex"

case3 :: IO String
case3 = do
    r <- parse_machine path3
    case r of
        Right [m] -> do
            (s,_,_)   <- str_verify_machine m
            return s
        x -> return $ show x

result4 :: String
result4 = unlines [
        " sort: Pair [a,b], , , "
      , " x: Int"
      , " x@prime: Int"
      , " y: Int"
      , " y@prime: Int"
      , " (= x@prime (+ x 2))"
      , " (= y@prime (+ y 1))"
      , " (= x (* 2 y))"
      , "|----"
      , " (= x@prime (* 2 y@prime))"]

show_po :: FilePath -> Label -> IO String
show_po path lbl = do
        m <- parse_machine path
        r <- return (do
            [m] <- m
            po <- proof_obligation m 
            return (po ! lbl) )
        case r of
            Right po -> do
                return $ show po
            Left x -> return $ show_err x


case4 :: IO String
case4 = show_po path3 $ label "m0/inc/INV/inv0"

result5 :: String
result5 = unlines [
        " sort: Pair [a,b], , , "
      , " x: Int"
      , " x@prime: Int"
      , " y: Int"
      , " y@prime: Int"
      , " (= x@prime x)"
      , " (= y@prime y)"
      , " (= x (* 2 y))"
      , "|----"
      , " (=> (= x 2) (= x@prime 4))"]

case5 :: IO String
case5 = show_po path3 $ label "m0/SKIP/CO/c0"

result6 :: String
result6 = (unlines 
      [ "  o  m0/INIT/FIS/x"
      , "  o  m0/INIT/FIS/y"
      , "  o  m0/INIT/INV/inv0"
      , " xxx m0/SKIP/CO/c0"
      , "  o  m0/inc/CO/c0"
      , "  o  m0/inc/FIS/x@prime" 
      , "  o  m0/inc/FIS/y@prime" 
      , "  o  m0/inc/INV/inv0"
      , "  o  m0/inc/SCH"
      , "  o  m0/inc/SCH/m0/1/REF/weaken"
      , "  o  m0/inc/TR/tr0/EN"
      , "  o  m0/inc/TR/tr0/NEG"
      , "passed 11 / 12"
    ])

path6 :: String
path6 = "Tests/small_machine_t3.tex"

case6 :: IO String
case6 = do
    r <- parse_machine path6
    case r of
        Right [m] -> do
            (s,_,_)   <- str_verify_machine m
            return s
        x -> return $ show x

result7 :: String
result7 = unlines [
        " sort: Pair [a,b], , , "
      , " x: Int"
      , " y: Int"
      , " (= x y)"
      , " (= x (* 2 y))"
      , "|----"
      , " (= x y)"]

case7 :: IO String
case7 = show_po path6 $ label "m0/inc/SCH"

path8 :: FilePath
path8 = "Tests/small_machine_t4.tex"

result8 :: String
result8 = unlines [
        " sort: Pair [a,b], , , "
      , " x: Int"
      , " y: Int"
      , " false"
      , " (= x (* 2 y))"
      , "|----"
      , " (= x y)"]

case8 :: IO String
case8 = show_po path8 $ label "m0/inc/SCH"

result9 :: String
result9 = unlines [
        " sort: Pair [a,b], , , "
      , " x: Int"
      , " x@prime: Int"
      , " y: Int"
      , " y@prime: Int"
      , " (= x (* 2 y))"
      , "|----",
            -- This should be the goal but it boils down to true
            -- after Literate Unit-B has simplified it
--        " (=> false (= x y))"]
        " true"]

case9 :: IO String
case9 = show_po path6 $ label "m0/inc/SCH/m0/1/REF/weaken"

result10 :: String
result10 = unlines [
        " sort: Pair [a,b], , , "
      , " x: Int"
      , " x@prime: Int"
      , " y: Int"
      , " y@prime: Int"
      , " (= x (* 2 y))"
      , "|----"
      , " (=> (= x y) (= x y))" ]

case10 = show_po path6 $ label "m0/inc/TR/tr0/EN"

result11 :: String
result11 = unlines [
        " sort: Pair [a,b], , , "
      , " x: Int"
      , " x@prime: Int"
      , " y: Int"
      , " y@prime: Int"
      , " (= x@prime (+ x 2))" 
      , " (= y@prime (+ y 1))" 
      , " (= x y)" 
      , " (= x y)" 
      , " (= x (* 2 y))"
      , "|----"
      , " (=> (= x y)" ++
            " (not (= x@prime y@prime)))" ]

case11 :: IO String
case11 = show_po path6 $ label "m0/inc/TR/tr0/NEG"

var_x :: Var
var_y :: Var
var_x' :: Var
var_y' :: Var

var_x = Var "x" int
var_y = Var "y" int

var_x' = Var "x@prime" int
var_y' = Var "y@prime" int

inc_event_m0 :: Event
inc_event_m0 = empty_event { 
    action = fromList [
                (label "a0",Word var_x' `zeq` (Word var_x `zplus` zint 2)) ] }

inc_event_m1 :: Event
inc_event_m1 = empty_event 
        { sched_ref = [sc]
        , scheds = fromList 
            [ (label "c0", x `zeq` y) 
            , (label "f0", x `zeq` y) ]
            `union` default_schedule
        , action  = fromList [
                    (label "a0",Word var_x' `zeq` (Word var_x `zplus` zint 2)),
                    (label "a1",Word var_y' `zeq` (Word var_y `zplus` zint 1)) ] 
        }
    where
        x = Word var_x
        y = Word var_y

sc :: ScheduleChange
sc = (weaken (label "inc"))
        { add = S.singleton (label "c0")
        , remove = S.singleton (label "default")
        }

m0_machine :: Machine
m0_machine = (empty_machine "m0") { 
        props = m0_props,
        events = singleton (label "inc") inc_event_m0,
        variables = fromList [("x", var_x), ("y", var_y)] }

m1_machine :: Machine
m1_machine = (empty_machine "m0") 
        { props = m1_props
        , events = singleton (label "inc") inc_event_m1
        , variables = fromList [("x", var_x), ("y", var_y)] 
        }

m0_props :: PropertySet
m0_props = empty_property_set {
        inv = singleton (label "inv0") (x `zeq` (zint 2 `ztimes` y)) }
    where
        x = Word var_x
        y = Word var_y

m1_props :: PropertySet
m1_props = m0_props
        { transient = fromList [
            (label "tr0", Transient empty (x `zeq` y) (label "inc") empty Nothing) ]
        , constraint = fromList [
            (label "c0", Co [] ( (x `zeq` z1) `zimplies` (x' `zeq` z2) )) ]
        , inv = insert 
                (label "inv1") 
                (x `zeq` (x `ztimes` (y `zplus` z1))) 
                (inv m0_props)
        , derivation = singleton (label "inc/SCH/m0/0") (Rule sc)
        }
    where
        x  = Word var_x
        y  = Word var_y
        x' = Word var_x'
        z1 = zint 1
        z2 = zint 2

