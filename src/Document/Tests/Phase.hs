module Document.Tests.Phase where

    -- Modules
import Document.Tests.Suite

    -- Libraries
import Test.UnitTest


test_case :: TestCase
test_case = test

test :: TestCase
test = test_cases 
            "refinement relations in the phase example" 
            [ (aCase "test 0, cyclic refinement relation between machines" (find_errors path0) result0)
            , (aCase "test 1, valid references to variables and event declared in ancestor" case1 result1)
            , (aCase "test 2, invalid proof obligations" case2 result2)
            ] 

path0 :: FilePath
path0 = [path|Tests/phases-t0.tex|]

result0 :: String
result0 = unlines
    [ "A cycle exists in the refinement structure"
    , "error 174:1:"
    , "\tm0"
    , ""
    , "error 180:1:"
    , "\tm1"
    , ""
    ]

path1 :: FilePath
path1 = [path|Tests/phases-t1.tex|]

case1 :: IO String
case1 = find_errors path1 

result1 :: String
result1 = "no errors"

path2 :: FilePath
path2 = [path|Tests/phases-t2.tex|]

case2 :: IO String
case2 = find_errors path2

result2 :: String
result2 = unlines
    [ "error 96:8:"
    , "    proof obligation does not exist: m0/TR/tr0/step/NEG"
    , ""
    , "m0/prog0/LIVE/disjunction/lhs"
    , "m0/prog0/LIVE/disjunction/rhs"
    , "m0/prog0/PROG/WD/rhs"
    , "m0/prog1/LIVE/implication"
    , "m0/prog1/PROG/WD/lhs"
    , "m0/prog1/PROG/WD/rhs"
    , "m0/prog2/LIVE/induction/lhs"
    , "m0/prog2/LIVE/induction/rhs"
    , "m0/prog2/PROG/WD/lhs"
    , "m0/prog2/PROG/WD/rhs"
    , "m0/prog3/LIVE/PSP/lhs"
    , "m0/prog3/LIVE/PSP/rhs"
    , "m0/prog3/PROG/WD/lhs"
    , "m0/prog3/PROG/WD/rhs"
    , "m0/prog4/LIVE/discharge/tr/lhs"
    , "m0/prog4/LIVE/discharge/tr/rhs"
    , "m0/prog4/PROG/WD/lhs"
    , "m0/prog4/PROG/WD/rhs"
    , "m0/saf0/SAF/WD/lhs"
    , "m0/saf0/SAF/WD/rhs"
    , "m0/step/FIS/pc@prime"
    , "m0/step/SAF/saf0"
    , "m0/step/WD/ACT/a0"
    , "m0/tr0/TR/WD"
    , "m0/tr0/TR/WFIS/p/p@prime"
    , "m0/tr0/TR/step/NEG"
    , ""
    ]
