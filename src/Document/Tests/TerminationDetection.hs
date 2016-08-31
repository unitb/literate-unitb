module Document.Tests.TerminationDetection where

import Document.Tests.Suite

import Test.UnitTest

test_case :: TestCase
test_case = test_cases 
    "Termination Detection" 
    [ poCase "test0: verify m0" case0 result0 
    , poCase "test1: verify m1" case1 result1 
    , poCase "test2: verify m2" case2 result2 
    , poCase "test3: verify m3" case3 result3 
    , poCase "test4: quantified union" case4 result4 ]

path0 :: FilePath
path0 = [path|Tests/termination detection/main.tex|]

case0 :: IO POResult
case0 = verify path0 0

result0 :: String
result0 = unlines
    [ "  o  m0/INIT/INV/m0:inv0"
    , "  o  m0/activate/INV/m0:inv0"
    , "  o  m0/stop/INV/m0:inv0"
    , "passed 3 / 3"
    ]

case1 :: IO POResult
case1 = verify path0 1

result1 :: String
result1 = unlines
    [ "  o  m1/INIT/INV/m1:inv0"
    , "  o  m1/INV/WD"
    , "  o  m1/LIVE/m1:prog0/ensure/SAF/WD/lhs"
    , "  o  m1/LIVE/m1:prog0/ensure/TR/WD"
    , "  o  m1/LIVE/m1:prog0/ensure/TR/detect/EN"
    , "  o  m1/LIVE/m1:prog0/ensure/TR/detect/NEG"
    , "  o  m1/activate/INV/m1:inv0"
    , "  o  m1/activate/SAF/LIVE/m1:prog0/ensure"
    , "  o  m1/activate/SAF/m1:saf0"
    , "  o  m1/activate/SCH/q/p"
    , "  o  m1/activate/WD/GRD"
    , "  o  m1/detect/INV/m1:inv0"
    , "  o  m1/detect/SAF/LIVE/m1:prog0/ensure"
    , "  o  m1/detect/SAF/m1:saf0"
    , "  o  m1/detect/SCH/m1:grd0"
    , "  o  m1/detect/WD/C_SCH"
    , "  o  m1/detect/WD/GRD"
    , "  o  m1/m1:prog0/PROG/WD/lhs"
    , "  o  m1/m1:saf0/SAF/WD/lhs"
    , "  o  m1/stop/INV/m1:inv0"
    , "  o  m1/stop/SAF/LIVE/m1:prog0/ensure"
    , "  o  m1/stop/SAF/m1:saf0"
    , "passed 22 / 22"
    ]

case2 :: IO POResult
case2 = verify path0 2

result2 :: String
result2 = unlines
    [ "  o  m2/INIT/INV/m2:inv0"
    , "  o  m2/INV/WD"
    , "  o  m2/LIVE/m2:prog1/ensure/SAF/WD/lhs"
    , "  o  m2/LIVE/m2:prog1/ensure/SAF/WD/rhs"
    , "  o  m2/LIVE/m2:prog1/ensure/TR/WD"
    , "  o  m2/LIVE/m2:prog1/ensure/TR/WFIS/p/p@prime"
    , "  o  m2/LIVE/m2:prog1/ensure/TR/add/EN"
    , "  o  m2/LIVE/m2:prog1/ensure/TR/add/NEG"
    , "  o  m2/activate/INV/m2:inv0"
    , "  o  m2/activate/SAF/LIVE/m2:prog1/ensure"
    , "  o  m2/activate/SAF/m2:saf0"
    , "  o  m2/add/INV/m2:inv0"
    , "  o  m2/add/SAF/LIVE/m2:prog1/ensure"
    , "  o  m2/add/SAF/m2:saf0"
    , "  o  m2/add/SCH/m2:grd0"
    , "  o  m2/add/WD/C_SCH"
    , "  o  m2/add/WD/GRD"
    , "  o  m2/detect/C_SCH/delay/0/prog/m2:prog0/lhs"
    , "  o  m2/detect/C_SCH/delay/0/prog/m2:prog0/rhs/m2:sch0"
    , "  o  m2/detect/C_SCH/delay/0/saf/activate/SAF/detect"
    , "  o  m2/detect/C_SCH/delay/0/saf/add/SAF/detect"
    , "  o  m2/detect/C_SCH/delay/0/saf/stop/SAF/detect"
    , "  o  m2/detect/GRD/str/m1:sch0"
    , "  o  m2/detect/INV/m2:inv0"
    , "  o  m2/detect/SAF/LIVE/m2:prog1/ensure"
    , "  o  m2/detect/SAF/m2:saf0"
    , "  o  m2/detect/SCH/m1:grd0"
    , "  o  m2/detect/WD/GRD"
    , "  o  m2/m2:prog0/LIVE/induction/lhs"
    , "  o  m2/m2:prog0/LIVE/induction/rhs"
    , "  o  m2/m2:prog0/PROG/WD/lhs"
    , "  o  m2/m2:prog1/PROG/WD/lhs"
    , "  o  m2/m2:prog1/PROG/WD/rhs"
    , "  o  m2/stop/INV/m2:inv0"
    , "  o  m2/stop/SAF/LIVE/m2:prog1/ensure"
    , "  o  m2/stop/SAF/m2:saf0"
    , "passed 36 / 36"
    ]

case3 :: IO POResult
case3 = verify path0 3

result3 :: String
result3 = unlines
    [ "  o  m3/INIT/INV/m3:inv0"
    , "  o  m3/INIT/INV/m3:inv1"
    , "  o  m3/INV/WD"
    , "  o  m3/activate/INV/m3:inv0"
    , " xxx m3/activate/INV/m3:inv1"
    , "  o  m3/activate/WD/ACT/m3:act0"
    , "  o  m3/add/INV/m3:inv0"
    , "  o  m3/add/INV/m3:inv1/goal"
    , "  o  m3/add/INV/m3:inv1/hypotheses"
    , "  o  m3/add/INV/m3:inv1/relation"
    , "  o  m3/add/INV/m3:inv1/step 1"
    , "  o  m3/add/INV/m3:inv1/step 2"
    , "  o  m3/add/INV/m3:inv1/step 3"
    , "  o  m3/add/INV/m3:inv1/step 4"
    , "  o  m3/add/INV/m3:inv1/step 5"
    , "  o  m3/add/INV/m3:inv1/step 6"
    , "  o  m3/add/INV/m3:inv1/step 7"
    , " xxx m3/add/INV/m3:inv1/step 8"
    , "  o  m3/add/WD/ACT/m3:act0"
    , "  o  m3/add/WD/GRD"
    , "  o  m3/detect/INV/m3:inv0"
    , "  o  m3/detect/INV/m3:inv1"
    , "  o  m3/detect/WD/GRD"
    , "  o  m3/stop/INV/m3:inv0"
    , "  o  m3/stop/INV/m3:inv1"
    , "passed 23 / 25"
    ]

path1 :: FilePath
path1 = [path|Tests/termination detection/main.tex|]

case4 :: IO POResult
case4 = verify path1 3

result4 :: String
result4 = unlines
    [ "  o  m3/INIT/INV/m3:inv0"
    , "  o  m3/INIT/INV/m3:inv1"
    , "  o  m3/INV/WD"
    , "  o  m3/activate/INV/m3:inv0"
    , " xxx m3/activate/INV/m3:inv1"
    , "  o  m3/activate/WD/ACT/m3:act0"
    , "  o  m3/add/INV/m3:inv0"
    , "  o  m3/add/INV/m3:inv1/goal"
    , "  o  m3/add/INV/m3:inv1/hypotheses"
    , "  o  m3/add/INV/m3:inv1/relation"
    , "  o  m3/add/INV/m3:inv1/step 1"
    , "  o  m3/add/INV/m3:inv1/step 2"
    , "  o  m3/add/INV/m3:inv1/step 3"
    , "  o  m3/add/INV/m3:inv1/step 4"
    , "  o  m3/add/INV/m3:inv1/step 5"
    , "  o  m3/add/INV/m3:inv1/step 6"
    , "  o  m3/add/INV/m3:inv1/step 7"
    , " xxx m3/add/INV/m3:inv1/step 8"
    , "  o  m3/add/WD/ACT/m3:act0"
    , "  o  m3/add/WD/GRD"
    , "  o  m3/detect/INV/m3:inv0"
    , "  o  m3/detect/INV/m3:inv1"
    , "  o  m3/detect/WD/GRD"
    , "  o  m3/stop/INV/m3:inv0"
    , "  o  m3/stop/INV/m3:inv1"
    , "passed 23 / 25"
    ]
