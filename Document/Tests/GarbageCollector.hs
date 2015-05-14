module Document.Tests.GarbageCollector where

import Document.Tests.Suite

import Tests.UnitTest

test_case :: TestCase
test_case = test_cases 
    "Garbage collector" 
    [ POCase "test0: verify m0" case0 result0 
    , POCase "test1: verify m1" case1 result1 ]

path0 :: FilePath
path0 = "Tests/garbage collector/main.tex"

case0 :: IO POResult
case0 = verify path0 0

result0 :: String
result0 = unlines
    [ "  o  m0/INIT/FIS/free"
    , "  o  m0/INIT/FIS/live"
    , "  o  m0/INIT/INV/m0:inv0"
    , "  o  m0/INIT/INV/m0:inv1"
    , "  o  m0/INIT/INV/m0:inv2"
    , "  o  m0/INIT/WD"
    , "  o  m0/INIT/WWD"
    , "  o  m0/INV/WD"
    , "  o  m0/alloc/FIS/free@prime"
    , "  o  m0/alloc/FIS/live@prime"
    , "  o  m0/alloc/INV/m0:inv0"
    , "  o  m0/alloc/INV/m0:inv1"
    , "  o  m0/alloc/INV/m0:inv2"
    , "  o  m0/alloc/WD/ACT/m0:act0"
    , "  o  m0/alloc/WD/ACT/m0:act1"
    , "  o  m0/alloc/WD/C_SCH"
    , "  o  m0/alloc/WD/F_SCH"
    , "  o  m0/alloc/WD/GRD"
    , "  o  m0/alloc/WWD"
    , "  o  m0/free/FIS/free@prime"
    , "  o  m0/free/FIS/live@prime"
    , "  o  m0/free/INV/m0:inv0"
    , "  o  m0/free/INV/m0:inv1"
    , "  o  m0/free/INV/m0:inv2"
    , "  o  m0/free/SCH/p"
    , "  o  m0/free/WD/ACT/m0:act0"
    , "  o  m0/free/WD/ACT/m0:act1"
    , "  o  m0/free/WD/C_SCH"
    , "  o  m0/free/WD/F_SCH"
    , "  o  m0/free/WD/GRD"
    , "  o  m0/free/WWD"
    , "passed 31 / 31"
    ]

case1 :: IO POResult
case1 = verify path0 1

result1 :: String
result1 = unlines
    [ "  o  m1/INIT/FIS/free"
    , "  o  m1/INIT/FIS/live"
    , "  o  m1/INIT/WD"
    , "  o  m1/INIT/WWD"
    , "  o  m1/INV/WD"
    , "  o  m1/alloc/FIS/free@prime"
    , "  o  m1/alloc/FIS/live@prime"
    , "  o  m1/alloc/FIS/ptr@prime"
    , "  o  m1/alloc/WD/C_SCH"
    , "  o  m1/alloc/WD/F_SCH"
    , "  o  m1/alloc/WD/GRD"
    , "  o  m1/alloc/WWD"
    , "  o  m1/free/FIS/free@prime"
    , "  o  m1/free/FIS/live@prime"
    , "  o  m1/free/FIS/ptr@prime"
    , " xxx m1/free/SCH/p"
    , "  o  m1/free/WD/C_SCH"
    , "  o  m1/free/WD/F_SCH"
    , "  o  m1/free/WD/GRD"
    , "  o  m1/free/WWD"
    , "  o  m1/m1:prog0/PROG/WD/lhs"
    , "  o  m1/m1:prog0/PROG/WD/rhs"
    , "  o  m1/m1:prog0/REF/ensure/m1/SAF/WD/lhs"
    , "  o  m1/m1:prog0/REF/ensure/m1/SAF/WD/rhs"
    , "  o  m1/m1:prog0/REF/ensure/m1/TR/WD"
    , "  o  m1/m1:prog0/REF/ensure/m1/TR/free/EN"
    , "  o  m1/m1:prog0/REF/ensure/m1/TR/free/NEG"
    , "  o  m1/m1:prog0/REF/ensure/m1/alloc/SAF"
    , "  o  m1/m1:prog0/REF/ensure/m1/free/SAF"
    , "passed 28 / 29"
    ]

