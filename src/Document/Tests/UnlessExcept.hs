module Document.Tests.UnlessExcept where

    -- Modules
import Document.Tests.Suite

import Tests.UnitTest

test_case :: TestCase
test_case = test

test :: TestCase
test = test_cases
            "Unless / except clause"
            [ (POCase "test 0, unless/except without indices" 
                (verify path0 0) result0)
            , (POCase "test 1, unless/except with indices and free variables" 
                (verify path0 1) result1)
            ]

path0 :: String
path0 = "Tests/unless-except.tex"

result0 :: String
result0 = unlines
    [ "  o  m0/INIT/WD"
    , "  o  m0/INIT/WWD"
    , "  o  m0/INV/WD"
    , "  o  m0/evt0/FIS/p@prime"
    , " xxx m0/evt0/SAF/saf1"
    , "  o  m0/evt0/WD/ACT/m0:act0"
    , "  o  m0/evt0/WD/C_SCH"
    , "  o  m0/evt0/WD/F_SCH"
    , "  o  m0/evt0/WD/GRD"
    , "  o  m0/evt0/WWD"
    , "  o  m0/evt1/FIS/p@prime"
    , "  o  m0/evt1/SAF/saf1"
    , "  o  m0/evt1/WD/ACT/m0:act0"
    , "  o  m0/evt1/WD/C_SCH"
    , "  o  m0/evt1/WD/F_SCH"
    , "  o  m0/evt1/WD/GRD"
    , "  o  m0/evt1/WWD"
    , "  o  m0/saf1/SAF/WD/lhs"
    , "  o  m0/saf1/SAF/WD/rhs"
    , "passed 18 / 19"
    ]

result1 :: String
result1 = unlines
    [ "  o  m1/INIT/WD"
    , "  o  m1/INIT/WWD"
    , "  o  m1/INV/WD"
    , "  o  m1/evt0/FIS/f@prime"
    , " xxx m1/evt0/SAF/saf1"
    , " xxx m1/evt0/WD/ACT/m0:act0"
    , "  o  m1/evt0/WD/C_SCH"
    , "  o  m1/evt0/WD/F_SCH"
    , "  o  m1/evt0/WD/GRD"
    , "  o  m1/evt0/WWD"
    , "  o  m1/evt1/FIS/f@prime"
    , "  o  m1/evt1/SAF/saf1"
    , " xxx m1/evt1/WD/ACT/m0:act0"
    , "  o  m1/evt1/WD/C_SCH"
    , "  o  m1/evt1/WD/F_SCH"
    , "  o  m1/evt1/WD/GRD"
    , "  o  m1/evt1/WWD"
    , " xxx m1/saf1/SAF/WD/lhs"
    , "  o  m1/saf1/SAF/WD/rhs"
    , "passed 15 / 19"
    ]
