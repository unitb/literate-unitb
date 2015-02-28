module Document.Tests.Puzzle where

    -- Modules
import Document.Tests.Suite

import Logic.Expr
import Logic.Proof

    -- Library
import Data.Map

import Tests.UnitTest

test_case :: TestCase
test_case = test_cases 
        "The king and his advisors puzzle"
        [ POCase "puzzle, m0" case0 result0
        , POCase "puzzle, m1" case1 result1
        ]

path0 :: FilePath
path0 = "Tests/puzzle/puzzle.tex"

case0 :: IO (String, Map Label Sequent)
case0 = verify path0 0

result0 :: String
result0 = unlines
    [ "  o  m0/INIT/FIS/b"
    , "  o  m0/INIT/WD"
    , "  o  m0/INV/WD"
    , "  o  m0/prog0/PROG/WD/lhs"
    , "  o  m0/prog0/PROG/WD/rhs"
    , "  o  m0/prog0/REF/ensure/m0/TR/term/EN"
    , "  o  m0/prog0/REF/ensure/m0/TR/term/NEG"
    , "  o  m0/prog0/REF/ensure/m0/term/SAF"
    , "  o  m0/term/FIS/b@prime"
    , "  o  m0/term/SCH"
    , "  o  m0/term/SCH/m0/0/REF/weaken"
    , "  o  m0/term/WD/ACT/act0"
    , "  o  m0/term/WD/C_SCH"
    , "  o  m0/term/WD/F_SCH"
    , "  o  m0/term/WD/GRD"
    , "passed 15 / 15"
    ]

case1 :: IO (String, Map Label Sequent)
case1 = verify path0 1

result1 :: String
result1 = unlines
    [ "  o  m1/INIT/FIS/b"
    , "  o  m1/INIT/INV/inv0"
    , "  o  m1/INIT/WD"
    , "  o  m1/INV/WD"
    , "  o  m1/term/FIS/b@prime"
    , "  o  m1/term/FIS/vs@prime"
    , "  o  m1/term/INV/inv0"
    , " xxx m1/term/SCH"
    , "  o  m1/term/WD/C_SCH"
    , "  o  m1/term/WD/F_SCH"
    , "  o  m1/term/WD/GRD"
    , "passed 10 / 11"
    ]
