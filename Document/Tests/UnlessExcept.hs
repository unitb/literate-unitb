module Document.Tests.UnlessExcept where


import Document.Machine

import Logic.Label
import Logic.Sequent

import UnitB.PO

import Tests.UnitTest

import Data.Map

test_case :: TestCase
test_case = Case "Specification and refinement of a lock-free algorithm" test True

test :: IO Bool
test = test_cases
            [ (POCase "test 0, unless/except without indices" 
                (verify path0) result0)
            ]

path0 :: String
path0 = "Tests/unless-except.tex"

result0 :: String
result0 = unlines
    [ "  o  m0/INIT/FIS/p"
    , "  o  m0/INIT/WD"
    , "  o  m0/INV/WD"
    , "  o  m0/evt0/FIS/p@prime"
    , "  o  m0/evt0/SAF/saf0"
    , "  o  m0/evt0/SCH"
    , "  o  m0/evt0/WD/ACT/m0:act0"
    , "  o  m0/evt0/WD/C_SCH"
    , "  o  m0/evt0/WD/F_SCH"
    , "  o  m0/evt0/WD/GRD"
    , "  o  m0/evt1/FIS/p@prime"
    , "  o  m0/evt1/SAF/saf0"
    , "  o  m0/evt1/SCH"
    , "  o  m0/evt1/WD/ACT/m0:act0"
    , "  o  m0/evt1/WD/C_SCH"
    , "  o  m0/evt1/WD/F_SCH"
    , "  o  m0/evt1/WD/GRD"
    , "  o  m0/saf0/SAF/WD/lhs"
    , "  o  m0/saf0/SAF/WD/rhs"
    , "passed 18 / 19"
    ]

verify :: FilePath -> IO (String, Map Label Sequent)
verify path = do
    r <- list_file_obligations path
    case r of
        Right [(m,pos)] -> do
            (s,_,_) <- str_verify_machine m
            return (s, pos)
        x -> return (show x, empty)
