module Document.Tests.LockFreeDeque where

    -- Modules
import Document.Document

import Logic.Label
import Logic.Sequent

import UnitB.PO

    -- Libraries
import Data.Map hiding ( map )

import Utilities.Syntactic

import Tests.UnitTest

test_case :: TestCase
test_case = Case "Specification and refinement of a lock-free algorithm" test True

test :: IO Bool
test = test_cases
            [ (POCase "test 0, verification, specification with intervals" 
                (verify path0) result0)
            , (POCase "test 1, verification, failed proof with intervals" 
                (verify path1) result1)
            , (StringCase "test 2, error message name clash in guards" 
                case2 result2)
            , (POCase "test 3, verification, looking up function outside of domain" 
                (verify path3) result3)
            ]            

result0 :: String
result0 = unlines
    [ "  o  m0/INIT/FIS/emp"
    , "  o  m0/INIT/FIS/p"
    , "  o  m0/INIT/FIS/q"
    , "  o  m0/INIT/FIS/qe"
    , "  o  m0/INIT/FIS/res"
    , "  o  m0/INIT/INV/m0:inv0"
    , "  o  m0/INIT/INV/m0:inv1"
    , "  o  m0/INIT/WD"
    , "  o  m0/INV/WD"
    , "  o  m0/m0:pop:left/FIS/emp@prime"
    , "  o  m0/m0:pop:left/FIS/p@prime"
    , "  o  m0/m0:pop:left/FIS/q@prime"
    , "  o  m0/m0:pop:left/FIS/qe@prime"
    , "  o  m0/m0:pop:left/FIS/res@prime"
    , "  o  m0/m0:pop:left/INV/m0:inv0"
    , "  o  m0/m0:pop:left/INV/m0:inv1"
    , "  o  m0/m0:pop:left/SCH"
    , "  o  m0/m0:pop:left/WD/ACT/m0:act0"
    , "  o  m0/m0:pop:left/WD/ACT/m0:act1"
    , "  o  m0/m0:pop:left/WD/ACT/m0:act2"
    , "  o  m0/m0:pop:left/WD/ACT/m0:act3"
    , "  o  m0/m0:pop:left/WD/ACT/m0:act4"
    , "  o  m0/m0:pop:left/WD/C_SCH"
    , "  o  m0/m0:pop:left/WD/F_SCH"
    , "  o  m0/m0:pop:left/WD/GRD"
    , "  o  m0/m0:pop:right/FIS/emp@prime"
    , "  o  m0/m0:pop:right/FIS/p@prime"
    , "  o  m0/m0:pop:right/FIS/q@prime"
    , "  o  m0/m0:pop:right/FIS/qe@prime"
    , "  o  m0/m0:pop:right/FIS/res@prime"
    , "  o  m0/m0:pop:right/INV/m0:inv0"
    , "  o  m0/m0:pop:right/INV/m0:inv1"
    , "  o  m0/m0:pop:right/SCH"
    , "  o  m0/m0:pop:right/WD/ACT/m0:act0"
    , "  o  m0/m0:pop:right/WD/ACT/m0:act1"
    , "  o  m0/m0:pop:right/WD/ACT/m0:act2"
    , "  o  m0/m0:pop:right/WD/ACT/m0:act3"
    , "  o  m0/m0:pop:right/WD/ACT/m0:act4"
    , "  o  m0/m0:pop:right/WD/C_SCH"
    , "  o  m0/m0:pop:right/WD/F_SCH"
    , "  o  m0/m0:pop:right/WD/GRD"
    , "  o  m0/m0:push:left/FIS/emp@prime"
    , "  o  m0/m0:push:left/FIS/p@prime"
    , "  o  m0/m0:push:left/FIS/q@prime"
    , "  o  m0/m0:push:left/FIS/qe@prime"
    , "  o  m0/m0:push:left/FIS/res@prime"
    , "  o  m0/m0:push:left/INV/m0:inv0"
    , "  o  m0/m0:push:left/INV/m0:inv1"
    , "  o  m0/m0:push:left/SCH"
    , "  o  m0/m0:push:left/WD/ACT/m0:act0"
    , "  o  m0/m0:push:left/WD/ACT/m0:act1"
    , "  o  m0/m0:push:left/WD/ACT/m0:act2"
    , "  o  m0/m0:push:left/WD/ACT/m0:act3"
    , "  o  m0/m0:push:left/WD/ACT/m0:act4"
    , "  o  m0/m0:push:left/WD/C_SCH"
    , "  o  m0/m0:push:left/WD/F_SCH"
    , "  o  m0/m0:push:left/WD/GRD"
    , "  o  m0/m0:push:right/FIS/emp@prime"
    , "  o  m0/m0:push:right/FIS/p@prime"
    , "  o  m0/m0:push:right/FIS/q@prime"
    , "  o  m0/m0:push:right/FIS/qe@prime"
    , "  o  m0/m0:push:right/FIS/res@prime"
    , "  o  m0/m0:push:right/INV/m0:inv0"
    , "  o  m0/m0:push:right/INV/m0:inv1"
    , "  o  m0/m0:push:right/SCH"
    , "  o  m0/m0:push:right/WD/ACT/m0:act0"
    , "  o  m0/m0:push:right/WD/ACT/m0:act1"
    , "  o  m0/m0:push:right/WD/ACT/m0:act2"
    , "  o  m0/m0:push:right/WD/ACT/m0:act3"
    , "  o  m0/m0:push:right/WD/ACT/m0:act4"
    , "  o  m0/m0:push:right/WD/C_SCH"
    , "  o  m0/m0:push:right/WD/F_SCH"
    , "  o  m0/m0:push:right/WD/GRD"
    , "passed 73 / 73"
    ]
path0 :: String
path0 = "tests/lock-free deque/main.tex"

path1 :: String
path1 = "tests/lock-free deque/main2.tex"

result1 :: String
result1 = unlines
    [ "  o  m0/INIT/FIS/p"
    , "  o  m0/INIT/FIS/q"
    , "  o  m0/INIT/FIS/qe"
    , "  o  m0/INIT/INV/m0:inv0"
    , "  o  m0/INIT/WD"
    , "  o  m0/INV/WD"
    , "  o  m0/m0:pop:left/FIS/p@prime"
    , "  o  m0/m0:pop:left/FIS/q@prime"
    , "  o  m0/m0:pop:left/FIS/qe@prime"
    , "  o  m0/m0:pop:left/INV/m0:inv0"
    , "  o  m0/m0:pop:left/SCH"
    , "  o  m0/m0:pop:left/WD/ACT/m0:act0"
    , "  o  m0/m0:pop:left/WD/ACT/m0:act1"
    , "  o  m0/m0:pop:left/WD/ACT/m0:act2"
    , "  o  m0/m0:pop:left/WD/C_SCH"
    , "  o  m0/m0:pop:left/WD/F_SCH"
    , "  o  m0/m0:pop:left/WD/GRD"
    , "  o  m0/m0:pop:right/FIS/p@prime"
    , "  o  m0/m0:pop:right/FIS/q@prime"
    , "  o  m0/m0:pop:right/FIS/qe@prime"
    , "  o  m0/m0:pop:right/INV/m0:inv0"
    , "  o  m0/m0:pop:right/SCH"
    , "  o  m0/m0:pop:right/WD/ACT/m0:act0"
    , "  o  m0/m0:pop:right/WD/ACT/m0:act1"
    , "  o  m0/m0:pop:right/WD/ACT/m0:act2"
    , "  o  m0/m0:pop:right/WD/C_SCH"
    , "  o  m0/m0:pop:right/WD/F_SCH"
    , "  o  m0/m0:pop:right/WD/GRD"
    , "  o  m0/m0:push:left/FIS/p@prime"
    , "  o  m0/m0:push:left/FIS/q@prime"
    , "  o  m0/m0:push:left/FIS/qe@prime"
    , " xxx m0/m0:push:left/INV/m0:inv0"
    , "  o  m0/m0:push:left/SCH"
    , "  o  m0/m0:push:left/WD/ACT/m0:act0"
    , "  o  m0/m0:push:left/WD/ACT/m0:act1"
    , "  o  m0/m0:push:left/WD/ACT/m0:act2"
    , "  o  m0/m0:push:left/WD/C_SCH"
    , "  o  m0/m0:push:left/WD/F_SCH"
    , "  o  m0/m0:push:left/WD/GRD"
    , "  o  m0/m0:push:right/FIS/p@prime"
    , "  o  m0/m0:push:right/FIS/q@prime"
    , "  o  m0/m0:push:right/FIS/qe@prime"
    , " xxx m0/m0:push:right/INV/m0:inv0"
    , "  o  m0/m0:push:right/SCH"
    , "  o  m0/m0:push:right/WD/ACT/m0:act0"
    , "  o  m0/m0:push:right/WD/ACT/m0:act1"
    , "  o  m0/m0:push:right/WD/ACT/m0:act2"
    , "  o  m0/m0:push:right/WD/C_SCH"
    , "  o  m0/m0:push:right/WD/F_SCH"
    , "  o  m0/m0:push:right/WD/GRD"
    , "passed 48 / 50"
    ]

path2 :: String
path2 = "tests/lock-free deque/main3.tex"

case2 :: IO String
case2 = do
        r <- parse_machine path2
        case r of
            Right _ -> do
                return "successful verification"
            Left xs -> return $ unlines $ map format_error xs


result2 :: String
result2 = unlines
        [ "error (44,3): 'm0:inv0' is already used for another invariant" 
        , "error (87,3): 'm0:grd0' is already used for another guard" ]

path3 :: String
path3 = "tests/lock-free deque/main4.tex"

result3 :: String
result3 = unlines
    [ "  o  m0/INIT/FIS/p"
    , "  o  m0/INIT/FIS/q"
    , "  o  m0/INIT/FIS/qe"
    , "  o  m0/INIT/INV/m0:inv0"
    , "  o  m0/INIT/INV/m0:inv1"
    , "  o  m0/INIT/WD"
    , "  o  m0/INV/WD"
    , "  o  m0/m0:pop:left/FIS/p@prime"
    , "  o  m0/m0:pop:left/FIS/q@prime"
    , "  o  m0/m0:pop:left/FIS/qe@prime"
    , "  o  m0/m0:pop:left/INV/m0:inv0"
    , "  o  m0/m0:pop:left/INV/m0:inv1"
    , "  o  m0/m0:pop:left/SCH"
    , "  o  m0/m0:pop:left/WD/ACT/m0:act0"
    , "  o  m0/m0:pop:left/WD/ACT/m0:act1"
    , "  o  m0/m0:pop:left/WD/ACT/m0:act2"
    , "  o  m0/m0:pop:left/WD/C_SCH"
    , "  o  m0/m0:pop:left/WD/F_SCH"
    , " xxx m0/m0:pop:left/WD/GRD"
    , "  o  m0/m0:pop:right/FIS/p@prime"
    , "  o  m0/m0:pop:right/FIS/q@prime"
    , "  o  m0/m0:pop:right/FIS/qe@prime"
    , "  o  m0/m0:pop:right/INV/m0:inv0"
    , "  o  m0/m0:pop:right/INV/m0:inv1"
    , "  o  m0/m0:pop:right/SCH"
    , "  o  m0/m0:pop:right/WD/ACT/m0:act0"
    , "  o  m0/m0:pop:right/WD/ACT/m0:act1"
    , "  o  m0/m0:pop:right/WD/ACT/m0:act2"
    , "  o  m0/m0:pop:right/WD/C_SCH"
    , "  o  m0/m0:pop:right/WD/F_SCH"
    , "  o  m0/m0:pop:right/WD/GRD"
    , "  o  m0/m0:push:left/FIS/p@prime"
    , "  o  m0/m0:push:left/FIS/q@prime"
    , "  o  m0/m0:push:left/FIS/qe@prime"
    , "  o  m0/m0:push:left/INV/m0:inv0"
    , "  o  m0/m0:push:left/INV/m0:inv1"
    , "  o  m0/m0:push:left/SCH"
    , "  o  m0/m0:push:left/WD/ACT/m0:act0"
    , "  o  m0/m0:push:left/WD/ACT/m0:act1"
    , "  o  m0/m0:push:left/WD/ACT/m0:act2"
    , "  o  m0/m0:push:left/WD/C_SCH"
    , "  o  m0/m0:push:left/WD/F_SCH"
    , "  o  m0/m0:push:left/WD/GRD"
    , "  o  m0/m0:push:right/FIS/p@prime"
    , "  o  m0/m0:push:right/FIS/q@prime"
    , "  o  m0/m0:push:right/FIS/qe@prime"
    , "  o  m0/m0:push:right/INV/m0:inv0"
    , "  o  m0/m0:push:right/INV/m0:inv1"
    , "  o  m0/m0:push:right/SCH"
    , "  o  m0/m0:push:right/WD/ACT/m0:act0"
    , "  o  m0/m0:push:right/WD/ACT/m0:act1"
    , "  o  m0/m0:push:right/WD/ACT/m0:act2"
    , "  o  m0/m0:push:right/WD/C_SCH"
    , "  o  m0/m0:push:right/WD/F_SCH"
    , " xxx m0/m0:push:right/WD/GRD"
    , "passed 53 / 55"
    ]

verify :: FilePath -> IO (String, Map Label Sequent)
verify path = do
    r <- list_file_obligations path
    case r of
        Right ms -> do
            let (m,pos) = ms !! 0
            (s,_,_) <- str_verify_machine m
            return (s, pos)
        x -> return (show x, empty)
