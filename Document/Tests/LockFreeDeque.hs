module Document.Tests.LockFreeDeque where

    -- Modules
import Document.Document

import Logic.Label
import Logic.Sequent

import UnitB.PO

    -- Libraries
import Data.Map hiding ( map )

import Tests.UnitTest

test_case :: TestCase
test_case = Case "lambda expressions in the cube example" test True

test :: IO Bool
test = test_cases
            [ (POCase "test 0, verification, lambda vs empty-fun" 
                (verify path0) result0)
            , (POCase "test 1, verification, lambda vs ovl, mk-fun" 
                (verify path1) result1)
            ]            

result0 :: String
result0 = unlines
        [ "  o  m0/INIT/FIS/p"
        , "  o  m0/INIT/FIS/q"
        , "  o  m0/INIT/FIS/qe"
        , "  o  m0/INIT/INV/m0:inv0"
        , "  o  m0/INIT/INV/m0:inv1"
        , "  o  m0/m0:pop:left/FIS/p@prime"
        , "  o  m0/m0:pop:left/FIS/q@prime"
        , "  o  m0/m0:pop:left/FIS/qe@prime"
        , "  o  m0/m0:pop:left/INV/m0:inv0"
        , "  o  m0/m0:pop:left/INV/m0:inv1"
        , "  o  m0/m0:pop:left/SCH"
        , "  o  m0/m0:pop:right/FIS/p@prime"
        , "  o  m0/m0:pop:right/FIS/q@prime"
        , "  o  m0/m0:pop:right/FIS/qe@prime"
        , "  o  m0/m0:pop:right/INV/m0:inv0"
        , "  o  m0/m0:pop:right/INV/m0:inv1"
        , "  o  m0/m0:pop:right/SCH"
        , "  o  m0/m0:push:left/FIS/p@prime"
        , "  o  m0/m0:push:left/FIS/q@prime"
        , "  o  m0/m0:push:left/FIS/qe@prime"
        , "  o  m0/m0:push:left/INV/m0:inv0"
        , "  o  m0/m0:push:left/INV/m0:inv1"
        , "  o  m0/m0:push:left/SCH"
        , "  o  m0/m0:push:right/FIS/p@prime"
        , "  o  m0/m0:push:right/FIS/q@prime"
        , "  o  m0/m0:push:right/FIS/qe@prime"
        , "  o  m0/m0:push:right/INV/m0:inv0"
        , "  o  m0/m0:push:right/INV/m0:inv1"
        , "  o  m0/m0:push:right/SCH"
        , "passed 29 / 29"
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
        , "  o  m0/m0:pop:left/FIS/p@prime"
        , "  o  m0/m0:pop:left/FIS/q@prime"
        , "  o  m0/m0:pop:left/FIS/qe@prime"
        , "  o  m0/m0:pop:left/INV/m0:inv0"
        , "  o  m0/m0:pop:left/SCH"
        , "  o  m0/m0:pop:right/FIS/p@prime"
        , "  o  m0/m0:pop:right/FIS/q@prime"
        , "  o  m0/m0:pop:right/FIS/qe@prime"
        , "  o  m0/m0:pop:right/INV/m0:inv0"
        , "  o  m0/m0:pop:right/SCH"
        , "  o  m0/m0:push:left/FIS/p@prime"
        , "  o  m0/m0:push:left/FIS/q@prime"
        , "  o  m0/m0:push:left/FIS/qe@prime"
        , " xxx m0/m0:push:left/INV/m0:inv0"
        , "  o  m0/m0:push:left/SCH"
        , "  o  m0/m0:push:right/FIS/p@prime"
        , "  o  m0/m0:push:right/FIS/q@prime"
        , "  o  m0/m0:push:right/FIS/qe@prime"
        , " xxx m0/m0:push:right/INV/m0:inv0"
        , "  o  m0/m0:push:right/SCH"
        , "passed 22 / 24"
        ]



verify :: FilePath -> IO (String, Map Label Sequent)
verify path = do
    r <- list_file_obligations path
    case r of
        Right [(m,pos)] -> do
            (s,_,_) <- str_verify_machine m
            return (s, pos)
        x -> return (show x, empty)
