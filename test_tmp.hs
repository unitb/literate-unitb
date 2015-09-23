{-# LANGUAGE OverloadedStrings #-}
module Main where

-- import Shelly

-- import Control.Exception
-- import Control.Monad

-- import Document.Tests.Suite
-- import Document.Tests.Puzzle
-- import Document.Tests.TrainStation
-- import Document.Tests.Lambdas
-- import Document.Tests.LockFreeDeque
import Document.Phase.Test
-- import UnitB.Test as UB
-- import qualified Latex.Test_Latex_Parser as LT
-- import qualified Z3.Test as ZT
-- import qualified Document.Test as DOC
-- import qualified Utilities.Format as FMT
-- import qualified Utilities.Test as UT
-- import qualified Code.Test as Code
-- import qualified Documentation.Test as Sum

import Tests.UnitTest

import System.Process

-- import Utilities.Trace

-- tests :: TestCase
-- tests = test_cases 
--     ""
--     [ TSets.test_case
--     ]

-- test_case :: TestCase
-- test_case = test_cases 
--         "Literate Unit-B Test Suite" 
--         [  DOC.test_case
--         ,  UB.test_case
--         ,  LT.test_case
--         ,  ZT.test_case
-- --        ,  FMT.test_case
--         ,  UT.test_case
--         ,  Code.test_case
--         ,  Sum.test_case
--         ]


main :: IO ()
main = do
    -- shelly $ do
    system "rm actual-*.txt"
    system "rm expected-*.txt"
    system "rm po-*.z3"
    system "rm log*.z3"
    -- traceM "foo"
    -- x <- liftM (fmap rnf) $ parse_machine 
    --     "tests/lock-free deque/main.tex"
        -- "tests/small_machine.tex"
    -- print $ leaves $ selectLeaf 4 tests 
    -- run_test_cases $ selectLeaf 4 tests
    -- let tests = drop 5 $ take 6 $ allLeaves test_case
    -- putStrLn $ nameOf $ head tests
    
    -- x0 <- proof_obligation path0 "m2/m0:leave/INV/m2:inv0/main goal/easy (362,30)" 2
    -- x1 <- proof_obligation path0 "m3/m0:leave/INV/m3:inv3" 3
    -- writeFile "po0.z3" x0
    -- writeFile "po1.z3" x1
    run_test_cases test_case
    -- run_test_cases `seq` case12
                -- 
    -- print x
    -- print 7
    return ()
