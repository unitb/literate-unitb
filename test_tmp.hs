{-# LANGUAGE OverloadedStrings, QuasiQuotes #-}
module Main where

-- import Shelly

--import Control.Lens
--import Data.Either.Combinators
--import Utilities.Syntactic

-- import Document.Tests.Suite
import Document.Tests.Puzzle  as Puzz
import Document.Tests.Cubes   as Cubes
import Document.Tests.Lambdas as Lam
import Document.Tests.SmallMachine  as SM
import Document.Tests.GarbageCollector  as GC
import Document.Tests.TerminationDetection  as Term
import Document.Tests.TrainStation  as TS
import Document.Tests.TrainStationSets  as TSS
import Document.Tests.TrainStationRefinement  as TSRef
import Document.Tests.LockFreeDeque as Deq
import Document.Tests.Suite 
import Z3.Test as Z3
import Document.Phase.Test as Ph
import Document.Test as Doc
import Utilities.Test as Ut
import UnitB.Test as UB
--import Logic.Expr.QuasiQuote
-- import UnitB.Test as UB
--import Latex.Parser
import qualified Latex.Test_Latex_Parser as Tex
-- import qualified Z3.Test as ZT
-- import qualified Document.Test as DOC
-- import qualified Utilities.Format as FMT
-- import qualified Utilities.Test as UT
import qualified Code.Test as Code
import qualified Documentation.Test as Sum

import Tests.UnitTest
--import Test.QuickCheck

--import Language.Haskell.TH
--import Language.Haskell.TH.Syntax

import System.Process
import System.TimeIt

import Utilities.Lines as Lines

--import Utilities.Instances ()

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
main = timeIt $ do
    -- shelly $ do
    system "rm actual-*.txt"
    system "rm expected-*.txt"
    system "rm po-*.z3"
    system "rm log*.z3"
    --print $ used_var $ asExpr x
    --let longestPrefix xs ys = length $ takeWhile id $ zipWith (==) xs ys
    --run_test_cases $ test_cases "all" 
    --    [ Deq.test_case
    --    , Puzz.test_case
    --    , Ph.test_case
    --    , TS.test_case
    --    , SM.test_case
    --    , Lam.test_case
    --    , Cubes.test_case
    --    , Puzz.test_case
    --    , Tex.test_case
    --    , UB.test_case 
    --    ]
    return $ run_test_cases Deq.test_case
    return $ run_test_cases Term.test_case
    return $ run_test_cases Puzz.test_case
    return $ run_test_cases Ph.test_case
    return $ run_test_cases Ut.test_case
    return $ run_test_cases Z3.test_case
    --print =<< Ph.case7
    return $ run_test_cases Code.test_case
    return $ run_test_cases Sum.test_case
    return verify
    return $ run_test_cases SM.test_case
    return $ run_test_cases Lam.test_case
    return $ run_test_cases Cubes.test_case
    return $ run_test_cases Puzz.test_case
    return $ run_test_cases UB.test_case
    return $ print =<< Lines.run_tests
    return $ run_test_cases TS.test_case
    return $ run_test_cases TSS.test_case
    return $ run_test_cases TSRef.test_case
    return $ run_test_cases Tex.test_case
    return $ run_test_cases GC.test_case
    return $ run_test_cases Doc.test_case
    return ()
