{-# LANGUAGE OverloadedStrings #-}
module Main where

import Document.Document as Doc ( syntaxSummary )
import Document.Phase.Expressions as PExp
import Document.MachineSpec as MSpec
import Document.Tests.Cubes   as Cubes
import Document.Tests.Definitions  as Def
import Document.Tests.GarbageCollector  as GC
import Document.Tests.Lambdas as Lam
import Document.Tests.LockFreeDeque as Deq
import Document.Tests.Parser  as Parser
import Document.Tests.Phase   as Sync
import Document.Tests.Puzzle  as Puzz
import Document.Tests.SmallMachine  as SM
import Document.Tests.Suite hiding (proof_obligation)
import Document.Tests.TerminationDetection  as Term
import Document.Tests.TrainStation     as TS
import Document.Tests.TrainStationRefinement  as TSRef
import Document.Tests.TrainStationSets as TSS
import Logic.Expr
import Logic.Test as Logic
import Z3.Test as Z3
import Document.Phase.Test as Ph
import Document.Test as Doc
import Utilities.Test as Ut
import UnitB.Test as UB
-- import UnitB.UnitB as UB hiding (raw_proof_obligation)
-- import Logic.Expr.PrettyPrint
-- import Logic.Names
import Logic.Names.Packaged ()
-- import Logic.Proof
-- import UnitB.Test as UB
--import Latex.Parser
import qualified Latex.Test as Tex
-- import qualified Document.Test as DOC
import qualified Utilities.Test as UT
import qualified Code.Test as Code
import qualified Documentation.Test as Sum

import Test.UnitTest

-- import Language.Haskell.TH
-- import Language.Haskell.TH.Syntax

import Control.Concurrent
import Control.Monad

-- import System.FilePath.Lens

import System.Process
-- import System.Timeout

-- import qualified Utilities.Lines as Lines
import Utilities.TimeIt
-- import Utilities.Timeout
-- import Utilities.Map

import Test.QuickCheck hiding (label)
import Test.QuickCheck.Report

import Document.ExprScope as EScope

main :: IO ()
main = timeIt $ void $ do
    setNumCapabilities 8
    system "rm actual-*.txt"
    system "rm expected-*.txt"
    system "rm po-*.z3"
    system "rm log*.z3"
    writeFile "syntax.txt" $ unlines syntaxSummary
    putStrLn $ nameType
    return $ edit =<< raw_proof_obligation Deq.path1 "m0/INIT/FIS/q/p" 0
    return $ printQuickCheckResult MSpec.run_spec
    return $ quickCheck MSpec.prop_expr_parser
    return $ run_test_cases Deq.test_case
    -- timeIt $ do
    --     p <- parse_system path
    --     evaluate $ force p
    -- x <- proof_obligation Deq.path4 "m1/LIVE/m1:prog3/ensure/TR/m0:pop:left:empty/NEG" 1
    return $ run_test_cases Term.test_case
    return $ run_test_cases Ph.test_case
    return $ run_test_cases Ut.test_case
    return $ run_test_cases Z3.test_case
    ----print =<< Ph.case7
    return $ run_test_cases Code.test_case
    return $ run_test_cases Sum.test_case
    return $ print =<< run_test_cases Doc.check_axioms
    return $ printQuickCheckResult PExp.check_props
    return $ run_test_cases SM.test_case
-- ******
    return $ run_test_cases Lam.test_case
-- ******
    return $ run_test_cases Cubes.test_case
    return $ run_test_cases Sync.test_case
    return $ run_test_cases Puzz.test_case
    return $ quickCheck MSpec.prop_expr_parser
    return $ printQuickCheckResult MSpec.run_spec
    return $ print =<< run_test_cases check_axioms
    return $ run_test_cases Def.test_case
    return $ run_test_cases Logic.test_case
    -- timeout (60 * 1000000) $ do
    return $ run_test_cases UB.test_case
    -- return $ print =<< Lines.run_tests
    return $ run_test_cases TS.test_case
    return $ run_test_cases TSS.test_case
    return $ run_test_cases TSRef.test_case
    return $ run_test_cases UT.test_case
    return $ run_test_cases Tex.test_case
    return $ run_test_cases GC.test_case
    return $ run_test_cases Parser.test_case
    return $ run_test_cases Z3.test_case
    return $ run_test_cases Doc.test_case
    return $ printQuickCheckResult EScope.run_tests
    return ()
