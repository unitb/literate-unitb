{-# LANGUAGE OverloadedStrings #-}
module Main where

import qualified Reactive as R
import Document.Document as Doc ( syntaxSummary )
import Document.Phase.Expressions as PExp
import Document.MachineSpec as MSpec hiding (main)
import Document.Tests.Cubes   as Cubes
import Document.Tests.GarbageCollector  as GC
import Document.Tests.Lambdas as Lam
import Document.Tests.LockFreeDeque as Deq
import Document.Tests.Parser as Parser
import Document.Tests.Phase  as Sync
import Document.Tests.Puzzle  as Puzz
import Document.Tests.SmallMachine  as SM
import Document.Tests.Suite 
import Document.Tests.TerminationDetection  as Term
import Document.Tests.TrainStation  as TS
import Document.Tests.TrainStationRefinement  as TSRef
import Document.Tests.TrainStationSets  as TSS
import Document.Phase.Types
import Logic.TestGenericity as Gen
import Z3.Test as Z3
import Document.Phase.Test as Ph
import Control.Lens
import Document.Test as Doc
import Utilities.Test as Ut
import UnitB.Test as UB
import Logic.Expr
--import Logic.Expr.PrettyPrint
--import Logic.Proof
---- import UnitB.Test as UB
----import Latex.Parser
import qualified Latex.Test_Latex_Parser as Tex
---- import qualified Document.Test as DOC
---- import qualified Utilities.Format as FMT
import qualified Utilities.Test as UT
import qualified Code.Test as Code
import qualified Documentation.Test as Sum


import Tests.UnitTest

--import Language.Haskell.TH
--import Language.Haskell.TH.Syntax

import System.Process
import System.TimeIt
import System.Timeout

import Utilities.BipartiteGraph
import qualified Utilities.Lines as Lines
import Utilities.Map as M

import Test.QuickCheck

import Text.Printf


main :: IO ()
main = timeIt $ do
    system "rm actual-*.txt"
    system "rm expected-*.txt"
    system "rm po-*.z3"
    system "rm log*.z3"
    writeFile "syntax.txt" $ unlines syntaxSummary
    return R.main
    return $ run_test_cases Deq.test_case
    --x <- proof_obligation Deq.path4 "m1/LIVE/m1:prog3/ensure/TR/m0:pop:left:empty/NEG" 1
    x <- Ph.case5
    let y = Ph.result5
    z <- Ph.case4
    let m1 = MId [tex|m1|]
        evt = "ae1a"
    print $ x & traverse %~ view (mchTable.ix m1.pEventRef.to leftMap.ix evt.eActions.to M.keys)
    print $ y & traverse %~ view (mchTable.ix m1.pEventRef.to leftMap.ix evt.eActions.to M.keys)
    print $ z & traverse %~ view (mchTable.ix m1.pEventRef.to leftMap.ix evt.eActions.to M.keys)
    return $ run_test_cases Term.test_case
    return $ run_test_cases Puzz.test_case
    return $ run_test_cases Ph.test_case
    return $ run_test_cases Ut.test_case
    return $ run_test_cases Z3.test_case
    ----print =<< Ph.case7
    return $ run_test_cases Code.test_case
    return $ run_test_cases Sum.test_case
    return $ run_test_cases Gen.test_case
    return verify
    return $ print =<< run_test_cases Doc.check_axioms
    return $ print =<< PExp.check_props
    return $ run_test_cases SM.test_case
    return $ do
        c4 <- Lam.case4
        printf "size: %s\n" (show $ 
                M.intersectionWith (==) <$> (c4) <*> (Lam.result4)) 
-- ******
    return $ run_test_cases Lam.test_case
-- ******
    return $ run_test_cases Cubes.test_case
    return $ run_test_cases Sync.test_case
    return $ run_test_cases Puzz.test_case
    return $ quickCheck MSpec.prop_expr_parser
    return $ print =<< MSpec.run_spec
    return $ print =<< run_test_cases check_axioms
    return $ run_test_cases Gen.test_case
    timeout (60 * 1000000) $ do
        return $ run_test_cases UB.test_case
    return $ print =<< Lines.run_tests
    run_test_cases TS.test_case
    return $ run_test_cases TSS.test_case
    return $ run_test_cases TSRef.test_case
    return $ run_test_cases UT.test_case
    return $ run_test_cases Tex.test_case
    return $ run_test_cases GC.test_case
    return $ run_test_cases Parser.test_case
    return $ run_test_cases Z3.test_case
    return $ run_test_cases Doc.test_case
    return ()
