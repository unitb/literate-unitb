{-# LANGUAGE OverloadedStrings #-}
module Main where

import qualified Reactive as R
import qualified Reactive.Banana.Property as R
import Document.Document as Doc ( syntaxSummary )
import Document.Document as Doc ( parse_system )
import Document.Phase.Expressions as PExp
import Document.MachineSpec as MSpec
import Document.Tests.Cubes   as Cubes
import Document.Tests.GarbageCollector  as GC
import Document.Tests.Lambdas as Lam
import Document.Tests.LockFreeDeque as Deq
import Document.Tests.Parser as Parser
import Document.Tests.Phase  as Sync
import Document.Tests.Puzzle  as Puzz
import Document.Tests.SmallMachine  as SM
import Document.Tests.Suite hiding (proof_obligation)
import Document.Tests.TerminationDetection  as Term
import Document.Tests.TrainStation  as TS
import Document.Tests.TrainStationRefinement  as TSRef
import Document.Tests.TrainStationSets  as TSS
import Logic.Expr
import Logic.TestGenericity as Gen
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
import Interactive.Serialize

import Test.UnitTest

-- import Language.Haskell.TH
-- import Language.Haskell.TH.Syntax

import Control.Concurrent
import Control.DeepSeq
import Control.Exception
-- import Control.Lens

import Data.Functor

-- import System.FilePath.Lens

import Reactive.Banana.Test as RB
import System.Process
-- import System.Timeout

-- import qualified Utilities.Lines as Lines
-- import Data.Map.Class as M
import Utilities.FileFormat
import Utilities.TimeIt
-- import Utilities.Timeout
-- import Utilities.Table

import Test.QuickCheck hiding (label)

-- import Text.Printf

    -- timeout 5000000 $ 
main :: IO ()
main = timeIt $ void $ do
    setNumCapabilities 8
    system "rm actual-*.txt"
    system "rm expected-*.txt"
    system "rm po-*.z3"
    system "rm log*.z3"
    writeFile "syntax.txt" $ unlines syntaxSummary
    putStrLn $ nameType
    return R.main
    let 
        path   = "/Users/Simon/Dropbox/Qualifying Exam/simon/chapters/models/lock-free-deque.tex"
        state' = "/Users/Simon/Dropbox/Qualifying Exam/simon/chapters/models/lock-free-deque-seq.tex.state"
        state  = "/Users/Simon/Dropbox/Qualifying Exam/simon/chapters/models/lock-free-deque-other.tex.state"
        -- state2 = state & basename.basename %~ (++ "-2")
    -- timeIt $ do
    --         -- writeFormat is extremely slow but the profiler seems to find readFormat slow
    --         -- attempts
    --         --   setNumCapabilities (made a difference but not a speedup)    
    --         --   inline traverseFileStruct (no difference)
    --         --   changed HashMap for Map (made things worse)
    --         --   next: build with better profiling flags
    --     r <- readFormat seqFileFormat state
    --     print $ () <$ r
    --     evaluate $ force r
    --     print $ () <$ r
    --     putStrLn "READING FAILS"
    --     mapM_ (writeFormat seqFileFormat state2) r
    --     putStrLn "read / write"
    -- r <- timeIt $ do
    -- r <- readFormat seqFileFormat state
    -- print $ () <$ r
    --     -- evaluate $ force r
    --     -- print $ () <$ r
    --     -- putStrLn "read other format"
    --     -- return r
    -- timeIt $ do
    --     putStrLn "write format"
    --     mapM_ (writeFormat seqFileFormat state2) r
    --     putStrLn "read / write"
    -- timeIt $ do
    --     putStrLn "write format"
    --     mapM_ (writeFormat seqFileFormat state2) r
    --     putStrLn "read / write"
    Right p <- timeIt $ do 
        p <- parse_system path
        evaluate $ force p
        putStrLn "parse"
        return p
    timeIt $ do
    --     -- mapM_ (writeFormat seqFileFormat state2 . (\p -> p!.machines & traverse %~ proof_obligation)) p
        putStrLn "serialize"
        writeFormat systemFileFormat state (mempty,fmap getExpr <$> p)
    timeIt $ do
    --     -- mapM_ (writeFormat seqFileFormat state2 . (\p -> p!.machines & traverse %~ proof_obligation)) p
        putStrLn "serialize POs"
        writeFormat seqFileFormat state' (po_table p)

    -- print =<< find_errors TSRef.path3
    return $ edit =<< raw_proof_obligation Deq.path1 "m0/INIT/FIS/q/p" 0
    return $ print =<< MSpec.run_spec
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
    return $ print =<< PExp.check_props
    return $ run_test_cases SM.test_case
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
    return $ run_test_cases RB.test_case
    return ()
