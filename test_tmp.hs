{-# LANGUAGE OverloadedStrings, QuasiQuotes #-}
module Main where

-- import Shelly

--import Control.Applicative
--import Data.Either.Combinators
--import Utilities.Syntactic

-- import Document.Tests.Suite
import Document.Tests.Puzzle  as Puzz
import Document.Tests.Cubes   as Cubes
import Document.Tests.Lambdas as Lam
import Document.Tests.SmallMachine  as SM
import Document.Tests.TrainStation  as TS
import Document.Tests.LockFreeDeque as Deq
import Document.Phase.Test as Ph
import UnitB.Test as UB
--import Logic.Expr.QuasiQuote
-- import UnitB.Test as UB
--import Latex.Parser
import qualified Latex.Test_Latex_Parser as Tex
-- import qualified Z3.Test as ZT
-- import qualified Document.Test as DOC
-- import qualified Utilities.Format as FMT
-- import qualified Utilities.Test as UT
-- import qualified Code.Test as Code
-- import qualified Documentation.Test as Sum

import Tests.UnitTest
--import Test.QuickCheck

import System.Process

import Utilities.Lines as Lines

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
    -- run_test_cases `seq` case12
    --let c = ctx $ do
    --        decls %= M.union (symbol_table [Var "x" int,Var "y" int])
    --        expected_type .= Nothing
    --    x = c [expr| \qforall{x}{}{x \le y} |]
    --putStrLn $ prettyPrint x
    --print $ used_var $ asExpr x
    --let longestPrefix xs ys = length $ takeWhile id $ zipWith (==) xs ys
    run_test_cases $ test_cases "all" 
        [ Deq.test_case
        , Puzz.test_case
        , Ph.test_case
        , TS.test_case
        , SM.test_case
        , Lam.test_case
        , Cubes.test_case
        , Puzz.test_case
        , Tex.test_case
        , UB.test_case 
        ]
    return $ run_test_cases Deq.test_case
    return $ run_test_cases Puzz.test_case
    return $ run_test_cases Ph.test_case
    return $ run_test_cases TS.test_case
    --run_test_cases 
    --print =<< TS.case0
    --print TS.machine0
    return $ run_test_cases SM.test_case
    return $ run_test_cases Lam.test_case
    return $ run_test_cases Cubes.test_case
    return $ run_test_cases Puzz.test_case
    return $ run_test_cases Tex.test_case
    return $ run_test_cases UB.test_case
    --print =<< Tex.properties
    return $ print =<< Lines.run_tests
    putStrLn =<< readFile "actual-1.txt"

    --print =<< parse_latex_document Puzz.path21
    --let ln = longestPrefix (show $ tokens Tex.counter0) (show Tex.counter0')
    --printf "== Counter Example 0 ==\n"
    --printf "expected: %s\n" $ drop (ln - 90) $ show $ tokens Tex.counter0
    --printf "actual:   %s\n" $ drop (ln - 90) $ show Tex.counter0'
    --printf "flatten:  %s\n" $ show $ flatten Tex.counter0
    --printf "tree:     %s\n" $ show Tex.counter0
    --print $ tokens Tex.counter0 == Tex.counter0'
    --print ln
    --print $ length $ show Tex.counter0'
    --print $ length $ show Tex.counter0
    ----print Tex.prop_counter_example0
    --printf "== Counter Example 1 ==\n"
    --printf "expected: %s\n" $ drop (ln - 50) $ show $ Tex.counter1
    --printf "actual:   %s\n" $ drop (ln - 50) $ show $ Tex.counter1'
    --printf "flatten:  %s\n" $ show $ concatMap (lexeme.fst) Tex.counter1
    --print $ Tex.counter1 == Tex.counter1'
    ----print $ tokens Tex.counter1
    --print ln
    --print $ length $ show Tex.counter1'
    --print $ length $ show Tex.counter1
    --printf "== Counter Example 2 ==\n"
    --printf "expected: %s\n" $ show $ map fst . take 4 . drop (ln-2) <$> Tex.counter2'
    --printf "actual:   %s\n" $ show $ map fst . take 4 . drop (ln-2) <$> Tex.counter2''
    ----printf "tree:  %s\n" $ show $ Tex.counter2
    --printf "flatten:  %s\n" $ show $ flatten Tex.counter2
    --print $ ln
    --print $ Tex.counter2' == Tex.counter2''
    --return flatten'
    --print Tex.prop_counter_example1
    --putStrLn . show =<< seeA
    --putStrLn . show =<< seeE
                -- 
    -- print x
    -- print 7
    return ()
