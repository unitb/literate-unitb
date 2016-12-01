{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.Concurrent
import Control.Invariant
import Control.Lens 
import Control.Monad

import Data.Functor.Compose
import Data.List
import Data.Monoid ((<>))

import Document.Document hiding (system)
import Document.Tests.SmallMachine as SM
import qualified UnitB.Test as UB
import qualified Latex.Test as LT
import Logic.UnitTest 
import qualified Z3.Test as ZT
import qualified Document.Test as DOC
import qualified Utilities.Test as UT
import qualified Code.Test as Code
import qualified Documentation.Test as Sum

import Shelly hiding (time,get)

import Options.Applicative

import System.Directory
import System.Exit
import System.Process

import Test.UnitTest hiding (QuickCheckProps)
import Test.QuickCheck.Lens 

import Utilities.TimeIt
import Test.QuickCheck.ZoomEq

selected_test_case :: TestCase
selected_test_case = test_cases 
        "Selected Literate Unit-B Test Case" 
        [ SM.test_case ]

test_case :: TestCase
test_case = test_cases 
        "Literate Unit-B Test Suite" 
        [  DOC.test_case
        ,  UB.test_case
        ,  LT.test_case
        ,  ZT.test_case
--        ,  FMT.test_case
        ,  UT.test_case
        ,  Code.test_case
        ,  Sum.test_case
        ]

data TestSelection = QuickCheckOnly Int | All Int | POCasesOnly

selectTestCase :: Parser TestCase
selectTestCase = flag Main.test_case selected_test_case
        (  long "selected-case" 
        <> help "Execute only the hard coded test case selection" )

executionMode :: Parser TestSelection
executionMode = 
        flag' POCasesOnly
            (  long "po-only" 
            <> help "among all the test cases, only run the verification test cases and check the PO" )
    <|> (   flag' QuickCheckOnly 
              (  long "quickcheck-only" 
              <> help "run only the QuickCheck properites." )
        <|> pure All)
        <*> (option auto 
                (  short 'c'
                <> metavar "TEST-COUNT"
                <> help "TEST-COUNT specifies the number of examples to test. Default to 100 " ) 
            <|> pure 100)

runSelection :: TestSelection -> TestCase -> IO Bool
runSelection (All n) t = run_test_cases_with t $ argMaxSuccess .= n
runSelection (QuickCheckOnly n) t = run_quickCheck_suite_with t $ argMaxSuccess .= n
runSelection POCasesOnly t = run_poTestSuite t

testScript :: IO Bool
testScript = do
    x <- SM.case0
    let x' = x & mapped.mapped %~ getCompose
        m' = getCompose SM.m0_machine
        m  = SM.m0_machine
    print $ x  == Right [SM.m0_machine]
    print $ x' == Right [m']
    print $ invariantMessage $ x  .== Right [m]
    print $ invariantMessage $ x' .== Right [m']
    return True


parseSelection :: Parser (IO Bool)
parseSelection = 
            flag' testScript
                (  long "select-script" 
                <> help "run hard coded test script" ) 
        <|> runSelection <$> executionMode <*> selectTestCase

trashTestFiles :: IO ()
trashTestFiles = do
    xs <- getDirectoryContents "."
    setNumCapabilities 8
    void $ system "rm actual* expected* po-* log*.z3"

main :: IO ()
main = timeIt $ do
    let opts = info (helper <*> parseSelection)
          ( fullDesc
         <> progDesc "Test Literate Unit-B"
         <> header "test - the Literate Unit-B test suite" )
    writeFile "syntax.txt" $ unlines syntaxSummary
    trashTestFiles
    -- b <- run_quickCheck_suite_with Main.test_case $ argMaxSuccess .= 1000
    -- b <- run_poTestSuite Main.test_case
    b <- join $ execParser opts
    if b 
    then do
        putStrLn "\n***************"
        putStrLn   "*** SUCCESS ***"
        putStrLn   "***************"
        exitSuccess
    else do
        putStrLn "\n***************"
        putStrLn   "*** FAILURE ***"
        putStrLn   "***************"
        exitFailure
