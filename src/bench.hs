{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.Monad

import Data.List
import Data.Time

import Document.Document
import qualified UnitB.Test as UB
import qualified Latex.Test as LT
import qualified Z3.Test as ZT
import qualified Document.Test as DOC
import qualified Utilities.Test as UT
import qualified Code.Test as Code
import qualified Documentation.Test as Sum


import Shelly

import System.Directory
import System.Environment
import System.IO

import Test.UnitTest
import Text.Printf

import Logic.Names
import Utilities.Map

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

timeItT :: IO a -> IO (Double,a)
timeItT cmd = do
    start <- getCurrentTime
    x <- cmd 
    end <- getCurrentTime 
    return (fromRational $ toRational $ end `diffUTCTime` start,x)

main :: IO ()
main = do
    (t,()) <- timeItT $ do
        writeFile "syntax.txt" $ unlines syntaxSummary
        xs <- getDirectoryContents "."
        let prefix ys = any (ys `isPrefixOf`) xs
        when (prefix "actual-") $
            shelly $ rm_f "actual-*.txt"
        when (prefix "expected-") $
            shelly $ rm_f "expected-*.txt"
        when (prefix "po-") $
            shelly $ rm_f "po-*.z3"
        b <- run_test_cases test_case
        if b 
        then do
            putStrLn "\n***************"
            putStrLn   "*** SUCCESS ***"
            putStrLn   "***************"
        else do
            putStrLn "\n***************"
            putStrLn   "*** FAILURE ***"
            putStrLn   "***************"
    name <- getProgName
    withFile "bench-result.txt" AppendMode $ \h -> do
        hPrintf h "%s,%s,%s,%f\n" name tableType nameType t 
