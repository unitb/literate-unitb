{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.Monad

import Data.List

import Document.Document
import qualified UnitB.Test as UB
import qualified Latex.Test_Latex_Parser as LT
import qualified Z3.Test as ZT
import qualified Document.Test as DOC
import qualified Utilities.Test as UT
import qualified Code.Test as Code
import qualified Documentation.Test as Sum

import Utilities.Table

import Shelly hiding (time,get)

import System.Directory

import Tests.UnitTest

import Utilities.TimeIt

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

main :: IO ()
main = timeIt $ do
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
    putStrLn tableType
    if b 
    then do
        putStrLn "\n***************"
        putStrLn   "*** SUCCESS ***"
        putStrLn   "***************"
    else do
        putStrLn "\n***************"
        putStrLn   "*** FAILURE ***"
        putStrLn   "***************"
