module Main where

import qualified UnitB.Test as UB
import qualified Latex.Test_Latex_Parser as LT
import qualified Z3.Test as ZT
import qualified Document.Test as DOC
import qualified Utilities.Format as FMT
import qualified Utilities.Test as UT

import Tests.UnitTest

test_case :: IO Bool
test_case = test_suite 
        [  DOC.test_case
        ,  UB.test_case
        ,  LT.test_case
        ,  ZT.test_case
        ,  FMT.test_case
        ,  UT.test_case
        ]

main :: IO ()
main = do
    b <- test_case
    if b 
    then do
        putStrLn "\n***************"
        putStrLn   "*** SUCCESS ***"
        putStrLn   "***************"
    else do
        putStrLn "\n***************"
        putStrLn   "*** FAILURE ***"
        putStrLn   "***************"
