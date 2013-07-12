module Main where

import Control.Monad

import qualified UnitB.Test as UB
import qualified Latex.Test_Latex_Parser as LT
import qualified Z3.Test as ZT
import qualified Document.Test as DOC

import Tests.UnitTest

--test_cases :: [(IO Bool, String)]
test_case = test_suite [
        DOC.test_case,
        UB.test_case, 
        LT.test_case, 
        ZT.test_case
    ]

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
