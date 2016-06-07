module Document.Tests.CompCalc where

    -- Modules
import Document.Tests.Suite

import Logic.Expr
import Logic.Proof


    -- Libraries
import Data.Map as M hiding (split, map)


import Test.UnitTest

test_case :: TestCase
test_case = test

test :: TestCase
test = test_cases
            "theories with new notation: comp calc"
            [ (POCase "proving a theorem with the everywhere operator" 
                case0 result0)
            ]            

path0 :: FilePath
path0 = [path|Tests/comp-calc.tex|]

result0 :: String
result0 = unlines [" xxx THM/CC:10i"]

case0 :: IO (String, Map Label Sequent)
case0 = verify_thy path0 "ctx0"
