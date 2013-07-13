module Document.Tests.TrainStation
    ( test_case )
where

import Data.Map hiding ( map )
import qualified Data.Map as M
import Document.Document

import Tests.UnitTest

import UnitB.AST
import UnitB.PO

import Z3.Calculation
import Z3.Const
import Z3.Def
import Z3.Z3

test_case = Case "train station example" test True

--test :: IO Bool
test = test_cases [
            (Case "test 0, syntax" case0 $ Right [machine0])
        ]
        
machine0 = (empty_machine "m0") {
    theories = [empty_theory { types = ["\\TRAIN"] }],
    variables = singleton "in" (Var "in" $ SET $ USER_DEFINED "\\TRAIN") }
path0 = "Tests/train-station.tex"
case0 = parse_machine path0