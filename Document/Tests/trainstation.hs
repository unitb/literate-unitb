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

trainType = USER_DEFINED "\\TRAIN"

machine0 = (empty_machine "m0") {
        theory = empty_theory { 
                types = ["\\TRAIN"], 
                dummies = singleton "t" $ Var "t" $ trainType },
        variables = singleton "in" (Var "in" $ SET trainType),
        events = fromList [(label "enter", empty_event), (label "leave", empty_event)],
        props = props0
    }
props0 = empty_property_set {
        program_prop = singleton (label "tr0") 
            (Transient [Var "t" trainType] (t `zelem` in_var) (label "leave") )
        }
    where
        (t, t_decl) = var "t" trainType
        (in_var, in_decl) = var "in" (SET trainType)

path0 = "Tests/train-station.tex"
case0 = parse_machine path0