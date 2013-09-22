module Document.Tests.Phase where

    -- Modules
import Document.Document

import UnitB.AST
import UnitB.PO
import UnitB.FunctionTheory

import Z3.Z3 hiding (verify)

    -- Libraries
import Control.Monad.IO.Class
import Control.Monad.Trans
import Control.Monad.Trans.Either

import Data.Map

import Tests.UnitTest

import Utilities.Syntactic

test_case = Case "refinement relations in the phase example" test True

test = test_cases 
            [ (Case "test 0, cyclic refinement relation between machines" (parse_machine path0) result0)
            , (Case "test 1, valid references to variables and event declared in ancester" case1 result1)
            ] 

path0 = "tests/phases-t0.tex"
result0 = Left [("A cycle exists in the refinement structure: m0,m1",0,0)]

path1 = "tests/phases-t1.tex"
case1 = do
    r <- parse_machine path1 
    return $ either Just (const Nothing) r
result1 = Nothing