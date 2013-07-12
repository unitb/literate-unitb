module Document.Test ( test_case ) where

import Data.Map hiding ( map )
import qualified Data.Map as M
import Document.Document

import qualified Document.Tests.Cubes as Cubes
import qualified Document.Tests.SmallMachine as SMch

import Tests.UnitTest

import UnitB.AST
import UnitB.PO

import Z3.Calculation
import Z3.Const
import Z3.Def
import Z3.Z3

test_case = ("Unit-B Document", test, True)

test :: IO Bool
test = test_cases [
        SMch.test_case,
        Cubes.test_case
        ]
