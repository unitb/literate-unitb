module Latex.Test where

import Tests.UnitTest

list = [] :: Show a => [(String, IO a, a)]

test_case :: IO Bool
test_case = test_suite list