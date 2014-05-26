module Document.Tests.Phase where

    -- Modules
import Document.Document

    -- Libraries
import Tests.UnitTest

import Utilities.Syntactic

test_case :: TestCase
test_case = Case "refinement relations in the phase example" test True

test :: IO Bool
test = test_cases 
            [ (Case "test 0, cyclic refinement relation between machines" (parse_machine path0) result0)
            , (Case "test 1, valid references to variables and event declared in ancestor" case1 result1)
            ] 

path0 :: String
path0 = "tests/phases-t0.tex"

result0 :: Either [Error] b
result0 = Left [Error "A cycle exists in the refinement structure: m0, m1" (LI "" 1 1)]

path1 :: String
path1 = "tests/phases-t1.tex"

case1 :: IO (Maybe [Error])
case1 = do
    r <- parse_machine path1 
    return $ either Just (const Nothing) r

result1 :: Maybe a
result1 = Nothing

