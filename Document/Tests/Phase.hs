module Document.Tests.Phase where

    -- Modules
import Document.Tests.Suite

    -- Libraries
import Tests.UnitTest


test_case :: TestCase
test_case = test

test :: TestCase
test = test_cases 
            "refinement relations in the phase example" 
            [ (Case "test 0, cyclic refinement relation between machines" (find_errors path0) result0)
            , (Case "test 1, valid references to variables and event declared in ancestor" case1 result1)
            ] 

path0 :: String
path0 = "tests/phases-t0.tex"

result0 :: String
result0 = unlines
    [ "A cycle exists in the refinement structure"
    , "error 174:1:"
    , "\tm0"
    , ""
    , "error 180:1:"
    , "\tm1"
    , ""
    , ""
    ]

path1 :: String
path1 = "tests/phases-t1.tex"

case1 :: IO String
case1 = find_errors path1 

result1 :: String
result1 = "no errors"

