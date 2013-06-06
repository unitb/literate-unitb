 module Latex.Test_Latex_Parser where

import Latex.Proof_Parser
import Latex.Parser

import Tests.UnitTest

import Text.ParserCombinators.ReadP

path1 = "/Users/simonhudon/Documents/ecole/EventB/eventb/trunk/thesis 2/"
    ++ "progress/unit-b-papers/2013-iFM/source/contribution.tex"

path2 = "tests/sample.tex"
result2 = concat ["Right (fromList [(\"calculation\"",
            ",[Env{calculation} (13),",
            "Env{calculation} (10)])])"]

path3 = "tests/sorted_sequences_err.tex"
result3 = "Left (\"expected \\\\end{equation}, read '}'\",29,13)"

sections = [
    "calculation",
    "theorem",
    "equation",
    "align",
    "lemma",
    "invariant",
    "machine"]

extract_structure ct = do
    xs <- latex_structure ct
    return (find sections xs)

test_case = ("latex parser", cases, True)

cases = test_suite [
    ("sample.tex", main path2, result2),
    ("sorted seq.tex", main path3, result3) ]

main path = do
        ct <- readFile path
        return $ show $ extract_structure ct
--        either f g lt
--    where
--        f lt        = return $ find ["calculation"] lt
--        g (s,(i,j)) = putStrLn "Error: " ++ s ++ " (" ++ show i ++ ", " ++ show j ++ ")"