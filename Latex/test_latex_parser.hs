module Latex.Test_Latex_Parser where

import Data.List
import qualified Data.Map as M 

import Latex.Proof_Parser
import Latex.Parser

import Tests.UnitTest

import Text.ParserCombinators.ReadP

import Utilities.Format

path1 = "/Users/simonhudon/Documents/ecole/EventB/eventb/trunk/thesis 2/"
    ++ "progress/unit-b-papers/2013-iFM/source/contribution.tex"

path2 = "tests/sample.tex"
result2 = concat ["Right (fromList [",
            "(\"align\",[]),",
            "(\"calculation\",",
                "[Env{calculation} (13),",
                 "Env{calculation} (10)]),",
            "(\"equation\",[]),",
            "(\"invariant\",[]),",
            "(\"lemma\",[]),",
            "(\"machine\",[]),",
            "(\"theorem\",[])",
            "])"]

path3 = "tests/sorted_sequences_err.tex"
result3 = "Left [(\"expected \\\\end{equation}, read '}'\",29,12)]"

path4 = "tests/sorted_sequences.tex"
path5 = "tests/integers.tex"

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
    return (find_env sections xs)

test_case = ("latex parser", cases, True)

cases = test_cases [
    (Case "sample.tex" (main path2) result2),
    (Case "sorted seq err.tex" (main path3) result3),
    (CalcCase "reconstitute sample.tex" 
        (tests path2) 
        (fmap uncomment $ readFile path2)),
    (CalcCase "reconstitute integers.tex" 
        (tests path5) 
        (fmap uncomment $ readFile path5)),
    (CalcCase "reconstitute sorted seq.tex" 
        (tests path4) 
        (fmap uncomment $ readFile path4)) ]

find_env :: [String] -> [LatexDoc] -> M.Map String [LatexDoc]
find_env kw xs = M.map reverse $ foldl f (M.fromList $ zip kw $ repeat []) xs
    where
        f m (t@(Env name _ c _))
            | name `elem` kw = M.insertWith (++) name [t] m
            | otherwise        = fold_doc f m t
        f m t                  = fold_doc f m t

main path = do
        ct <- readFile path
        return $ show $ extract_structure ct

tests path = do
        ct <- readFile path
        let x = (do
            tree <- latex_structure ct
            return (concatMap flatten tree))
        return (case x of
            Right xs -> xs
            Left msgs -> error $ unlines $ map (\(xs, i, j) -> format "error ({0},{1}): {2}" i j xs) msgs)

--        either f g lt
--    where
--        f lt        = return $ find_env ["calculation"] lt
--        g (s,(i,j)) = putStrLn "Error: " ++ s ++ " (" ++ show i ++ ", " ++ show j ++ ")"