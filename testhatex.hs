module TestHaTex where

import Control.Monad

import Data.List as L
import Data.Map hiding ( foldl, map, lookup, filter )
import qualified Data.Text as T

import System.IO.Unsafe

import Text.LaTeX.Base.Parser
import Text.LaTeX.Base.Render
import Text.LaTeX.Base.Syntax

import UnitB.AST

data Tree a = Node a [Tree a]

path = "/Users/simonhudon/Downloads/z3/Tests/small_machine.tex"

flat :: LaTeX -> [LaTeX]
flat (TeXSeq x y) = flat x ++ flat y
flat x            = [x]

flat_arg (OptArg x)   = [x]
flat_arg (FixArg x)   = [x]
flat_arg (MOptArg xs) = xs
flat_arg (SymArg x)   = [x]
flat_arg (MSymArg xs) = xs

fold_doc f x t =
    case t of
        TeXRaw _      -> x
        TeXComm _ xs  -> foldl f x $ concatMap flat_arg xs
        TeXCommS _    -> x
        TeXEnv _ xs y -> foldl f x (concatMap flat_arg xs ++ [y])
        TeXMath y     -> f x y
        TeXNewLine _  -> x
        TeXOp _ y z   -> foldl f x [y,z]
        TeXBraces y   -> f x y
        TeXComment _  -> x
        TeXSeq y z    -> foldl f x [y,z]
        TeXEmpty      -> x

map_doc f t = reverse $ fold_doc g [] t
    where
        g xs x = f x : xs

as_tree :: LaTeX -> Tree LaTeX
as_tree t = head $ f [] t
    where
        f xs x = Node x (fold_doc f [] x) : xs

zip_tree :: Tree a -> Tree b -> Tree (a,b)
zip_tree (Node x xs) (Node y ys) = Node (x,y) $ map (uncurry zip_tree) $ zip xs ys

line_info :: LaTeX -> Tree Int
line_info t = head $ snd $ f (1,[]) t
    where
        f :: (Int,[Tree Int]) -> LaTeX -> (Int,[Tree Int])
        f (n,xs) t = 
            ( (case t of
                TeXRaw ys -> n' + T.length (zs ys)
                _         -> n'),
              Node n (reverse ys) : xs)
            where
                zs ys   = T.filter (== '\n') ys :: T.Text
                (n',ys) = fold_doc f (n,[]) t :: (Int, [Tree Int])

with_print x = unsafePerformIO (do 
        putStrLn "----------"
        putStrLn $ show x
        return x)

in_mch = [ "evassignment", "invariant", "evguard", "evcsched", "evfsched" ]

--find_env :: Text -> LaTeX -> [LaTeX]
--find_env n t = f [] t
--    where
--        f xs x@(TeXEnv name _ _)
--                | n == name         = x : xs
--                | n `elem` in_mch   = xs
--                | otherwise         = fold_doc f xs x

    -- From a document, find all the machine pieces, put them together
    -- and return the content of the machines
machine_env :: LaTeX -> (Map Text LaTeX, [String])
machine_env tex = fold_doc f (empty, []) tex
    where 
        f (m,es) x@(TeXEnv n xs _)
                | n == "machine"   = 
                    case name of
                        Just n  -> (insertWith g n x m, es)
                        Nothing -> (m, "Require a name for a machine":es)
                | otherwise         = fold_doc f (m,es) x
            where
                name = case xs of
                        FixArg (TeXRaw xs):_ -> Just xs
                        _ -> Nothing
        f xs t = fold_doc f xs t
        g (TeXEnv n0 _ xs) (TeXEnv n1 _ ys) = (TeXEnv n1 [] (TeXSeq ys xs))

merge_machine :: Machine -> Machine -> Machine
merge_machine x y = empty_machine "shiyyyit"

get_machines :: LaTeX -> (Map Text Machine, [String])
get_machines x = f (empty,[]) x
    where 
        f (m,es) x@(TeXEnv n xs _)
                | n == fromString "machine"   = snd $ with_print((),
                    case name of
                        Just n  -> (insertWith merge_machine n (empty_machine $ show n) m, es)
                        Nothing -> (m, "Require a name for a machine":es))
                | otherwise         = fold_doc f (m,es) x
            where
                name = case xs of
                        FixArg (TeXRaw xs):_ -> Just xs
                        _ -> Nothing
        f xs t = fold_doc f xs t

    -- From a machine, find all the variable declaration sections
--variables :: LaTeX -> (Map 

open (TeXEnv _ _ x) = flat x

uncomment :: Text -> Text
uncomment t = T.unlines $ map (T.takeWhile (/= '%')) $ T.lines t

main = do
        ct <- fmap uncomment $ readFileTex path
--        ct <- readFileTex path
        forM_ (T.lines ct) (putStrLn . show)
        let d0 = parseLaTeX ct
        let d1 = (case d0 of
                Right x -> x
                Left x -> error $ show x)
--        return $ get_machines d1
--        let d2 = machine_env d1 -- flat d1 !! 17
        forM_ (open (flat d1 !! 17)) (\x -> do
            (putStrLn . show) x)
--        return d2