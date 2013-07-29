module Main where

import Control.Concurrent
import Control.Monad

import Data.Map as M (lookup,empty,union,fromList)
import Document.Document

import System.Directory
import System.Environment
import System.IO
--import System.Posix

import Text.Printf

import UnitB.AST
import UnitB.PO

check_one pos m = do
        let { po = case M.lookup (_name m) pos of
            Just po -> po
            Nothing -> empty }
        (po,s,n)   <- verify_changes m po
        return ((n,"> machine " ++ show (_name m) ++ ":\n" ++ s), (_name m,po))

check_file path m = do
        r <- parse_machine path
        case r of
            Right ms -> do
                xs <- forM ms (check_one m)
                putStr $ take 40 $ cycle "\n"
                forM_ (map fst xs) (putStrLn . f)
                return (union (fromList $ map snd xs) m)
            Left xs -> do
                putStr $ take 40 $ cycle "\n"
                forM_ xs (\(x,i,j) -> printf "error (%d,%d): %s\n" i j x)
                return m
    where
        f (n,xs) = unlines (filter p (lines xs) ++ ["Redid " ++ show n ++ " proofs"])
        p ln = take 4 ln /= "  o "

main = do
        args <- getArgs
        case args of
            [xs] -> do
                b <- doesFileExist xs
                if b
                then do
                    pos <- check_file xs empty
                    t <- getModificationTime xs
                    f xs (t, pos) 
                else do
                    putStrLn ("'" ++ xs ++ "' is not a valid file")
            _ -> putStrLn "usage: continuous file"
    where
        f xs (t0,m) = do
            threadDelay 100000
            x <- hReady stdin
            c <- if x then getChar else return ' '
            if c `elem` ['q','Q'] then return ()
            else do 
                t1 <- getModificationTime xs
                m <- if t0 /= t1 
                    then check_file xs m 
                    else return m
                f xs (t1,m) 