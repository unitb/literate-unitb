module Main where

import Control.Monad

import Document.Document

import System.Directory
import System.Environment
--import System.Posix

import Text.Printf

import UnitB.AST
import UnitB.PO

check_one m = do
        (s,_,_)   <- str_verify_machine m
        return ("> machine " ++ show (_name m) ++ ":\n" ++ s)        

check path = do
        r <- parse_machine path
        case r of
            Right ms -> do
                xs <- forM ms check_one
--                putStr $ take 40 $ cycle "\n"
                forM_ xs (putStrLn . f)
            Left (x,i,j) -> printf "error (%d,%d): %s\n" i j x
    where
        f xs = unlines $ filter p $ lines xs
        p ln = take 4 ln /= "  o "

main = do
        args <- getArgs
        case args of
            [xs] -> do
                b <- doesFileExist xs
                if b
                then check xs
--                    t <- getModificationTime xs
--                    foldM (f xs) t $ repeat ()
--                    return ()
                else
                    putStrLn ("'" ++ xs ++ "' is not a valid file")
            _ -> putStrLn "usage: verify file"
--    where
--        f xs t0 () = do
--            sleep 1
--            t1 <- getModificationTime xs
--            when (t0 /= t1) $ check xs
--            return t1 