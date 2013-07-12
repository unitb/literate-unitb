module Main where

import Control.Monad

import Document.Document

import System.Directory
import System.Environment
import System.Posix

import UnitB.PO

check_one m = do
        (s,_,_)   <- str_verify_machine m
        return s        

check path = do
        r <- parse_machine path
        case r of
            Right ms -> do
                xs <- forM ms check_one
                putStr $ take 40 $ cycle "\n"
                forM_ xs (putStrLn . f)
            Left x -> print x
    where
        f xs = unlines $ filter p $ lines xs
        p ln = take 4 ln /= "  o "

main = do
        args <- getArgs
        case args of
            [xs] -> do
                b <- doesFileExist xs
                if b
                then do
                    check xs
                    t <- getModificationTime xs
                    foldM (f xs) t $ repeat ()
                    return ()
                else do
                    putStrLn (xs ++ " is not a valid file")
            _ -> putStrLn "usage: continuous file"
    where
        f xs t0 () = do
            sleep 1
            t1 <- getModificationTime xs
            when (t0 /= t1) $ check xs
            return t1 