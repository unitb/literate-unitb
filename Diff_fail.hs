#!/usr/bin/env runhaskell
module Main where

import Data.Function
import Data.List

import Interactive.Config

import System.Directory
import System.Process

import Text.Printf

main :: IO ()
main = do
    ls <- getDirectoryContents "."
    let xs = filter (f "actual-") ls
        ys = filter (f "expected-") ls
    fix (\proc n xs ys -> do
        print xs
        print ys
        if null xs || null ys then return ()
        else do
            let file1 = (printf "actual-%d.txt" n)
                file2 = (printf "expected-%d.txt" (n :: Int))
            b1 <- doesFileExist file1
            b2 <- doesFileExist file2
            if b1 && b2 then do
                system $ "./quote.hs \"" ++ file1 ++ "\" | pbcopy"
                diff file1 file2
                return ()
            else return ()
            proc (n+1) (delete file1 xs) (delete file2 ys)
        ) 0 xs ys
    where
        f x xs = x == take (length x) xs