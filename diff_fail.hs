module Main where

import Data.Function
import Data.List

import Interactive.Config

import System.Directory

import Utilities.Format

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
            let file1 = (format "actual-{0}.txt" n)
                file2 = (format "expected-{0}.txt" n)
            b1 <- doesFileExist file1
            b2 <- doesFileExist file2
            if b1 && b2 then do
                diff file1 file2
                return ()
            else return ()
            proc (n+1) (delete file1 xs) (delete file2 ys)
        ) 0 xs ys
    where
        f x xs = x == take (length x) xs