#!/usr/bin/env runhaskell
{-# LANGUAGE QuasiQuotes #-}
import Control.Monad

import System.Directory
import System.Process

import Utilities.PrintfTH

main :: IO ()
main = do
        ls <- getDirectoryContents "."
        let xs = filter (f "po-") ls
        forM_ xs $ \fn -> do
            putStrLn fn
            system ([printf|head -n 2 %s|] fn)
            system ([printf|time z3 -smt2 -T:30 %s|] fn)
    where
        f x xs = x == take (length x) xs

