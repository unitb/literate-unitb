#!/usr/bin/env runhaskell
import Control.Monad

import Data.Function
import Data.List

import System.Directory
import System.Process

import Utilities.Format

main = do
        ls <- getDirectoryContents "."
        let xs = filter (f "po-") ls
        forM_ xs $ \fn -> do
            putStrLn fn
            system (format "head -n 2 {0}" fn)
            system (format "time z3 -smt2 -T:30 {0}" fn)
    where
        f x xs = x == take (length x) xs

