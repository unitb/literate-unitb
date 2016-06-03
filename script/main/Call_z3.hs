#!/usr/bin/env cabal exec runhaskell
{-# LANGUAGE QuasiQuotes #-}
import Control.Monad

import Data.List

import System.Directory
import System.Process

import Text.Printf.TH

main :: IO ()
main = do
        ls <- getDirectoryContents "."
        let xs = filter (isPrefixOf "po-") ls ++ filter (isPrefixOf "log") ls
        forM_ xs $ \fn -> do
            putStrLn fn
            system ([printf|head -n 2 %s|] fn)
            system ([printf|time z3 -smt2 -T:30 %s|] fn)

