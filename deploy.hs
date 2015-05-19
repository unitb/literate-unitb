#!/usr/bin/env runhaskell
module Main where

import System.Process

main :: IO ()
main = do
    system $ "cp bin/continuous /usr/bin/unitb"
    return ()
