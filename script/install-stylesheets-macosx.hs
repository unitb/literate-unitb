#!/usr/bin/env cabal exec runhaskell -W -Werror
module Main where

import Control.Monad

import System.Directory
import System.Environment
import System.FilePath

main :: IO ()
main = do
    home <- getEnv "HOME"
    let sty = [ "bsymb.sty" 
              , "calculation.sty" 
              , "eventB.sty" 
              , "unitb.sty" ]
        src  = "Tests"
        path = home </> "Library/texmf/tex/"
    forM_ sty $ \fn -> do
        copyFile (src </> fn) (path </> fn)
