#!/usr/bin/env runhaskell

import Control.Monad

import Data.Map as M

import System.Directory
import System.Environment

import Interactive.Serialize

main :: IO ()
main = do
    xs <- getArgs
    ys <- liftM (zip xs) $ mapM doesFileExist xs
    case ys of 
        [(x,True)] -> do
            xs <- load_pos x M.empty
            dump_z3 Nothing x xs
        _ -> 
            putStrLn "usage: extract_z3 tex_file"
