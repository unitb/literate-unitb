#!/usr/bin/env cabal exec runhaskell

import Control.Monad

import Data.List

import System.Environment

import Utilities.Config    
import Utilities.Directory

main :: IO ()
main = do
        xs <- getArgs
        case xs of
            [x] -> do
                xs <- (drop 2 . head . lines) `liftM` readFile x
                --let xs' = "\"" ++ xs ++ "\""
                sources <- visit "." [".hs",".lhs"]
                ys <- concat `liftM` forM sources (\f -> do
                    zs <- (zip [1..] . lines) `liftM` readFile f
                    let p (_,ln) = xs `isInfixOf` ln
                    return $ zip (map fst $ filter p zs) $ repeat f)
                forM_ ys $ \(n,fn) -> do
                    open_at n fn
                    --fix $ \rec -> do
                    --    xs <- getLine
                    --    if xs /= ":q" then do
                    --        goto_definition fn xs
                    --        rec
                    --    else return ()
            [] -> putStrLn "Usage: find_case error_file"
