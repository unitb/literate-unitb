#!/usr/bin/env cabal exec runhaskell
import Control.Applicative
import Control.Monad

import System.Directory
import System.Environment
import System.FilePath

import Text.Printf

paths :: [String]
paths = 
    [ "z3-4.3.2.2ca14b49fe45-x64-osx-10.9.2"
    , "z3-4.3.2.784307fc3001-x64-osx-10.8.2"
    , "z3-4.3.2.5e72cf0123f6-x64-osx-10.8.2"
    , "z3-4.4.0.0482e7fe727c-x64-osx-10.9.5" ]

versions :: [String]
versions = map show [1..length paths]

deploy :: IO ()
deploy = do
    forM_ (zip [(1 :: Int)..] paths) $ \(i,p) ->
        copyFile (p </> "bin/z3") (printf "/usr/bin/z3-%d" i)

main :: IO ()
main = do
    v <- concat <$> getArgs
    if v `elem` versions then 
        copyFile (printf "/usr/bin/z3-%s" v) "/usr/bin/z3"
    else putStrLn "invalid version"