{-# LANGUAGE TemplateHaskell #-}
module Main where

import Data.List
import Data.Version
import Development.GitRev
import Paths_literate_unitb

import System.Environment
import Text.Printf.TH

printUnitBZipName :: [String] -> IO ()
printUnitBZipName os = do
        let v = showVersion version
            h = take 12 $gitHash
        putStrLn $ [s|literate-unitb-%s-%s-%s|] v (intercalate "-" os) h

main :: IO ()
main = do
    xs <- getArgs
    if null xs 
        then putStrLn "usage: unitb-zip-name os"
        else printUnitBZipName xs
