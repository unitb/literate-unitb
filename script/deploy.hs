#!/usr/bin/env runhaskell
module Main where

import Build

import Control.Monad.Trans
import Control.Monad.Trans.Maybe

import Data.Functor

import System.Directory
import System.Process

main :: IO ()
main = void $ runMaybeT $ do
    MaybeT $ do
        path <- getCurrentDirectory
        build path compile_app
    lift $ system $ "cp bin/continuous /usr/bin/unitb"
    return ()
