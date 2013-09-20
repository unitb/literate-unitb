module Main where

import Control.Concurrent.Thread.Delay
import Control.Monad

import System.Process

interval = Minutes 10

data Time = Minutes Integer | Seconds Integer

microseconds (Minutes x) = x * 60000000
microseconds (Seconds x) = x * 1000000

main = do
    forever $ do
        system "./run_tests"
        system "cp result.txt last_result.txt"
        delay (microseconds interval)