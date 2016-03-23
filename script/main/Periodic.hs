#!/usr/bin/env cabal exec runhaskell
module Main where

import Tools.BuildSystem
import Tools.Heap

import Control.Concurrent

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class

import Data.List
import Data.Time

import System.Directory
import System.Environment
import System.IO
import System.Process

long_interval :: Time
long_interval = Minutes 1

short_interval :: Time
short_interval = Seconds 10

retry_interval :: Time
retry_interval = Seconds 10

data Time = Minutes Int | Seconds Int

microseconds :: Time -> Int
microseconds (Minutes x) = x * 60000000
microseconds (Seconds x) = x * 1000000

data Monitor = HaskellMon | LaTeXMon
    deriving (Eq, Ord)

main :: IO ()
main = do
    xs <- getArgs
    if not $ length xs <= 2 then 
        putStrLn "usage: periodic [module_name [function_name]]"
    else do
        let args = intercalate " " xs
        evalHeapT $ do
            new HaskellMon $ return init_state
            new LaTeXMon $ return init_state
            focus LaTeXMon $ set_extensions [".tex"]
            forever $ do
                b3 <- focus LaTeXMon $ didAnythingChange
                t0 <- liftIO $ getModificationTime "test"
                t1 <- liftIO $ getModificationTime "last_result.txt"
                lift $ if (t1 <= t0) || b3 then do
                    putStr $ take 80 (repeat '\b') ++ "Testing..."
                    hFlush stdout
                    t2 <- getCurrentTime
                    if null args then do
                        system $ "./run_tests 2>&1 >> /dev/null"
                        system "cp result.txt last_result.txt"
                        tz <- getCurrentTimeZone
                        t  <- getCurrentTime :: IO UTCTime
                        let local = utcToLocalTime tz t
                            time = formatTime defaultTimeLocale "Time: %H:%M:%S" $ local
                        system $ "echo \"" ++ time ++ "\" >> last_result.txt"
                        t0 <- getModificationTime "test"
                        if t2 <= t0 then
                            void $ system "touch test"
                        else return ()
                        void $ system "cat last_result.txt"
                    else do
                        void $ system $ "./run_tests \"" ++ args ++ "\""
                else return ()
                lift $ threadDelay (microseconds retry_interval)
