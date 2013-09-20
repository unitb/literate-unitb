module Main where

import Control.Concurrent.Thread.Delay
import Control.Monad

import Data.Time
import Data.Time.Clock

import System.Directory
import System.Locale
import System.Process

interval = Minutes 1
retry_interval = Seconds 30

data Time = Minutes Integer | Seconds Integer

microseconds (Minutes x) = x * 60000000
microseconds (Seconds x) = x * 1000000

main = do
    forever $ do
        b <- doesFileExist "test"
        c <- if b
        then do
            t0 <- getModificationTime "test"
            system "ghc test 2>&1 >> /dev/null"
            t1 <- getModificationTime "test"
            return (t0 /= t1)
        else do
            system "ghc test 2>&1 >> /dev/null"
            return True
        if c then do
            system "./run_tests 2>&1 >> /dev/null"
            system "cp result.txt last_result.txt"
            tz <- getCurrentTimeZone
            t  <- getCurrentTime :: IO UTCTime
            let time = formatTime defaultTimeLocale "Time: %H:%M:%S" $ utcToLocalTime tz t
            system $ "echo \"" ++ time ++ "\" >> last_result.txt"
            system "cat last_result.txt"
            delay (microseconds interval)
        else delay (microseconds retry_interval)