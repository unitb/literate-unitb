module Main where

import Tools.BuildSystem
import Tools.Heap

import Control.Concurrent

import Control.Monad
import Control.Monad.Trans

import Data.Time

import System.Directory
import System.Environment
import System.IO
import System.Locale
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
    if not $ length xs <= 1 then 
        putStrLn "usage: run_test [module_name]"
    else do
        let args = concat xs
        evalHeapT $ do
            new HaskellMon $ return init_state
            new LaTeXMon $ return init_state
            focus LaTeXMon $ set_extensions [".tex"]
            forever $ do
                b3 <- focus LaTeXMon $ didAnythingChange
                t0 <- liftIO $ getModificationTime "test"
                t1 <- liftIO $ getModificationTime "last_result.txt"
                lift $ if (t1 <= t0) || b3 then do
                    if null args then do
                        putStr $ take 80 (repeat '\b') ++ "Testing..."
                        hFlush stdout
                        t2 <- getCurrentTime
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
                    else
                        void $ system $ "./run_tests \"" ++ args ++ "\""
                else return ()
                lift $ threadDelay (microseconds retry_interval)
