module Main where

import BuildSystem

import Control.Concurrent.Thread.Delay
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.State
import Control.Monad.Trans.Writer

import Data.Map hiding ( null )
import Data.Time
import Data.Time.Clock

import System.Directory
import System.Environment
import System.Locale
import System.Process

long_interval = Minutes 1
short_interval = Seconds 10
retry_interval = Seconds 10

data Time = Minutes Integer | Seconds Integer

microseconds (Minutes x) = x * 60000000
microseconds (Seconds x) = x * 1000000

main = do
    xs <- getArgs
    if not $ length xs <= 1 then 
        putStrLn "usage: run_test [module_name]"
    else do
        let args = concat xs
        let { interval = if null xs 
            then long_interval
            else short_interval }
        flip evalStateT init_state $ do
            set_extensions [".hs",".tex",".lhs"]
            forever $ do
                b2 <- didAnythingChange
                lift $ if b2 then do
                    if null args then do
                        t0 <- getModificationTime "test"
                        t1 <- getModificationTime "last_result.txt"
                        if t1 <= t0 then do
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
                        else return ()
                    else
                        void $ system $ "./run_tests \"" ++ args ++ "\""
--                    delay (microseconds interval)
                else return ()
                lift $ delay (microseconds retry_interval)