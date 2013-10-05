module Main where

import BuildSystem

import Control.Concurrent.Thread.Delay
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.State
import Control.Monad.Trans.Writer

import Data.Map hiding ( map )
import Data.Time
import Data.Time.Clock

import System.Directory
import System.FilePath.Posix
import System.IO 
import System.Locale
import System.Process

interval = Minutes 1
retry_interval = Seconds 1

data Time = Minutes Integer | Seconds Integer

microseconds (Minutes x) = x * 60000000
microseconds (Seconds x) = x * 1000000

--break_errs xs = concatMap f $ lines xs
--    where
--        f [] = [Just []]
--        f ys@(x:xs)
--            | isAlpha x       = [Nothing, Just ys]
--            | not $ isAlpha x = [Just ys]

main = do
    flip evalStateT init_state $ forever $ do
        b <- didAnythingChange
        c <- lift $ if b
        then do
            (c,xs,ys) <- readProcessWithExitCode "ghc" ["test"] ""
            forM_ (take 20 $ repeat "") putStrLn
            putStr ys 
            putStr $ (take 60 $ cycle "\b") ++ show c ++ "       "
            hFlush stdout
        else return ()
--            return True
--        if c then do
--            xs <- readFile "errors.txt"
--            putStrLn xs
--        else return ()
        lift $ delay (microseconds retry_interval)