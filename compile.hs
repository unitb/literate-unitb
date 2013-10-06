module Main where

import BuildSystem

import Control.Concurrent.Thread.Delay
import Control.Concurrent.Timeout
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

repeatWhile m = do
    b <- m
    if b 
        then repeatWhile m
        else return ()

main = do
    flip evalStateT [] $ flip evalStateT init_state $ forever $ do
        b <- didAnythingChange
        if b then do
            ys <- liftIO $ do
                forM_ (take 20 $ repeat "") putStrLn
                (c,xs,ys) <- readProcessWithExitCode "ghc" ["test"] ""
                putStr ys 
                putStrLn $ (take 60 $ cycle "\b") ++ show c ++ "       "
                hFlush stdout
                return ys
            lift $ put ys
        else return ()
        ys <- lift $ get
        liftIO $ do
            xs <- timeout (microseconds retry_interval) getLine
            if xs == Just "less" then do
                writeFile "errors.txt" ys
                pc <- runCommand "less errors.txt"
                void $ waitForProcess pc
            else return ()
--            delay (microseconds retry_interval)
        return True
            