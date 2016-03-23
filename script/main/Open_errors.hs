#!/usr/bin/env cabal exec runhaskell
import Control.Concurrent
import Control.Monad.Fix

import Data.Tuple

import System.Directory

import Utilities.Config

data Input = Quit | Next

keyboard :: IO (MVar Input)
keyboard = do
        v <- newMVar Next
        tid <- myThreadId
        forkIO $ fix $ \rec -> do
            x <- getLine
            if x == "quit" then do 
                putMVar v Quit
                killThread tid
            else if x == "next" then do
                putMVar v Next
                rec
            else rec
        return v

main :: IO ()
main = do
    b <- doesFileExist "compile_errors.txt"
    if b then do
        v  <- keyboard
        xs <- readFile "compile_errors.txt"
        fix (\rec xs -> do
            k <- takeMVar v
            case (xs,k) of
                (x:xs, Next) -> do
                    uncurry open_at $ swap $ read x
                    putMVar v Next 
                    rec xs
                _ -> return ())
            (take 1 $ filter (not . null) $ lines xs)              
    else putStrLn "file does not exist"
            
        