module Main where

import BuildSystem

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.State

import System.Timeout
import System.Console.ANSI
import System.Exit
import System.IO 
import System.Process

interval = Minutes 1
retry_interval = Seconds 1

data Time = Minutes Int | Seconds Int

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
--                forM_ (take 20 $ repeat "") putStrLn
                clearScreen
                let compile x = readProcessWithExitCode "ghc" (x ++ ["--make","-W","-Werror"]) ""
                rs <- mapM compile 
                    [ ["test.hs","-threaded"]
                    , ["continuous.hs","-threaded"]
                    , ["verify.hs"]
                    , ["periodic.hs"]
                    , ["compile.hs"]
                    , ["run_tests.hs","-threaded"] ]
                let (cs,_,yss) = unzip3 rs
                let c = foldl success ExitSuccess cs
                let ys = concat yss
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
    where
        success ExitSuccess ExitSuccess = ExitSuccess
        success _ _                     = ExitFailure 0
