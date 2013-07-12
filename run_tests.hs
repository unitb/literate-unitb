module Main where

import Control.Monad.Error

import GHC.IO.Exception

import System.Process

runRaw phase cmd args  = do
    c <- liftIO $ rawSystem cmd args
    case c of
        ExitSuccess -> return ()
        ExitFailure _ -> throwError ("phase '" ++ phase ++ "' failed")

run phase cmd  = do
    c <- liftIO $ system cmd
    case c of
        ExitSuccess -> return ()
        ExitFailure _ -> throwError ("phase '" ++ phase ++ "' failed")

main = do
        c0 <- rawSystem "ghc" ["test.hs", "--make"] 
        case c0 of
            ExitSuccess -> do
                c1 <- system "./test > result.txt"
                c2 <- rawSystem "cat" ["result.txt"]
                return $ success c1 c2
            ExitFailure _ -> do
                putStrLn "\n***************"
                putStrLn   "*** FAILURE ***"
                putStrLn   "***************"
                return c0
    where
        success ExitSuccess ExitSuccess = ExitSuccess
        success _ _                     = ExitFailure 0
