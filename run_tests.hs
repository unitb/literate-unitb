module Main where

import Control.Monad.Error

import GHC.IO.Exception

import System.IO
--import System.Posix
import System.Environment
import System.Process

import Text.Printf

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

general = do
        c0 <- rawSystem "ghc" ["test.hs", "--make"] 
        c3 <- rawSystem "ghc" ["continuous.hs", "--make"]
        c4 <- rawSystem "ghc" ["verify.hs", "--make"]
        case c0 `success` c3 `success` c4 of
            ExitSuccess -> do
                c1 <- system "./test > result.txt"
                system "echo \"Lines of Haskell code:\" >> result.txt"
                system "grep . */*.hs *.hs | wc >> result.txt"
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

specific :: String -> IO ()
specific mod_name = do
        h <- openFile "test_tmp.hs" WriteMode
        hPrintf h test_prog mod_name
        hClose h
        c0 <- rawSystem "ghc" ["test_tmp.hs", "--make"]
        case c0 of
            ExitSuccess -> 
                system "./test_tmp" >> return ()
            ExitFailure _ -> do
                putStrLn "\n***************"
                putStrLn   "*** FAILURE ***"
                putStrLn   "***************"
    where
        test_prog = unlines 
            [ "module Main where"
            , "import %s "
            , "main = test" 
            ]

main = do
    xs <- getArgs
    case xs of
        []  -> general >> return ()
        [x] -> specific x
        _   -> putStrLn "usage: run_test [module_name]"
    