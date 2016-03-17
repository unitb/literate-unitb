#!/usr/bin/env runhaskell -W -Werror
{-# LANGUAGE OverloadedStrings,FlexibleContexts #-}
module Main where

import Build
import Interactive.Config

import Control.Concurrent
import Control.Monad.Except

import Data.Char
import Data.List
import Data.Time

import GHC.IO.Exception

import Shelly as Sh hiding (FilePath,(</>))

import System.IO
import System.Directory hiding ( executable )
import System.Environment
import System.Process

import Text.Printf

import Z3.Version

p_system :: String -> IO ExitCode
p_system cmd
    | is_os_windows = system cmd
    | otherwise     = system $ "./" ++ cmd

runRaw :: (MonadIO m, MonadError [Char] m) 
       => [Char] -> String -> [String] -> m ()
runRaw phase cmd args  = do
    c <- liftIO $ rawSystem cmd args
    case c of
        ExitSuccess -> return ()
        ExitFailure _ -> throwError ("phase '" ++ phase ++ "' failed")

run :: (MonadIO m, MonadError [Char] m)
    => [Char] -> String -> m ()
run phase cmd  = do
    c <- liftIO $ system cmd
    case c of
        ExitSuccess -> return ()
        ExitFailure _ -> throwError ("phase '" ++ phase ++ "' failed")

general :: IO ExitCode
general = do
        let c1 = ExitSuccess
        case c1 of
            ExitSuccess -> do
                path <- getCurrentDirectory
                build path (cabal_build "test")
                --build path compile_all
                putStrLn "Running test ..."
                hFlush stdout
                t0 <- getCurrentTime
                --c1 <- p_system "bin/test > result.txt"
                c1 <- system "cabal run test > result.txt"
                t1 <- getCurrentTime
                ys' <- lines `liftM` readProcess "git" ["ls-files","*hs"] ""
                zs' <- mapM (liftM (length . lines) . readFile) ys'
                let -- ys  = "total" : ys'
                    zs  = sum zs' : zs'
                    lc  = filter (\(_,x) -> not $ "test" `isInfixOf` map toLower x) $ zip zs' ys'
                    lc' = (sum $ map fst lc,"total") : lc
                    n = maximum $ map (length . show) zs
                    pad xs = replicate (3 + n - length xs) ' ' ++ xs ++ " "
                    f (n,xs) = pad (show n) ++ xs
                appendFile "result.txt"
                    $ unlines 
                    $ "Lines of Haskell code:"
                       : (take 6 $ map f $ reverse 
                            $ sortOn fst lc')
                      ++ ["Run time: " ++ (let (m,s) = divMod (round $ diffUTCTime t1 t0) (60 :: Int) in 
                                printf "%dm %ds" m s)]
                xs <- readFile "result.txt"
                putStrLn xs
                return c1
            ExitFailure _ -> do
                putStrLn "\n***************"
                putStrLn   "*** FAILURE ***"
                putStrLn   "***************"
                return c1

specific :: String -> Maybe String -> IO ()
specific mod_name fun_name = do
        b <- doesFileExist $ executable "test_tmp"
        when b $ shelly $ do
            rm_f $ fromText $ executable "test_tmp"
        h <- openFile "test_tmp.hs" WriteMode
        hPrintf h test_prog mod_name
        hClose h
        fix $ \rec -> do
            b <- doesFileExist $ executable "test_tmp"
            threadDelay 50000
            if b 
                then return ()
                else do
                    rec
        putStrLn "Running test ..."
        hFlush stdout
        void $ p_system "test_tmp"
        hFlush stdout
    where
        test_prog = unlines 
            [ "module Main where"
            , "import %s "
            , "main :: IO Bool"
            , "main = " ++ fun 
            ]
        fun = case fun_name of
            Just x  -> x
            Nothing -> "test"

main :: IO ()
main = do
    xs <- getArgs
    b <- check_z3_bin
    system "rm actual* expected* po-* log*.z3"
    if b then 
        case xs of
            []    -> general >> return ()
            [x]   -> specific x Nothing
            [x,y] -> specific x $ Just y
            _   -> putStrLn "usage: run_test [module_name [function_name]]"
    else
        return ()
    