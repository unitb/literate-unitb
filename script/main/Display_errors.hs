#!/usr/bin/env cabal exec runhaskell
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE FlexibleContexts   #-}
module Main where

import Build

import Control.Concurrent
import Control.Precondition 

import Control.Monad
import Control.Monad.Trans

import Data.List

import System.Directory
import System.Environment
import System.FilePath
import System.Process
import System.IO.Unsafe

import Shelly (shelly,rm_f)

compile_script :: Build ()
compile_script = do
        compile_file
        -- profile_test 
        --     >>= run_benchmark
        compile_test 
            >>= run_test
        -- cabal_build "bench-bucket-packaged"
           -- >>= cabal_run
        -- compile_all
        compile_app
        -- profile_app
        return ()

_wait :: IO Bool -> IO ()
_wait cond = do
    b <- cond 
    unless b $ do
        threadDelay 250000
        _wait cond

file :: FilePath
path :: FilePath
_errFile :: FilePath
(file,path,_errFile) = unsafePerformIO $ do
    xs <- getArgs
    let file = xs !! 0
        path = xs !! 1
        _errFile  = xs !! 2
    return (file,path,_errFile)

_o_file :: FilePath
_o_file = replaceExtension file ".o"

inBin :: Pre => FilePath -> FilePath
inBin file = byRel "isPrefixOf" isPrefixOf path file $ path </> "bin" </> drop (length path + 1) (dropExtension file) <.> "o"

compile_file :: Build ()
compile_file = do
    liftIO $ do
        b <- doesFileExist $ inBin file
        when b $ removeFile $ inBin file
    compile True (args (CompileFlags CompileFile False) file)
    liftIO $ rawSystem "touch" [file]
    return ()

run_test :: FilePath -> Build ()
run_test fp = lift $ lift $ void $ rawSystem fp []

run_benchmark :: FilePath -> Build ()
run_benchmark fp = do
    liftIO $ do
        -- removeFile $ takeFileName $ fp ++ ".tix"
        void $ rawSystem fp ["+RTS","-p","-RTS"]
        removeFile $ takeFileName $ fp ++ ".tix"

main :: IO ()
main = do
    -- path <- split ":" `liftM` getEnv "PATH"
    -- print path
    -- ghc_make <- filterM doesFileExist $ map (++ "ghc-make") path
    createDirectoryIfMissing True "bin"

    -- home <- getEnv "HOME"
    -- system "bash" [home </> ".profile"]
    setCurrentDirectory path
    shelly $ do
        rm_f "actual-*.txt"
        rm_f "expected-*.txt"
        rm_f "po-*.z3"
    build path compile_script
    -- printf "%s\n" path
    -- putStrLn $ intercalate " " $ "ghc" : (args CompileFile file)
        -- putStrLn "File ok"
        -- rawSystem "ghc-make" 
        --     [ "ghc-make", "-j4"
        --     , "test.hs"
        --     , "-o", "bin/test"
        --     , "-odir", "bin"
        --     , "-hidir", "interface"
        --     , "-Wall"
        --     , "-Werror"
        --     , "-fno-warn-name-shadowing"
        --     , "-fno-warn-orphans"
        --     , "-fno-warn-type-defaults"
        --     , "-fno-warn-unused-do-bind"
        --     , "-threaded" ]
    -- rawSystem "ghc" (args Make "test.hs")
        -- r <- rawSystem "ghc" (args Make "test_tmp.hs")
        -- when (r == ExitSuccess) $ void $ rawSystem (path </> "bin/test_tmp") []
        -- wait (liftM (not . null) $ readFile errFile)
        -- readFile errFile >>= putStrLn
    return ()
    -- else return ()
    -- putStrLn inf
    -- mapM_ putStrLn xs
    -- putStrLn "allo"
