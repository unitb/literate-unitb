{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE LambdaCase         #-}
module Main where

import Build

import Control.Concurrent
import Control.Exception

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
        compile_test 
              >>= run_test
        --compile_all
        --compile_app
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

inBin :: (Bool -> FilePath -> FilePath) -> FilePath -> FilePath
inBin arse file = arse (path `isPrefixOf` file) $ path </> "bin" </> drop (length path + 1) (dropExtension file) <.> "o"

compile_file :: Build ()
compile_file = do
    liftIO $ do
        b <- doesFileExist $ inBin assert file
        when b $ removeFile $ inBin assert file
    compile True (args CompileFile file)

run_test :: FilePath -> Build ()
run_test fp = lift $ lift $ void $ rawSystem fp []

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
