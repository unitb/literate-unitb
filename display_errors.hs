{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE LambdaCase         #-}
module Main where
import Control.Concurrent

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Maybe

-- import Data.List
-- import Data.List.Utils

import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import System.Process
import System.IO.Unsafe

import Shelly (shelly,rm_f)

-- import Text.Printf

_wait :: IO Bool -> IO ()
_wait cond = do
    b <- cond 
    unless b $ do
        threadDelay 250000
        _wait cond

data CompileMode = Make | CompileFile

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
inf :: FilePath
inf  = "interface"
bin :: FilePath
bin  = "bin"

args :: CompileMode -> FilePath -> [FilePath]
args opt file = 
        flag ++
        [ "-j8"
        , "-odir" ++ bin
        , "-i" ++ inf
        , "-hidir" ++ inf
        , "-W", "-fwarn-missing-signatures"
        , "-fwarn-incomplete-uni-patterns"
        , "-fwarn-missing-methods"
        , "-threaded"
        , "-fwarn-tabs", "-Werror"
        -- , "-v"
        ]
    where
        flag = case opt of 
                    CompileFile -> ["-c",file]
                    Make        -> ["--make",file,"-o",path </> "bin" </> dropExtension file]

compile :: Bool -> [String] -> MaybeT IO ()
compile silent args = MaybeT $ do
    r <- if silent then do
        (r,_out,err) <- readProcessWithExitCode "ghc" args []
        -- putStrLn $ unlines $ filter ("[" `isPrefixOf`) $ lines _out
        putStrLn err
        return r
    else rawSystem "ghc" args
    case r of
        ExitSuccess -> return $ Just ()
        _ -> return Nothing
compile_file :: MaybeT IO ()
compile_file = compile True (args CompileFile file)             
compile_test :: MaybeT IO FilePath
compile_test = do
    compile False (args Make "test_tmp.hs")
    return "bin/test_tmp"
compile_all :: MaybeT IO ()
compile_all = compile False (args Make "test.hs")
run_test :: FilePath -> MaybeT IO ()
run_test fp = lift $ void $ rawSystem fp []

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
    runMaybeT $ do
        compile_file
        compile_test 
            -- >>= run_test
        compile_all
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
