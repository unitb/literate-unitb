
import Control.Concurrent

import Control.Monad

import Data.List
-- import Data.List.Utils

import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import System.Process

import Text.Printf

_wait :: IO Bool -> IO ()
_wait cond = do
    b <- cond 
    unless b $ do
        threadDelay 250000
        _wait cond

_main :: IO ()
_main = do
    xs <- getArgs
    -- path <- split ":" `liftM` getEnv "PATH"
    -- print path
    -- ghc_make <- filterM doesFileExist $ map (++ "ghc-make") path
    let file = xs !! 0
        path = xs !! 1
        inf  = "interface"
        errFile  = xs !! 2
    -- home <- getEnv "HOME"
    -- system "bash" [home </> ".profile"]
    setCurrentDirectory path
    (r,_out,err) <- readProcessWithExitCode "ghc"
        [ "-i" ++ inf
        , "-c",file
        , "-W", "-fwarn-missing-signatures"
        , "-fwarn-incomplete-uni-patterns"
        , "-fwarn-missing-methods"
        , "-fwarn-tabs", "-Werror"] ""
    putStr err
    if r == ExitSuccess then do
        putStrLn "File ok"
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
        _wait (liftM (not . null) $ readFile errFile)
        readFile errFile >>= putStrLn
        -- return ()
    else return ()
    -- putStrLn inf
    -- mapM_ putStrLn xs
    -- putStrLn "allo"

data CompileMode = Make | CompileFile

main :: IO ()
main = do
    xs <- getArgs
    -- path <- split ":" `liftM` getEnv "PATH"
    -- print path
    -- ghc_make <- filterM doesFileExist $ map (++ "ghc-make") path
    let file = xs !! 0
        _o_file = replaceExtension file ".o"
        path = xs !! 1
        inf  = "interface"
        bin  = "bin"
        _errFile  = xs !! 2
        args opt file = 
                [ flag,file
                , "-j8"
                , "-odir" ++ bin
                , "-i" ++ inf
                , "-W", "-fwarn-missing-signatures"
                , "-fwarn-incomplete-uni-patterns"
                , "-fwarn-missing-methods"
                , "-threaded"
                , "-fwarn-tabs", "-Werror"
                -- , "-v"
                ]
            where
                flag = case opt of 
                            CompileFile -> "-c"
                            Make        -> "--make"
    -- home <- getEnv "HOME"
    -- system "bash" [home </> ".profile"]
    setCurrentDirectory path
    -- printf "%s\n" path
    -- putStrLn $ intercalate " " $ "ghc" : (args CompileFile file)
    (r,_out,err) <- readProcessWithExitCode "ghc"
        (args CompileFile file) ""
    putStr err
    if r == ExitSuccess then do
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
        rawSystem "ghc" (args Make "test.hs")
        -- wait (liftM (not . null) $ readFile errFile)
        -- readFile errFile >>= putStrLn
        return ()
    else return ()
    -- putStrLn inf
    -- mapM_ putStrLn xs
    -- putStrLn "allo"
