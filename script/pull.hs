module Main where

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Maybe

import System.Directory
import System.Exit
import System.FilePath
import System.Process

liftS :: IO ExitCode -> MaybeT IO ()
liftS cmd = MaybeT $ do
    x <- cmd
    case x of
        ExitSuccess -> return $ Just ()
        _ -> return Nothing

test_dir :: FilePath
test_dir = "literate-unitb-test"

main :: IO (Maybe ())
main = runMaybeT $ do
    source_dir <- lift $ takeFileName `liftM` getCurrentDirectory
    lift $ do
        setCurrentDirectory ".."
        ex <- doesDirectoryExist test_dir
        if ex 
            then removeDirectoryRecursive test_dir
            else return ()
        createDirectory test_dir
        setCurrentDirectory test_dir
    liftS $ rawSystem "git" ["init"]
    liftS $ rawSystem "git" ["remote","add","origin",".." </> source_dir]
    liftS $ rawSystem "git" ["pull","origin","master"]
    liftS $ rawSystem "ghc" ["test.hs","-threaded"]
    liftS $ rawSystem "runghc" ["run_tests.hs"]
    return ()
