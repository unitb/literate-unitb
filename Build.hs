module Build where

import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Reader

-- import Data.List

import System.Exit
import System.FilePath
import System.Process

data CompileMode = Make | CompileFile

type Build = MaybeT (ReaderT FilePath IO)

inf :: FilePath
inf  = "interface"
bin :: FilePath
bin  = "bin"

build :: FilePath -> Build a -> IO (Maybe a)
build path cmd = runReaderT (runMaybeT cmd) path

args :: CompileMode -> FilePath -> Build [FilePath]
args opt file = do
    path <- lift ask
    let flag = case opt of 
                    CompileFile -> ["-c",file]
                    Make        -> ["--make",file,"-o",path </> "bin" </> dropExtension file]
    return $ flag ++
        [ "-j8"
        , "-odir" ++ bin
        , "-i" ++ inf
        , "-hidir" ++ inf
        , "-W"
        , "-fwarn-missing-signatures"
        , "-fwarn-incomplete-uni-patterns"
        , "-fwarn-missing-methods"
        , "-threaded", "-fno-ignore-asserts"
        , "-fwarn-tabs", "-Werror"
        , "-package", "either-4.3"
        , "-package", "mtl-2.1.3.1"
        , "-package", "transformers-0.3.0.0"
        , "-package", "exceptions-0.6.1"
        -- , "-ddump-splices"
        , "-dynamic-too"
        -- , "-v"
        ]

compile :: Bool -> Build [String] -> Build ()
compile silent argsM = do
    args <- argsM
    MaybeT $ lift $ do
        r <- if silent then do
            (r,_out,err) <- readProcessWithExitCode "ghc" args []
            -- putStrLn $ unlines $ filter (not . ("[" `isPrefixOf`)) $ lines _out
            putStrLn err
            return r
        else rawSystem "ghc" args
        case r of
            ExitSuccess -> return $ Just ()
            _ -> return Nothing

compile_test :: Build FilePath
compile_test = do
    compile False (args Make "test_tmp.hs")
    return "bin/test_tmp"

compile_all :: Build ()
compile_all = compile False (args Make "test.hs")

compile_app :: Build ()
compile_app = compile False (args Make "continuous.hs")
