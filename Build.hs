module Build where

import Control.Concurrent
import Control.Lens

import Control.Monad.RWS
import Control.Monad.Trans.Maybe

import System.Exit
import System.FilePath
import System.Process

data CompileMode = Make | CompileFile

type Build = RWST FilePath () (FilePath,[FilePath]) (MaybeT IO)

inf :: FilePath
inf  = "interface"
bin :: FilePath
bin  = "bin"

build :: FilePath -> Build a -> IO (Maybe (a, FilePath, [FilePath]))
build path cmd = fmap f <$> runMaybeT (runRWST cmd path ("ghc",[]))
    where 
        f (x,(y,z),()) = (x,y,z)

args :: CompileMode -> FilePath -> Build ()
args opt file = do
    path <- ask
    let flag = case opt of 
                    CompileFile -> ["-c",file]
                    Make        -> ["--make",file,"-o",path </> "bin" </> dropExtension file]
    _2 .= flag ++
        [ "-j8"
        , "-odir" ++ bin
        , "-i" ++ inf
        , "-hidir" ++ inf
        , "-W"
        , "-XTupleSections"
        , "-XDeriveFunctor"
        , "-XDeriveGeneric"
        , "-XDeriveFoldable"
        , "-XRankNTypes"
        , "-XMultiParamTypeClasses"
        , "-XGeneralizedNewtypeDeriving"
        , "-XTemplateHaskell"
        , "-XFlexibleContexts"
        , "-XFlexibleInstances"
        , "-XDeriveDataTypeable"
        , "-XTypeSynonymInstances"
        , "-XDefaultSignatures"
        , "-XDeriveTraversable"
        , "-XFunctionalDependencies"
        , "-fwarn-missing-signatures"
        , "-fwarn-incomplete-uni-patterns"
        , "-fwarn-missing-methods"
        --, "-fwarn-orphans"
        , "-threaded", "-fno-ignore-asserts"
        , "-fwarn-tabs", "-Werror"
        --, "-package", "either-4.3"
        --, "-package", "mtl-2.1.3.1"
        --, "-package", "QuickCheck"
        --, "-package", "transformers-0.3.0.0"
        --, "-package", "exceptions-0.6.1"
        -- , "-ddump-splices"
        , "-dynamic-too"
        -- , "-v"
        ]

compile :: Bool -> Build () -> Build ()
compile silent argsM = do
    argsM
    (ghc,args) <- get
    lift $ MaybeT $ do
        r <- if silent then do
            (r,_out,err) <- readProcessWithExitCode ghc args []
            -- putStrLn $ unlines $ filter (not . ("[" `isPrefixOf`)) $ lines _out
            putStrLn err
            return r
        else rawSystem ghc args
        threadDelay 10
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