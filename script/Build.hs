{-# LANGUAGE QuasiQuotes #-}
module Build where

import Control.Concurrent
import Control.Lens

import Control.Monad.RWS
import Control.Monad.Trans.Maybe

import Data.Char
import Data.List
import Data.Maybe
import Data.String.Lines

import System.Directory
import System.Exit
import System.FilePath
import System.Process

import Text.Printf.TH

data CompileMode = Make | CompileFile

data CompileFlags = CompileFlags
        { mode :: CompileMode 
        , profile :: Bool }

type Build = RWST FilePath () (FilePath,[FilePath]) (MaybeT IO)

data BuildTool = Cabal | Stack

inf :: FilePath
inf  = "interface"
bin :: FilePath
bin  = "bin"

tool :: BuildTool
tool = Cabal

build :: FilePath -> Build a -> IO (Maybe (a, FilePath, [FilePath]))
build path cmd = fmap f <$> runMaybeT (runRWST cmd path ("ghc",[]))
    where 
        f (x,(y,z),()) = (x,y,z)

args :: CompileFlags -> FilePath -> Build ()
args opt file = do
    path <- ask
    liftIO $ createDirectoryIfMissing True $ 
        path </> "bin" </> takeDirectory file
    let flag = case mode opt of 
                    CompileFile -> ["-c",file]
                    Make        
                        | profile opt -> ["--make",file,"-o",path </> "bin" </> dropExtension file ++ "_p"]
                        | otherwise   -> ["--make",file,"-o",path </> "bin" </> dropExtension file]
    _2 .= flag ++
        [ "-j8"
        , "-odir" ++ bin
        , "-i" ++ intercalate ":" [inf,"suite","src","utils","latex","logic"
                                  ,"libs/axiomatic-classes","libs/data-compressed"
                                  ,"libs/data-map-class","libs/data-packaged"
                                  ,"libs/existential","libs/generic-instances"
                                  ,"libs/invariants","libs/partial-order"
                                  ,"libs/printf-th","libs/reactive-banana-transformers"
                                  ,"libs/string-lenses","libs/unfoldable"
                                  ,"libs/show-with","libs/typelist-functor"
                                  ,"libs/file-system-mockup","libs/transformer-lenses"
                                  ,"libs/bipartite-graph","libs/classy-lens-hierarchy"
                                  ,"libs/co-applicative", "libs/unitb-testing"
                                  ,"libs/lens-extra", "libs/pretty-printable"
                                  ]
        , "-hidir" ++ inf
        , "-W", "-O0"
        , "-XTupleSections"
        , "-XDeriveFunctor"
        , "-XDeriveGeneric"
        , "-XQuasiQuotes"
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
        , "-XImplicitParams"
        --, "-D__HASHED_KEYS__"
        -- , "-D__HASH_MAP__"
        -- , "-D__HASH_MAP_LAZY__"
        -- , "-D__PACKAGED_NAMES__"
        , "-fwarn-missing-signatures"
        , "-fwarn-incomplete-uni-patterns"
        , "-fwarn-missing-methods"
        -- , "-fwarn-orphans"
        , "-threaded", "-fno-ignore-asserts"
        , "-fwarn-tabs", "-Werror"
        , "-ignore-package", "literate-unitb"
        -- , "-package", "either-4.3"
        -- , "-package", "mtl-2.1.3.1"
        -- , "-package", "QuickCheck"
        -- , "-package", "transformers-0.3.0.0"
        -- , "-package", "exceptions-0.6.1"
        -- , "-ddump-splices"
        -- , "-fforce-recomp"
        -- , "-O2"
        ] ++ if profile opt 
            then [ "-osufp_o", "-hisufp_hi"
                 , "-prof", "-O2"
                 , "-fhpc"
                 , "-caf-all"
                 -- , "-fforce-recomp"
                 , "-auto-all"
                 , "-rtsopts" ]
            else [ "-dynamic-too" ]
        -- , "-v"

showBuildCommand :: FilePath -> Build () -> IO (Maybe String)
showBuildCommand fp cmd = fmap (fmap $ view _1) $ build fp $ do
    cmd 
    (ghc,args) <- get
    return $ showCommandForUser ghc args

compile :: Bool -> Build () -> Build ()
compile silent argsM = do
    argsM
    (ghc,args) <- get
    lift $ MaybeT $ do
        r <- if silent then do
            (r,_out,err) <- readProcessWithExitCode ghc args []
            -- putStrLn $ unlines $ filter (not . ("[" `isPrefixOf`)) $ lines _out
            putStrLn $ removeAtLineNumber err
            return r
        else rawSystem ghc args
        threadDelay 10
        case r of
            ExitSuccess -> return $ Just ()
            _ -> return Nothing

removeAtLineNumber :: String -> String
removeAtLineNumber = traverseLines.spanIso isSpace._2 %~ dropKW "at "
    where
        dropKW kw xs | kw `isPrefixOf` xs = drop (length kw) xs
                     | otherwise          = xs

newtype CabalTarget = CabalTarget FilePath

returnIf :: a -> ExitCode -> Build a
returnIf x ExitSuccess = return x
returnIf _ (ExitFailure _) = mzero

liftIOWithExit :: IO ExitCode -> Build ()
liftIOWithExit cmd = do
        r <- liftIO cmd
        returnIf () r

toolBuild :: (String -> [String] -> r) -> [String] -> r
toolBuild f args = case tool of
  Cabal -> f "cabal" $ "build" : args
  Stack -> f "stack" $ "build" : args

toolExec :: (String -> [String] -> r) -> [String] -> r
toolExec f args = case tool of
  Cabal -> f "cabal" $ "run" : args
  Stack -> f "stack" $ "exec" : args

execCommand :: String -> String -> String
execCommand command outfile = toolExec (\c args -> [printf|%s %s %s > %s|] c (intercalate " " args) command outfile) []

cabal_run :: CabalTarget -> Build ()
cabal_run (CabalTarget target) = do
    liftIOWithExit $ do
        (r,_out,err) <- toolExec readProcessWithExitCode [target] []
        -- putStrLn $ unlines $ filter (not . ("[" `isPrefixOf`)) $ lines _out
        putStrLn $ removeAtLineNumber err
        return r

cabal_build :: Maybe String -> Build CabalTarget
cabal_build target = do
    liftIOWithExit $ do
        (r,_out,err) <- toolBuild readProcessWithExitCode (maybeToList target) []
        -- putStrLn $ unlines $ filter (not . ("[" `isPrefixOf`)) $ lines _out
        putStrLn $ removeAtLineNumber err
        return r
    return $ CabalTarget $ fromMaybe "" target

enableProfiling :: FilePath -> Build FilePath
enableProfiling target = do
    compile False (args (CompileFlags Make True) target)
    return $ "bin" </> dropExtension target ++ "_p"

make :: FilePath -> Build FilePath
make target = do
    compile False (args (CompileFlags Make False) target)
    return $ "bin" </> dropExtension target

compile_test :: Build FilePath
compile_test = make "suite/test_tmp.hs"

profile_test :: Build FilePath
profile_test = do
    make "suite/test_tmp.hs"
    enableProfiling "suite/test_tmp.hs"

compile_all :: Build FilePath
compile_all = make "suite/test.hs"

compile_app :: Build FilePath
compile_app = make "app/continuous.hs"

profile_app :: Build FilePath
profile_app = do 
    make "app/continuous.hs"
    enableProfiling "app/continuous.hs"
