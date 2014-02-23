{-# LANGUAGE FlexibleContexts #-}
module Main where

import Interactive.Config

import Control.Monad.Error

import GHC.IO.Exception

import System.IO
--import System.Posix
import System.Environment
import System.Process

--import Control.Concurrent

import Text.Printf

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
        let compile x = readProcessWithExitCode "ghc" (x ++ 
                        [ "--make"
                        , "-W"
                        , "-Werror"
                        , "-hidir", "interface"
                        , "-odir", "bin"]) ""
        rs <- mapM compile 
            [ ["test.hs","-threaded"]
            , ["continuous.hs","-threaded"]
            , ["verify.hs"]
            , ["periodic.hs"]
            , ["compile.hs"]
            , ["run_tests.hs"] ]
        let (cs,_,xs) = unzip3 rs
        let c1 = foldl success ExitSuccess cs
        forM_ (concatMap lines xs) putStrLn
        case c1 of
            ExitSuccess -> do
                putStrLn "Running test ..."
                hFlush stdout
--                (_,hout,_,ps) <- runInteractiveCommand "./test"
--                hSetBinaryMode hout False
----                (_, Just out, _, ps) <- createProcess (shell "./test") { std_out = CreatePipe }
--                out                  <- hGetContents hout
----                (c1,out,_) <- readProcessWithExitCode "./test" [] ""
--                withFile "result.txt" WriteMode $ \h -> do
--                    (_, Just hreport, _, p2) <- createProcess 
--                        (shell "wc -l $(git ls-files | grep '.*\\.hs$') | sort -r | head -n 6")
--                            { std_out = CreatePipe }
--                    report <- hGetContents hreport
--                    let lns = lines out ++ ["Lines of Haskell code:"] ++ lines report
--                    if null out 
--                        then putStrLn "NULL" 
--                        else putStrLn "not NULL"
--                    forM_ lns $ \ln -> do
--                        putStrLn ln
--                        hPutStrLn h ln
--                        hFlush stdout
--                        hFlush h
--                    waitForProcess p2
--                c1 <- waitForProcess ps
                c1 <- p_system "test > result.txt"
                system "echo \"Lines of Haskell code:\" >> result.txt"
                system "wc -l $(git ls-files | grep '.*hs$') | sort -r | head -n 6 >> result.txt"
                rawSystem "cat" ["result.txt"]
                return c1
            ExitFailure _ -> do
                putStrLn "\n***************"
                putStrLn   "*** FAILURE ***"
                putStrLn   "***************"
                return c1
    where
        success ExitSuccess ExitSuccess = ExitSuccess
        success _ _                     = ExitFailure 0

specific :: String -> Maybe String -> IO ()
specific mod_name fun_name = do
        h <- openFile "test_tmp.hs" WriteMode
        hPrintf h test_prog mod_name
        hClose h
        c0 <- rawSystem "ghc" ["test_tmp.hs", "--make"
                                , "-W"
                                , "-Werror"
                                , "-hidir", "interface"
                                , "-odir", "bin"]
        case c0 of
            ExitSuccess -> do
                putStrLn "Running test ..."
                hFlush stdout
                void $ p_system "test_tmp"
            ExitFailure _ -> do
                putStrLn "\n***************"
                putStrLn   "*** FAILURE ***"
                putStrLn   "***************"
    where
        test_prog = unlines 
            [ "module Main where"
            , "import %s "
            , "main = " ++ fun 
            ]
        fun = case fun_name of
            Just x  -> x
            Nothing -> "test"

main :: IO ()
main = do
    xs <- getArgs
    case xs of
        []    -> general >> return ()
        [x]   -> specific x Nothing
        [x,y] -> specific x $ Just y
        _   -> putStrLn "usage: run_test [module_name [function_name]]"
    