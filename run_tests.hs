module Main where

import Control.Monad.Error

import GHC.IO.Exception

import System.IO
--import System.Posix
import System.Environment
import System.Process
import Control.Concurrent

import Text.Printf

runRaw phase cmd args  = do
    c <- liftIO $ rawSystem cmd args
    case c of
        ExitSuccess -> return ()
        ExitFailure _ -> throwError ("phase '" ++ phase ++ "' failed")

run phase cmd  = do
    c <- liftIO $ system cmd
    case c of
        ExitSuccess -> return ()
        ExitFailure _ -> throwError ("phase '" ++ phase ++ "' failed")

general = do
        c0 <- rawSystem "ghc" ["test.hs", "--make"] 
        c1 <- case c0 of
            ExitSuccess -> do
                c3 <- rawSystem "ghc" ["continuous.hs", "--make"]
                c4 <- rawSystem "ghc" ["verify.hs", "--make"]
                c5 <- rawSystem "ghc" ["periodic.hs", "--make"]
                c6 <- rawSystem "ghc" ["compile.hs", "--make"]
                c7 <- rawSystem "ghc" ["run_tests.hs", "--make"]
                return $ foldl success ExitSuccess [c3,c4,c5,c6,c7]
            ExitFailure _ -> return c0
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
                c1 <- system "./test > result.txt"
                system "echo \"Lines of Haskell code:\" >> result.txt"
                system "wc -l $(git ls-files | grep '.*\\.hs$') | sort -r | head -n 6 >> result.txt"
                c2 <- rawSystem "cat" ["result.txt"]
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
        c0 <- rawSystem "ghc" ["test_tmp.hs", "--make"]
        case c0 of
            ExitSuccess -> do
                putStrLn "Running test ..."
                hFlush stdout
                void $ system "./test_tmp"
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

main = do
    xs <- getArgs
    case xs of
        []    -> general >> return ()
        [x]   -> specific x Nothing
        [x,y] -> specific x $ Just y
        _   -> putStrLn "usage: run_test [module_name [function_name]]"
    