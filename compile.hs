module Main where

import Tools.BuildSystem

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Either
import Control.Monad.Trans.State

import System.Directory
import System.FilePath
import System.Timeout
import System.Console.ANSI
import System.Exit
import System.IO 
import System.Process

import Utilities.Format

interval :: Time
interval = Minutes 1

retry_interval :: Time
retry_interval = Seconds 1

data Time = Minutes Int | Seconds Int

microseconds :: Time -> Int
microseconds (Minutes x) = x * 60000000
microseconds (Seconds x) = x * 1000000

repeatWhile :: (Monad m) => m Bool -> m ()
repeatWhile m = do
    b <- m
    if b 
        then repeatWhile m
        else return ()

main :: IO ()
main = do
    flip evalStateT [] $ flip evalStateT init_state $ forever $ do
        b <- didAnythingChange
        if b then do
            ys <- liftIO $ do
--                forM_ (take 20 $ repeat "") putStrLn
                let f cmd = do
                        x <- cmd
                        case x of 
                            (ExitSuccess,_,_) -> return $ Right x
                            (ExitFailure _,_,_) -> return $ Left x 
                    g cmd = do
                        x <- cmd
                        return $ either (:[]) id x
                    compile x = EitherT $ f $ do
                            let src_file = head x
                                obj_file = addExtension (dropExtension $ src_file) "o"
                            b <- doesFileExist src_file
                            if b then do
                                b <- doesFileExist obj_file
                                when b $
                                    void $ system $ format "mv bin/{0} bin/Main.o" obj_file
                                r <- readProcessWithExitCode 
                                            "ghc" 
                                            (x ++ 
                                    [ "--make"
                                    , "-W", "-fwarn-missing-signatures"
                                    , "-Werror", "-rtsopts"
                                    , "-hidir", "interface"
                                    , "-fbreak-on-error"
    --                                , "-prof", "-caf-all", "-auto-all", "-O2"
                                          -- these are usable with +RTS -p
                                    , "-odir", "bin"]) ""
                                b <- doesFileExist "bin/Main.o"
                                when b $
                                    void $ system $ format "mv bin/Main.o bin/{0}" obj_file
                                return r
                            else return (ExitSuccess,"","")
                putStr "compiling..."
                hFlush stdout
                rs <- g $ runEitherT $ mapM compile 
                    [ ["periodic.hs"]
                    , ["compile.hs"]
                    , ["test.hs","-threaded"]
                    , ["continuous.hs","-threaded"]
                    , ["verify.hs"]
                    , ["run_tests.hs","-threaded"]
                    , ["test_tmp.hs","-threaded"] ]
                clearScreen
                hFlush stdout
                let (cs,xs,yss) = unzip3 rs
                let c = foldl success ExitSuccess cs
                let ys = concat yss
                putStr (take 60 $ cycle "\b") 
                putStr $ concat xs
                putStr ys 
                putStrLn $ (take 60 $ cycle "\b") ++ show c ++ "       "
                hFlush stdout
                return ys
            lift $ put ys
        else return ()
        ys <- lift $ get
        liftIO $ do
            xs <- timeout (microseconds retry_interval) getLine
            if xs == Just "less" then do
                writeFile "errors.txt" ys
                pc <- runCommand "less errors.txt"
                void $ waitForProcess pc
            else return ()
--            delay (microseconds retry_interval)
        return True
    where
        success ExitSuccess ExitSuccess = ExitSuccess
        success _ _                     = ExitFailure 0
