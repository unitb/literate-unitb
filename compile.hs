module Main where

import BuildSystem

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Either
import Control.Monad.Trans.State

import System.Timeout
import System.Console.ANSI
import System.Exit
import System.IO 
import System.Process

interval :: Time
interval = Minutes 1

retry_interval :: Time
retry_interval = Seconds 1

data Time = Minutes Int | Seconds Int

microseconds :: Time -> Int
microseconds (Minutes x) = x * 60000000
microseconds (Seconds x) = x * 1000000

--break_errs xs = concatMap f $ lines xs
--    where
--        f [] = [Just []]
--        f ys@(x:xs)
--            | isAlpha x       = [Nothing, Just ys]
--            | not $ isAlpha x = [Just ys]


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
                clearScreen
                let f cmd = do
                        x <- cmd
                        case x of 
                            (ExitSuccess,_,_) -> return $ Right x
                            (ExitFailure _,_,_) -> return $ Left x 
                    g cmd = do
                        x <- cmd
                        return $ either (:[]) id x
                    compile x = EitherT $ f 
                                    $ readProcessWithExitCode 
                                        "ghc" 
                                        (x ++ 
                                [ "--make"
                                , "-W" --, "-fwarn-missing-signatures"
                                , "-Werror"
                                , "-hidir", "interface"
                                , "-odir", "bin"]) ""
                putStr "compiling..."
                hFlush stdout
                rs <- g $ runEitherT $ mapM compile 
                    [ ["periodic.hs"]
                    , ["compile.hs"]
                    , ["test.hs","-threaded"]
                    , ["continuous.hs","-threaded"]
                    , ["verify.hs"]
                    , ["run_tests.hs","-threaded"] ]
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
