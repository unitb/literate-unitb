#!/usr/bin/env cabal exec runhaskell
{-# LANGUAGE OverloadedStrings #-}
module Main where

import Tools.BuildSystem

import Control.Concurrent

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Either
import Control.Monad.Trans.State

import Data.Char
import Data.String

import Shelly hiding ( get, put, (</>), liftIO )

import System.Directory
import System.FilePath
-- import System.Timeout
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

repeatWhile :: (Monad m) => m Bool -> m ()
repeatWhile m = do
    b <- m
    if b 
        then repeatWhile m
        else return ()

data Event = Timeout | Line String
    deriving Eq
        
keyboard :: MVar Event -> IO ()
keyboard v = forever $ do
        xs <- getLine
        putMVar v $ Line xs

timeout :: MVar () -> MVar Event -> IO ()
timeout start v = forever $ do
        () <- takeMVar start
        threadDelay $ microseconds retry_interval
        putMVar v $ Timeout
        
main :: IO ()
main = do
    delay <- newEmptyMVar
    waitv <- newEmptyMVar
    createDirectoryIfMissing True "bin"
    forkIO $ keyboard waitv
    forkIO $ timeout delay waitv
    let wait = do
            x <- tryTakeMVar waitv
            maybe (do
                putMVar delay ()
                takeMVar waitv)
                return
                x
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
                                bin_dir  = "./bin"
                                inf_dir  = "./interface"
                                main_o :: IsString a => a
                                main_o   = fromString $ bin_dir </> "Main.o"
                                obj_file = bin_dir </> addExtension (dropExtension src_file) ".o"
                                args =  [ "--make"
                                        , "-W", "-fwarn-missing-signatures"
                                        , "-fwarn-incomplete-uni-patterns"
                                        , "-fwarn-missing-methods"
                                        , "-fwarn-tabs"
                                        -- , "-v2"
                                        , "-Werror", "-rtsopts"
                                        , "-hidir", inf_dir
                                        -- , "-osuf", "_" ++ dropExtension (head x)
                                        , "-o", bin_dir </> dropExtension (head x)
                                        , "-fbreak-on-error"
        --                                , "-prof", "-caf-all", "-auto-all", "-O2"
                                              -- these are usable with +RTS -p
                                        , "-odir", bin_dir]
                            b <- doesFileExist src_file
                            if b then do
                                b <- doesFileExist obj_file
                                when b $
                                    void $ shelly $ do
                                        mv (fromText $ fromString $ obj_file) 
                                            $ fromText main_o
                                r <- readProcessWithExitCode 
                                            "ghc" 
                                            (x ++ args) ""
                                -- putStr out
                                -- putStr err
                                -- hFlush stdout
                                b  <- doesFileExist main_o
                                when b $
                                    void $ shelly $ do
                                        mv (fromText main_o)
                                            $ fromText $ fromString obj_file
                                return r
                            else return (ExitSuccess,"","")
                putStr "compiling..."
                hFlush stdout
                writeFile "ghc_errors.txt" []
                rs <- g $ runEitherT $ mapM compile 
                    [ ["periodic.hs"]
                    , ["compile.hs"]
                    --, ["open_errors.hs","-threaded"]
                    --, ["find.hs"]
                    --, ["diff_fail.hs"]
                    --, ["modulestruct.hs"]
                    --, ["find_case.hs","-threaded"]
                    , ["test.hs","-threaded"]
                    , ["continuous.hs","-threaded","-O2"]
                    , ["extract_z3.hs"]
                    --, ["verify.hs"]
                    , ["run_tests.hs","-threaded"]
                    , ["test_tmp.hs","-threaded"] ]
                clearScreen
                hFlush stdout
                let (cs,xs,yss) = unzip3 rs
                    c = foldl success ExitSuccess cs
                    ys = concat yss
                putStr (take 60 $ cycle "\b") 
                putStr $ concat xs
                putStr ys 
                putStrLn $ (take 60 $ cycle "\b") ++ show c ++ "       "
                let fnames =    map (break (== ':')) $ 
                                    -- 
                                filter (any isLetter . (take 1)) $      
                                    -- to keep only the first line of each error
                                    -- messages
                                takeWhile ((/= "<") . (take 1)) $     
                                    -- in order to break after the 
                                    -- <no location info> note in the error 
                                    -- messages
                                lines ys
                    lno  = map (takeWhile (/= ':') . drop 1 . snd) fnames
                    is_nb x = case reads x :: [(Int,String)] of
                                [(_,"")] -> True
                                _ -> False
                    cmds = map (\(ln,fn) -> "(" ++ show fn ++ ", " ++ ln ++ ")") $ 
                                filter (is_nb . fst) $
                                zip lno $ map fst fnames
                writeFile "ghc_errors.txt" (unlines $ lines ys ++ ["done"])
                writeFile "compile_errors.txt" $ 
                    unlines (reverse cmds)
                xs <- getDirectoryContents "bin"
                forM_ (filter ((`elem` ["",".exe"]) . takeExtension) xs) $ \x -> do
                    b <- doesFileExist $ "bin" </> x
                    when b $ do
                        shelly $ cp (fromString $ "bin" </> x) "."
                hFlush stdout
                return ys
            lift $ put ys
        else return ()
        ys <- lift $ get
        liftIO $ do
            xs <- wait
            if xs == Line "less" then do
                writeFile "errors.txt" ys
                pc <- runCommand "less errors.txt"
                void $ waitForProcess pc
            else if xs == Line "quit" then do
                t <- myThreadId
                killThread t
            else return ()
--            delay (microseconds retry_interval)
        return True
    where
        success ExitSuccess ExitSuccess = ExitSuccess
        success _ _                     = ExitFailure 0
