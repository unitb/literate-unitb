{-# LANGUAGE FlexibleContexts #-}
module Main where

    -- Modules
import Data.Time
import Data.Time.Clock

import Document.Document

import UnitB.AST
import UnitB.PO

import Z3.Z3

    -- Libraries
import Control.Applicative ( (<|>) )
import Control.Concurrent
import Control.Monad
import Control.Monad.State

import Data.Map as M 
    ( Map,lookup
    , empty,union
    , fromList
    , insert, alter
    )

import System.Console.GetOpt
import System.Directory
import System.Environment
import System.IO
import System.Locale

import Text.Printf

liftMS :: (Monad m, Ord k) => v -> StateT v m a -> k -> StateT (Map k v) m a
liftMS y act x = do
        m <- get
        (r,y) <- lift $ runStateT act (maybe y id $ M.lookup x m)
        put (insert x y m)
        return r

monitor :: (Monad m, Eq s) 
        => m s -> m () 
        -> m () -> m ()
monitor measure delay act = do
    t <- measure
    runStateT (
        forever (do
            t0 <- get
            t1 <- lift measure
            if t0 == t1
                then return ()
                else do 
                    put t1
                    lift act
            lift delay)) t
    return ()

data Params = Params
        { path :: FilePath
        , verbose :: Bool
        , continuous :: Bool
        , pos :: Map Label (Map Label (Bool,ProofObligation))
        }

check_one :: (MonadIO m, MonadState Params m) 
          => Machine -> m (Int,String)
check_one m = do
        param <- get
        let p = M.lookup (_name m) $ pos param
        let po = maybe empty id p
        (po,s,n)    <- liftIO $ verify_changes m po
        put (param { pos = insert (_name m) po $ pos param })
        return (n,"> machine " ++ show (_name m) ++ ":\n" ++ s)

clear :: (MonadIO m, MonadState Params m) 
      => m ()
clear = do
    param <- get
    if continuous param 
        then liftIO $ putStr $ take 40 $ cycle "\n"
        else return ()

check_file :: (MonadIO m, MonadState Params m) 
           => m ()
check_file = do
        param <- get
        let m = pos param
        let { p ln = verbose param || take 4 ln /= "  o " }
        r <- liftIO $ parse_machine $ path param
        case r of
            Right ms -> do
                xs <- forM ms check_one
                clear
                forM_ xs (\(n,xs) -> liftIO $ do
                    forM_ (filter p $ lines xs) 
                        putStrLn
                    putStrLn ("Redid " ++ show n ++ " proofs"))
            Left xs -> do
                clear
                forM_ xs (\(x,i,j) -> liftIO $ 
                    printf "error (%d,%d): %s\n" i j x)
        liftIO $ putStrLn ""
        tz <- liftIO (getCurrentTimeZone)
        t  <- liftIO (getCurrentTime :: IO UTCTime)
        liftIO $ putStrLn $ formatTime defaultTimeLocale "Time: %H:%M:%S" $ utcToLocalTime tz t

data Option = Verbose | Continuous
    deriving Eq

options :: [OptDescr Option]
options =
    [ Option ['V'] ["verbose"] (NoArg Verbose) 
            "display all successful proof obligations" 
    , Option ['c'] ["continuous"] (NoArg Continuous) 
            "monitor input files and reverify when they change"
    ]

main = do
        rawargs <- getArgs
        let (opts,args,err) = getOpt Permute options rawargs
        case args of
            [xs] -> do
                b <- doesFileExist xs
                if b then do
                    let { param = Params 
                            { path = xs, pos = empty
                            , verbose = Verbose `elem` opts
                            , continuous = Continuous `elem` opts
                            } }
                    runStateT (do
                        check_file
                        if continuous param 
                        then do
                            monitor
                                (liftIO $ getModificationTime xs)
                                (liftIO $ threadDelay 1000000)
                                check_file
                        else return ()) param
                    return ()
                else do
                    putStrLn ("'" ++ xs ++ "' is not a valid file")
            _ -> putStrLn $ usageInfo "usage: continuous file" options
