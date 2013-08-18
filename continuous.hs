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

import qualified 
       Data.ByteString as BS
import qualified 
       Data.ByteString.Internal as BSI
import Data.Map as M 
    ( Map,lookup
    , empty,union
    , fromList
    , insert, alter
    )
import qualified
       Data.Serialize as Ser

import System.Console.GetOpt
import System.Directory
import System.Environment
import System.IO
import System.Locale

import Text.Printf

instance Ser.Serialize Label where
instance Ser.Serialize Sort where
instance Ser.Serialize Var where
instance Ser.Serialize Type where
instance Ser.Serialize Fun where
instance Ser.Serialize Def where
instance Ser.Serialize Quantifier where
instance Ser.Serialize Context where
instance Ser.Serialize Expr where
instance Ser.Serialize ProofObligation where

with_po_map act param = do
        let fn = path param ++ ".state"
        b <- doesFileExist fn
        param <- if b then do
            xs <- BS.readFile fn
            either 
                (\_ -> return param) 
                (\po -> return param { pos = po }) 
                $ Ser.decode xs
        else return param
        void $ execStateT act param

dump_pos :: MonadIO m => StateT Params m ()
dump_pos = do
        p    <- gets pos
        file <- gets path         
        let fn = file ++ ".state"
        liftIO $ BS.writeFile fn $ Ser.encode p

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
                            { path = xs
                            , pos = empty
                            , verbose = Verbose `elem` opts
                            , continuous = Continuous `elem` opts
                            } }
                    with_po_map (do
                        check_file
                        dump_pos
                        if continuous param 
                        then do
                            monitor
                                (liftIO $ getModificationTime xs)
                                (liftIO $ threadDelay 1000000)
                                (do check_file
                                    dump_pos)
                        else return ()) param
                    return ()
                else do
                    putStrLn ("'" ++ xs ++ "' is not a valid file")
            _ -> putStrLn $ usageInfo "usage: continuous file" options
