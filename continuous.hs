{-# LANGUAGE FlexibleContexts #-}
module Main where

    -- Modules
import Pipeline
import Config
	
import Document.Document

import Logic.Label

import UnitB.AST
import UnitB.PO

import Z3.Z3

    -- Libraries
import Control.Monad
import Control.Monad.State
import Control.Monad.Trans.Either 

import Data.Map as M ( elems )
import Data.Time

import qualified Data.ByteString as BS
import           Data.Map as M 
    ( Map,lookup
    , empty
    , insert
    )
import qualified Data.Serialize as Ser

import System.Console.GetOpt
import System.Directory
import System.Environment
import System.Locale

import Text.Printf

import Utilities.Syntactic

with_po_map :: StateT Params IO a -> Params -> IO ()
with_po_map act param = do
        let fn = path param ++ ".state'"
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
        let fn = file ++ ".state'"
--        liftIO $ Ser.dump_pos file p
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
        , pos :: Map Label (Map Label (Bool,Sequent))
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
        let { p ln = verbose param || take 4 ln /= "  o " }
        r <- liftIO $ runEitherT $ do
            s <- EitherT $ parse_system $ path param
            lift $ produce_summaries s
            return $ M.elems $ machines s
        case r of
            Right ms -> do
                xs <- forM ms check_one
                clear
                forM_ xs $ \(n,xs) -> liftIO $ do
                    forM_ (filter p $ lines xs) 
                        putStrLn
                    putStrLn $ "Redid " ++ show n ++ " proofs"
            Left xs -> do
                clear
                forM_ xs (\(Error x (LI _ i j)) -> liftIO $ 
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

main :: IO ()
main = do
        rawargs <- getArgs
        let (opts,args,_) = getOpt Permute options rawargs
        case args of
            [xs] -> do
                b1 <- doesFileExist xs
                b2 <- z3_installed
                if b1 && b2 then do
                    let { param = Params 
                            { path = xs
                            , pos = empty
                            , verbose    = Verbose `elem` opts
                            , continuous = Continuous `elem` opts
                            } }
                    if continuous param then do
                    	run_pipeline xs
                    	return ()
                    else
                    	with_po_map (do
                    		check_file
                    		dump_pos) param
                    -- with_po_map (do
                        -- check_file
                        -- dump_pos
                        -- if continuous param 
                        -- then do
                            -- monitor
                                -- (liftIO $ getModificationTime xs)
                                -- (liftIO $ threadDelay 1000000)
                                -- (do check_file
                                    -- dump_pos)
                        -- else return ()) param
                    return ()
                else if not b2 then
                    putStrLn ("a 'z3' executable hasn't been found in the path ")
                else
                    putStrLn ("'" ++ xs ++ "' is not a valid file")
            _ -> putStrLn $ usageInfo "usage: continuous file [options]" options
