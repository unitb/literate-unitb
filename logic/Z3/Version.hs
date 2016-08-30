{-# LANGUAGE LambdaCase #-}
module Z3.Version where

import Control.Lens
import Control.Monad
import Control.Monad.Trans.Maybe
import Control.Precondition

import Data.Char
import Data.List as L
import Data.List.Utils as L
import Data.ConfigFile

import System.Directory
import System.Environment
import System.FilePath
import System.Process
import System.IO.Unsafe

import Text.Printf.TH

import Utilities.Config

check_z3_bin :: IO Bool
check_z3_bin = do
    b <- z3_installed
    if b then do
        (v,h) <- z3_version
        let versions = [ ("4.3.2","2ca14b49fe45")
                       , ("4.3.2","784307fc3001")
                       , ("4.3.2","5e72cf0123f6")
                       , ("4.4.0","0482e7fe727c")
                       , ("4.4.1","e8811748d39a")
                       , ("4.4.1","")]
        if (v,h) `elem` versions then
            return True
        else do
            putStrLn $ [printf|Expecting z3 %s\n|] $ intercalate " or\n"
                $ map (uncurry $ [printf|z3 version %s, hashcode %s|]) versions
            return False
    else do
        putStrLn ("A 'z3' executable has not been found in the path ")
        return False

z3_version :: IO (String,String)
z3_version = do
        xs <- (words . head . lines) `liftM` readProcess z3_path ["--help"] ""
        let hashcode = dropWhile (/= "hashcode") xs^?ix 1
            version = dropWhile (/= "[version") xs ! 1
        return (version, maybe "" (filter isHexDigit) hashcode)


z3_installed :: IO Bool        
z3_installed = do
    path <- getEnv "PATH"
    xs   <- if is_os_windows then do
            let ps = L.split ";" path ++ ["."]
            forM ps (doesFileExist . (`combine` "z3.exe"))
    else do
            let ps = L.split ":" path
            forM ps (doesFileExist . (`combine` "z3"))
    return $ or xs

data Z3Config = Z3Config 
    { z3c_path :: FilePath
    , z3c_timeout :: Int
    , z3c_capacity :: Int }
    deriving Show

doesFileExist' :: FilePath -> IO (Maybe FilePath)
doesFileExist' fn = do
    doesFileExist fn >>= \case 
        True  -> return $ Just fn
        False -> return $ Nothing

doFilesExist :: [FilePath]
             -> IO (Maybe FilePath)
doFilesExist fs = do
    runMaybeT $ msum $ map (MaybeT . doesFileExist') fs

z3_config :: Z3Config
z3_config = unsafePerformIO $ do
    let fn = "z3_config.conf"
    path <- getExecutablePath
    home <- homeSettingPath
    cp <- doFilesExist 
            [ fn 
            , path </> fn 
            , home </> fn ]
        >>= \case
            Just fn' -> readfile emptyCP fn'
            Nothing  -> return $ return emptyCP
    let option :: Get_C a => a -> String -> a
        option x name = fromRight x $ do
            cp <- cp
            get cp "DEFAULT" name
    return $ Z3Config
        { z3c_path = option "z3" "z3_path" 
        , z3c_timeout  = option 20 "timeout"
        , z3c_capacity = option 32 "capacity" }

z3_path :: String
z3_path = z3c_path z3_config

default_timeout :: Int
default_timeout = z3c_timeout z3_config
