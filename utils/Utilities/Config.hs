module Utilities.Config where

import Control.Monad

import Data.String

import System.Directory
import System.FilePath
import System.Info
import System.Process

data EditorOption = EditorOpt 
    { line :: Maybe Int
    , file :: String
    , wait :: Bool
    }

homeSettingPath :: IO FilePath
homeSettingPath = do
    home <- getHomeDirectory
    return $ home </> "Literate Unit-B"

editFile :: String -> EditorOption
editFile fn = EditorOpt Nothing fn False

notepadpp :: EditorOption -> IO ()
notepadpp (EditorOpt ln fn w) = do
        system $ "notepad++ \"" ++ first ++ "\" " ++ fn
        when w $ getLine >> return ()
    where
        first = maybe "" (("-n " ++) . show) ln

textmate :: EditorOption -> IO ()
textmate (EditorOpt ln fn w) = do
        system $ "mate " ++ first ++ " \"" ++ fn ++ "\" " ++ second
        return ()
    where
        first = maybe "" (("-l " ++) . show) ln
        second = if w then "--wait" else ""

textwrangler :: EditorOption -> IO ()
textwrangler (EditorOpt ln fn w) = do
        system $ "edit " ++ first ++ " \"" ++ fn ++ " \"" ++ second
        return ()
    where
        first = maybe "" (("+" ++) . show) ln
        second = if w then "--wait" else ""

sublimetext :: EditorOption -> IO ()
sublimetext (EditorOpt ln fn w) = do
        system $ "subl \"" ++ fn ++ first ++ "\" " ++ second
        return ()
    where
        first = maybe "" ((":" ++) . show) ln
        second = if w then "--wait" else ""

editor :: EditorOption -> IO ()
editor 
    | is_os_windows = notepadpp 
    | otherwise     = sublimetext

edit :: Int -> String -> IO ()
edit n fn = editor cmd
    where
        cmd = (editFile fn) { line = Just n, wait = True }

open_at :: Int -> String -> IO ()
open_at n fn = editor cmd
    where
        cmd = (editFile fn) { line = Just n }

diff :: String -> String -> IO ()
diff file1 file2
    | is_os_windows = do
            system ("fc " ++ quote file1 ++ " " ++ quote file2)
            getLine
            return ()
    | otherwise     = do
            system ("twdiff " ++ quote file1 ++ " " ++ quote file2 ++ " --wait")
            return ()

quote :: String -> String
quote xs = "\"" ++ xs ++ "\""

executable :: IsString a => String -> a
executable fn
    | is_os_windows = fromString $ fn ++ ".exe"
    | otherwise     = fromString $ fn
        
is_os_windows :: Bool
is_os_windows = "mingw" == take 5 os 
