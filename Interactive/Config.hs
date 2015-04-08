module Interactive.Config where

import Control.Monad

import Data.Char
import Data.List.Utils 
import Data.String

import System.Directory 
import System.Environment 
import System.FilePath.Posix 
import System.Info
import System.Process

-- main = do
    -- b <- z3_installed
    -- if b then
        -- putStrLn "z3 has been found"
    -- else
        -- putStrLn "z3 hasn't been found"

data EditorOption = EditorOpt 
    { line :: Maybe Int
    , file :: String
    , wait :: Bool
    }

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

z3_version :: IO (String,String)
z3_version = do
        xs <- (words . head . lines) `liftM` readProcess "z3" ["--help"] ""
        let hashcode = dropWhile (/= "hashcode") xs !! 1
            version = dropWhile (/= "[version") xs !! 1
        return (version, filter isHexDigit hashcode)


z3_installed :: IO Bool        
z3_installed = do
    path <- getEnv "PATH"
    xs   <- if is_os_windows then do
            let ps = split ";" path ++ ["."]
            forM ps (doesFileExist . (`combine` "z3.exe"))
    else do
            let ps = split ":" path
            forM ps (doesFileExist . (`combine` "z3"))
    return $ or xs
