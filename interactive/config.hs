module Interactive.Config where

import Control.Monad

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

edit :: Int -> String -> IO ()
edit n fn
    | is_os_windows = do
            system $ "notepad++ -n" ++ show n ++ " \"" ++ fn ++ "\""
            getLine
            return ()
    | otherwise     = do
            system $ "edit +" ++ show n ++ " \"" ++ fn ++ "\" --wait"
            return ()

executable :: IsString a => String -> a
executable fn
    | is_os_windows = fromString $ fn ++ ".exe"
    | otherwise     = fromString $ fn
        
is_os_windows :: Bool
is_os_windows = "mingw" == take 5 os 

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
