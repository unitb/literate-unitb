module Config where

import Control.Monad

import Data.List.Utils 

import System.Directory 
import System.Environment 
import System.FilePath.Posix 
import System.Info

-- main = do
	-- b <- z3_installed
	-- if b then
		-- putStrLn "z3 has been found"
	-- else
		-- putStrLn "z3 hasn't been found"

is_os_windows = "mingw" == take 5 os 
		
z3_installed = do
	path <- getEnv "PATH"
	xs   <- if is_os_windows then do
			let ps = split ";" path ++ ["."]
			forM ps (doesFileExist . (`combine` "z3.exe"))
	else do
			let ps = split ":" path
			forM ps (doesFileExist . (`combine` "z3"))
	return $ or xs
