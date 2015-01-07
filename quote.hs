#!/usr/bin/env runhaskell

import Control.Monad

import System.Environment
import System.Process

main = do
		fn <- getArgs
		case fn of
			[fn] -> do 
				lns <- (drop 1 . lines) `liftM` readFile fn
				let n = length lns - 2
				putStrLn $ "    [ \"" ++ (lns !! 0) ++ "\""
				forM_ (take n $ drop 1 lns) $ \ln -> do
					putStrLn $ "    , \"" ++ ln ++ "\""
				putStrLn "    ]"
				system $ "runhaskell find_case.hs " ++ fn
				return ()
			_ -> putStrLn "usage: quote file"
