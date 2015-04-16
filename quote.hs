#!/usr/bin/env runhaskell

import Control.Monad

import System.Environment
import System.Process

escape :: String -> String
escape xs = concatMap f xs
    where
        f '\t' = "\\t"
        f '\\' = "\\\\"
        f x    = [x]

main :: IO ()
main = do
        fn <- getArgs
        case fn of
            [fn] -> do 
                lns <- (map escape . drop 1 . lines) 
                    `liftM` readFile fn
                let n = length lns - 2
                putStrLn $ "    [ \"" ++ (lns !! 0) ++ "\""
                forM_ (take n $ drop 1 lns) $ \ln -> do
                    putStrLn $ "    , \"" ++ ln ++ "\""
                putStrLn "    ]"
                system $ "runhaskell find_case.hs " ++ fn
                return ()
            _ -> putStrLn "usage: quote file"
