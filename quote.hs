#!/usr/bin/env runhaskell

import Control.Monad

import System.Environment
import System.Process

import Utilities.Partial

escape :: String -> String
escape xs = concatMap f xs
    where
        f '\t' = "\\t"
        f '\\' = "\\\\"
        f '\"' = "\\\""
        f x    = [x]

allBut :: Int -> [a] -> [a]
allBut k xs = take (n - k) xs
    where
        n = length xs

main :: IO ()
main = do
        fn <- getArgs
        case fn of
            [fn] -> do 
                lns <- (map escape . drop 1 . lines) 
                    `liftM` readFile fn
                let lns' = drop 1 lns
                putStrLn $ "    [ \"" ++ (lns' ! 0) ++ "\""
                forM_ (allBut 1 $ drop 1 lns') $ \ln -> do
                    putStrLn $ "    , \"" ++ ln ++ "\""
                putStrLn "    ]"
                --system $ "runhaskell find_case.hs " ++ fn
                rawSystem "subl" [drop 2 $ head lns]
                return ()
            _ -> putStrLn "usage: quote file"
