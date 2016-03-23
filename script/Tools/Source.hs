module Tools.Source where

import Data.String.Utils

import System.Process

import Utilities.Config

goto_definition :: String -> String -> IO ()
goto_definition scope symbol = do
        xs <- readProcess "ghci" [scope] $ unlines 
                [ ":i " ++ symbol
                , ":q"
                , "" ]
        putStrLn $ replicate 50 '-'
        let ys    = "  \t-- Defined at "
            p x   = take (length ys) x == ys
            zs    = map (drop $ length ys) $ filter p $ lines xs
            f xs  = reverse $ take 2 $ split ":" xs 
            cmd xs = open_at (read $ xs !! 0) (xs !! 1)
        mapM_  (cmd . f) zs
