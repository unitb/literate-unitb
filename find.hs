
import Data.String.Utils

import Interactive.Config

import System.Environment
import System.Process

main :: IO ()
main = do
        xs <- getArgs
        case xs of
            x0:x1:_ -> do
                xs <- readProcess "ghci" [x0] $ unlines 
                        [ ":i " ++ x1
                        , ":q"
                        , "" ]
                putStrLn $ replicate 50 '-'
                let ys    = "  \t-- Defined at "
                    p x   = take (length ys) x == ys
                    zs    = map (drop $ length ys) $ filter p $ lines xs
                    f xs  = reverse $ take 2 $ split ":" xs 
                    cmd xs = edit (read $ xs !! 0) (xs !! 1)
                mapM_  (cmd . f) zs
            _ -> return ()
            