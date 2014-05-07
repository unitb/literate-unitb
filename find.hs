
import Data.String.Utils

import System.Environment
import System.Process

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
                    cmd xs = "edit +" ++ xs !! 0 ++ " \"" ++ xs !! 1 ++ "\" --wait"
                mapM_  (system . cmd . f) zs
                -- return ()
            _ -> return ()
            