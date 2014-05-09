
import Interactive.Config

import System.Directory

main :: IO ()
main = do
    b <- doesFileExist "compile_errors.txt"
    if b then do
        xs <- readFile "compile_errors.txt"
        mapM_ (\x -> uncurry edit $ read x) 
              (filter (not . null) $ lines xs)
    else putStrLn "file does not exist"
            
        