module Utilities.Directory where
 
import Control.Monad

import System.Directory
import System.FilePath

visit :: FilePath -> [String] -> IO [FilePath] 
visit path ext = do
    let f x = take 1 x /= "."
    xs <- (map (path </>) . filter f) `liftM` getDirectoryContents path
    ds <- filterM doesDirectoryExist xs
    let p x = takeExtension x `elem` ext
        fs = filter p xs
    zs <- concat `liftM` mapM (flip visit ext) ds
    return $ fs ++ zs
