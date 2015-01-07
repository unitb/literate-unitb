
import Control.Concurrent

import Control.Monad

-- import Data.List.Utils

import System.Directory
import System.Environment
import System.Exit
-- import System.FilePath
import System.Process

wait :: IO Bool -> IO ()
wait cond = do
    b <- cond 
    unless b $ do
        threadDelay 250000
        wait cond

main :: IO ()
main = do
    xs <- getArgs
    -- path <- split ":" `liftM` getEnv "PATH"
    -- print path
    -- ghc_make <- filterM doesFileExist $ map (++ "ghc-make") path
    let file = xs !! 0
        path = xs !! 1
        inf  = "interface"
        errFile  = xs !! 2
    -- home <- getEnv "HOME"
    -- system "bash" [home </> ".profile"]
    setCurrentDirectory path
    (r,_out,err) <- readProcessWithExitCode "ghc"
        [ "-i" ++ inf
        , "-c",file
        , "-W", "-fwarn-missing-signatures"
        , "-fwarn-incomplete-uni-patterns"
        , "-fwarn-missing-methods"
        , "-fwarn-tabs", "-Werror"] ""
    putStr err
    if r == ExitSuccess then do
        putStrLn "File ok"
        -- rawSystem "ghc-make" 
        --     [ "ghc-make", "-j4"
        --     , "test.hs"
        --     , "-o", "bin/test"
        --     , "-odir", "bin"
        --     , "-hidir", "interface"
        --     , "-Wall"
        --     , "-Werror"
        --     , "-fno-warn-name-shadowing"
        --     , "-fno-warn-orphans"
        --     , "-fno-warn-type-defaults"
        --     , "-fno-warn-unused-do-bind"
        --     , "-threaded" ]
        wait (liftM (not . null) $ readFile errFile)
        readFile errFile >>= putStrLn
        -- return ()
    else return ()
    -- putStrLn inf
    -- mapM_ putStrLn xs
    -- putStrLn "allo"
