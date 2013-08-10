module Main where

import Control.Concurrent
import Control.Monad
import Control.Monad.State

import Data.Map as M 
    ( Map,lookup
    , empty,union
    , fromList,insert 
    )
import Document.Document

import System.Console.GetOpt
import System.Directory
import System.Environment
import System.IO
--import System.Posix

import Text.Printf

import UnitB.AST
import UnitB.PO

import Z3.Z3

monitor :: (Monad m, Eq s) 
        => m s -> m () 
        -> m () -> m ()
monitor measure delay act = do
    t <- measure
    runStateT (
        forever (do
            t0 <- get
            t1 <- lift measure
            if t0 == t1
                then return ()
                else do 
                    put t1
                    lift act
            lift delay)) t
    return ()

data Params = Params
        { path :: FilePath
        , verbose :: Bool
        , continuous :: Bool
        , pos :: Map Label (Map Label (Bool,ProofObligation))
        }

check_one m = do
        param <- get
        let p = M.lookup (_name m) $ pos param
        let po = maybe empty id p
        (po,s,n)    <- lift $ verify_changes m po
        put (param { pos = insert (_name m) po $ pos param })
        return (n,"> machine " ++ show (_name m) ++ ":\n" ++ s)

clear = do
    param <- get
    if continuous param 
        then lift $ putStr $ take 40 $ cycle "\n"
        else return ()

check_file = do
        param <- get
        let m = pos param
        let { p ln = verbose param || take 4 ln /= "  o " }
--        let f (n,xs) = unlines (filter p (lines xs) ++ ["Redid " ++ show n ++ " proofs"])
        r <- lift $ parse_machine $ path param
        case r of
            Right ms -> do
                xs <- forM ms check_one
                clear
                forM_ xs (\(n,xs) -> lift $ do
                    forM_ (filter p $ lines xs) 
                        putStrLn
                    putStrLn ("Redid " ++ show n ++ " proofs"))
            Left xs -> do
                clear
                lift $ forM_ xs (\(x,i,j) -> 
                    printf "error (%d,%d): %s\n" i j x)

data Option = Verbose | Continuous
    deriving Eq

options :: [OptDescr Option]
options =
    [ Option ['V'] ["verbose"] (NoArg Verbose) 
            "display all successful proof obligations" 
    , Option ['c'] ["continuous"] (NoArg Continuous) 
            "monitor input files and reverify when they change"
    ]

main = do
        rawargs <- getArgs
        let (opts,args,err) = getOpt Permute options rawargs
        case args of
            [xs] -> do
                b <- doesFileExist xs
                if b then do
                    let { param = Params 
                            { path = xs
                            , verbose = Verbose `elem` opts
                            , continuous = Continuous `elem` opts
                            , pos = empty
                            } }
                    runStateT (do
                        check_file
                        if Continuous `elem` opts then do
                            monitor
                                (lift $ getModificationTime xs)
                                (lift $ threadDelay 1000000)
                                check_file
                        else return ()) param
                    return ()
                else do
                    putStrLn ("'" ++ xs ++ "' is not a valid file")
            _ -> putStrLn $ usageInfo "usage: continuous file" options
