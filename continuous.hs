module Main where

import Control.Concurrent
import Control.Monad

import Data.Map as M (lookup,empty,union,fromList)
import Document.Document

import System.Console.GetOpt
import System.Directory
import System.Environment
import System.IO
--import System.Posix

import Text.Printf

import UnitB.AST
import UnitB.PO

data Params = Params
        { path :: FilePath
        , verbose :: Bool
        , continuous :: Bool
        }

check_one pos m = do
        let { po = case M.lookup (_name m) pos of
            Just po -> po
            Nothing -> empty }
        (po,s,n)    <- verify_changes m po
        return ((n,"> machine " ++ show (_name m) ++ ":\n" ++ s), (_name m,po))

check_file param m = do
        r <- parse_machine $ path param
        case r of
            Right ms -> do
                xs <- forM ms (check_one m)
                if continuous param then
                    putStr $ take 40 $ cycle "\n"
                else return ()
                forM_ (map fst xs) (putStrLn . f)
                return (union (fromList $ map snd xs) m)
            Left xs -> do
                if continuous param then
                    putStr $ take 40 $ cycle "\n"
                else return ()
                forM_ xs (\(x,i,j) -> printf "error (%d,%d): %s\n" i j x)
                return m
    where
        f (n,xs) = unlines (filter p (lines xs) ++ ["Redid " ++ show n ++ " proofs"])
        p ln = 
            if verbose param then True
            else take 4 ln /= "  o "

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
                if b
                then do
                    let { param = Params 
                        { path = xs
                        , verbose = Verbose `elem` opts
                        , continuous = Continuous `elem` opts
                        } }
                    pos <- check_file param empty
                    if Continuous `elem` opts then do
                        t <- getModificationTime xs
                        f param xs (t, pos) 
                    else return ()
                else do
                    putStrLn ("'" ++ xs ++ "' is not a valid file")
            _ -> putStrLn $ usageInfo "usage: continuous file" options
    where
        f param xs (t0,m) = do
            threadDelay 100000
            x <- hReady stdin
            c <- if x then getChar else return ' '
            if c `elem` ['q','Q'] then return ()
            else do 
                t1 <- getModificationTime xs
                m <- if t0 /= t1 
                    then check_file param m 
                    else return m
                f param xs (t1,m) 