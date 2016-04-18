#!/usr/bin/env cabal exec runhaskell
module Main where

import Control.Monad

import           Data.Char
import           Data.Graph ( SCC (..))
import           Data.List hiding ( transpose )
import           Data.Map hiding ( map, split, null, filter )
import qualified Data.Map as M
import           Data.String.Utils

import Utilities.Directory
import Utilities.Graph ( cycles )

module_name :: FilePath -> IO [String]
module_name file = do
    xs <- lines `liftM` readFile file
    let p x = take 7 x == "module "
        ys  = map (drop 7) $ filter p xs
        zs  = map (takeWhile (not . isSpace) . lstrip) ys
    return zs

import_list :: FilePath -> [String] -> IO [String]
import_list file mods = do
    xs <- lines `liftM` readFile file
    let p x = take 7 x == "import "
        ys  = map (drop 7) $ filter p xs
        f x = filter (`isInfixOf` x) mods
        zs  = concatMap f ys
    return zs
    
dependency :: IO (Map [String] [[String]])
dependency = do
        xs   <- visit "." [".hs", ".lhs"]
        mods <- mapM module_name xs
        imps <- mapM (flip import_list $ concat mods) xs
        rs   <- concat `liftM` zipWithM (\x' y' -> do
            let is_test xs = "test" `isInfixOf` map toLower xs
                -- h k x = not (is_test k) && not (is_test x)
                x   = filter (not . is_test) x'
                y   = filter (not . is_test) y'
                f x = -- map (intercalate ".") $ 
                        filter (not . null) $ inits $ split "." x
            case x of
                [] -> return []
                x:_ -> return $ map (\x -> (x,nub $ concatMap f y)) $ f x
            ) mods imps
        return $ M.map nub $ fromListWith (++) rs

within :: String -> Map [String] [[String]] -> Map [String] [[String]] 
within k xs = M.map (map f . filter p) ys
    where
        ys :: Map [String] [[String]]
        ys = mapKeys f $ M.filterWithKey (const . p) xs
        p x = take 1 x == [k] && length x > 1
        f x = drop 1 x
    
clusters :: IO (Map [String] [[String]])
clusters = do
        xs <- dependency
        let f x _ = length x == 1
            g k x = length x == 1 && x /= k
        return $ M.mapWithKey (\k -> filter $ g k) $ filterWithKey f xs

edges :: Map [String] [[String]] -> [(String, String)]
edges xs = do
        (x,ys) <- toList xs
        y      <- ys
        return (intercalate "." x,intercalate "." y)

transpose :: Ord a => Map a [a] -> Map a [a]
transpose xs = fromListWith (++) $ (zip (keys xs) $ repeat []) ++ do
        (x,ys) <- toList xs
        y      <- ys
        return (y,[x])

degree :: Map [String] [[String]] -> IO ()
degree xs = do
        forM_ (reverse $ sortOn snd $ toList $ M.map length xs) $ \(x,n) -> do
            putStrLn $ (intercalate "." x) ++ ": " ++ show n
        
main :: IO ()
main = do
        -- xs <- clusters
        xs <- within "Logic" `liftM` dependency
        putStrLn "> Clusters:"
        forM_ (map (intercalate ".") $ keys xs) putStrLn
        putStrLn "> Cycles:"
        print $ filter is_cycle $ cycles $ edges xs
        putStrLn "> Out degrees:"
        degree xs
        putStrLn "> In degrees:"
        let ys = transpose xs
        degree ys
        let xs' = M.mapKeys (intercalate ".") $ M.map (map $ intercalate ".") xs
            -- ys' = M.mapKeys (intercalate ".") $ M.map (map $ intercalate ".") ys
        print $ xs' ! "Tactics"

is_cycle :: SCC t -> Bool
is_cycle (CyclicSCC _) = True
is_cycle _ = False
    