
import Control.Monad

import           Data.Char
import           Data.Graph ( SCC (..))
import           Data.List hiding ( transpose )
import           Data.List.Ordered ( sortOn )
import           Data.Map hiding ( map, split, null, filter )
import qualified Data.Map as M
import           Data.String.Utils

import System.Directory
import System.FilePath

import Utilities.Graph ( cycles )

visit path ext = do
    let f x = take 1 x /= "."
    xs <- (map (path </>) . filter f) `liftM` getDirectoryContents path
    ds <- filterM doesDirectoryExist xs
    let p x = takeExtension x `elem` ext
        fs = filter p xs
    zs <- concat `liftM` mapM (flip visit ext) ds
    return $ fs ++ zs

module_name file = do
    xs <- lines `liftM` readFile file
    let p x = take 7 x == "module "
        ys  = map (drop 7) $ filter p xs
        zs  = map (takeWhile (not . isSpace) . lstrip) ys
    return zs

import_list file mods = do
    xs <- lines `liftM` readFile file
    let p x = take 7 x == "import "
        ys  = map (drop 7) $ filter p xs
        f x = filter (`isInfixOf` x) mods
        zs  = concatMap f ys
    return zs
    
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

clusters = do
    xs <- dependency
    let f x _ = length x == 1
        g k x = length x == 1 && x /= k
    return $ M.mapWithKey (\k -> filter $ g k) $ filterWithKey f xs

edges xs = do
        (x,ys) <- toList xs
        y      <- ys
        return (intercalate "." x,intercalate "." y)

transpose xs = fromListWith (++) $ do
        (x,ys) <- toList xs
        y      <- ys
        return (y,[x])

degree xs = do
        forM_ (reverse $ sortOn snd $ toList $ M.map length xs) $ \(x,n) -> do
            putStrLn $ (intercalate "." x) ++ ": " ++ show n
        
main = do
        xs <- clusters
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
        print $ xs' ! "Document"
        print $ xs' ! "UnitB"
        
is_cycle (CyclicSCC _) = True
is_cycle _ = False
    