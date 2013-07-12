{-# LANGUAGE ExistentialQuantification #-} 

module Tests.UnitTest where

import Control.Exception
import Control.Monad

import Data.Char
import Data.IORef   
import Data.List
import Data.Typeable

import Prelude hiding ( catch )

import System.IO
import System.IO.Unsafe

data TestCase = 
      forall a . (Show a, Typeable a) => Case String (IO a) a
    | forall a . (Show a, Typeable a) => CalcCase String (IO a) (IO a) 
    | StringCase String (IO String) String

diff xs ys = p6
    where
        p0 = take (length p7 - 3) p7
        p1 = drop 3 p8
        p7 = longest_prefix xs ys
        p8 = longest_suffix xs ys
        p2 = unlines $ concatMap break_line $ lines (p0 ++ "|___|" ++ p1)
        m  = length p0
        n  = length p1
        p3 = map ("  > " ++) ("Actual" : (concatMap break_line $ lines $ quote $ drop m $ take (length xs - n) xs))
        p4 = map ("  < " ++) ("Expected" : (concatMap break_line $ lines $ quote $ drop m $ take (length ys - n) ys))
        p5 = unlines $ interleave p3 p4
        p6 = p2 ++ "\n\nComparison:[\n" ++ p5 ++ "]"

break_line :: String -> [String]
break_line y =  map concat (
        takel 80 x : (
            takeWhile (not . null) 
                [ takel 80 $ dropl (80*i) x  | i <- [1..] ]) )
    where
        x :: [String]
        x       = groupBy f y
        f x y   = p x == p y
        p x     = (isSpace x, isAlphaNum x)

--break_words x = groupBy f x
--    where
--        g       = groupBy f x
--        f x y   = p x == p y
--        p x     = (isSpace x, isAlphaNum x)
--        ls      = map length g
--        xs      = map sum $ tail inits ls
--        ys      = zip xs g

takel :: Int -> [[a]] -> [[a]]
takel n (x:xs)
    | n <= length x  = []
    | length x < n = x:takel (n-length x) xs
takel _ [] = []

--map $ concat

dropl :: Int -> [[a]] -> [[a]]
dropl n (x:xs)
    | n <= length x  = x:xs
    | length x < n = dropl (n-length x) xs
dropl _ [] = []

longest_prefix [] _ = []
longest_prefix _ [] = []
longest_prefix (x:xs) (y:ys)
    | x /= y    = []
    | x == y    = x : longest_prefix xs ys

longest_suffix xs ys = reverse $ longest_prefix (reverse xs) (reverse ys)

interleave [] xs = xs
interleave xs [] = xs
interleave (x:xs) (y:ys) = x:y:d : interleave xs ys
    where
        d = map (f . uncurry (==)) $ zip x y
        f True = ' '
        f False = '-'

quote [] = []
quote (x:xs)
    | x == ' '  = "_." ++ quote xs
    | x == '\t' = "\\t" ++ quote xs
    | x == '\n' = "\\n\n" ++ quote xs
    | True      = x : quote xs

margin = unsafePerformIO $ newIORef 0
 
 
test_suite :: Show a => [(String, IO a, a)] -> IO Bool
test_suite xs = test_suite_string $ map f xs 
    where
        f (x,y,z) = (x, (do a <- y ; return $ show a), show z)

test_cases :: [TestCase] -> IO Bool
test_cases xs = 
        mapM f xs >>= test_suite_string
    where
        f (Case x y z) = return (x, (do a <- y ; return $ disp a), disp z)
        f (CalcCase x y z) = do 
                r <- z
                return (x, (do a <- y ; return $ disp a), disp r)
        f (StringCase x y z) = return (x, y, z)


disp :: (Typeable a, Show a) => a -> String
disp x = maybe (show x) id (cast x)

test_suite_string :: [(String, IO String, String)] -> IO Bool
test_suite_string xs = do
        n  <- readIORef margin
        let bars = concat $ take n $ repeat "|  "
        let putLn xs = putStr $ unlines $ map (bars ++) $ lines xs 
        writeIORef margin (n+1)
        xs <- forM xs (\(x,y,z) -> do
            putLn ("+- " ++ x)
            r <- catch (do r <- y; return $ Right r) (\e -> return $ Left $ show (e :: ErrorCall))
            case r of
                Right r -> 
                    if (r == z)
                        then return True
                        else do
                            putLn $ diff r z
                            return False 
                Left m -> do
                    putLn ("   Exception:  " ++ m)
                    return False )
        let x = length xs
        let y = length $ filter id xs
        writeIORef margin n
        putLn ("+- [ Success: " ++ show y ++ " / " ++ show x ++ " ]")
        return (and xs)
