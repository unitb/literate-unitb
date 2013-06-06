module Tests.UnitTest where

import Control.Monad

import Data.IORef   

import System.IO
import System.IO.Unsafe

data TestCase = forall a . Show a => Case String (IO a) a

diff xs ys = p6
    where
        p0 = take (length p7 - 3) p7
        p1 = drop 3 p8
        p7 = longest_prefix xs ys
        p8 = longest_suffix xs ys
        p2 = p0 ++ "|___|" ++ p1
        m  = length p0
        n  = length p1
        p3 = map ("> " ++) $ lines $ quote $ drop m $ take (length xs - n) xs
        p4 = map ("< " ++) $ lines $ quote $ drop m $ take (length ys - n) ys
        p5 = unlines $ interleave p3 p4
        p6 = p2 ++ "\n\nComparison:[\n" ++ p5 ++ "]"

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
test_cases xs = test_suite_string $ map f xs 
    where
        f (Case x y z) = (x, (do a <- y ; return $ show a), show z)

test_suite_string :: [(String, IO String, String)] -> IO Bool
test_suite_string xs = do
        n  <- readIORef margin
        let bars = concat $ take n $ repeat "| "
        let putLn xs = putStr $ unlines $ map (bars ++) $ lines xs 
        writeIORef margin (n+1)
        xs <- forM xs (\(x,y,z) -> do
            putLn ("+- " ++ x)
            r <- y
            if (r == z)
                then return True
                else do
                    putLn $ diff r z
                    return False )
        let x = length xs
        let y = length $ filter id xs
        writeIORef margin n
        putLn ("[ Success: " ++ show y ++ " / " ++ show x ++ " ]")
        return (and xs)
