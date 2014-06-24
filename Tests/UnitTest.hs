{-# LANGUAGE ExistentialQuantification #-} 
module Tests.UnitTest where

    -- Modules
import Logic.Expr
import Logic.Proof

import Z3.Z3

    -- Libraries
import Control.Exception
import Control.Monad

import           Data.Char
import           Data.IORef   
import           Data.List
import qualified Data.Map as M
import           Data.Tuple
import           Data.Typeable

import Prelude

import Utilities.Format

import System.IO
import System.IO.Unsafe

data TestCase = 
      forall a . (Show a, Typeable a) => Case String (IO a) a
    | POCase String (IO (String, M.Map Label Sequent)) String
    | forall a . (Show a, Typeable a) => CalcCase String (IO a) (IO a) 
    | StringCase String (IO String) String
    | LineSetCase String (IO String) String

diff :: [Char] -> [Char] -> [Char]
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

takel :: Int -> [[a]] -> [[a]]
takel n (x:xs)
    | n <= length x  = []
    | otherwise      = x:takel (n-length x) xs
takel _ [] = []

dropl :: Int -> [[a]] -> [[a]]
dropl n (x:xs)
    | n <= length x  = x:xs
    | otherwise      = dropl (n-length x) xs
dropl _ [] = []
 
longest_prefix :: Eq a => [a] -> [a] -> [a]
longest_prefix [] _ = []
longest_prefix _ [] = []
longest_prefix (x:xs) (y:ys)
    | x == y    = x : longest_prefix xs ys
    | otherwise = []

longest_suffix :: Eq a => [a] -> [a] -> [a]
longest_suffix xs ys = reverse $ longest_prefix (reverse xs) (reverse ys)

interleave :: [[Char]] -> [[Char]] -> [[Char]]
interleave [] xs = xs
interleave xs [] = xs
interleave (x:xs) (y:ys) = x:y:d : interleave xs ys
    where
        d = map (f . uncurry (==)) $ zip x y
        f True = ' '
        f False = '-'

quote :: [Char] -> [Char]
quote [] = []
quote (x:xs)
    | x == ' '  = "_." ++ quote xs
    | x == '\t' = "\\t" ++ quote xs
    | x == '\n' = "\\n\n" ++ quote xs
    | True      = x : quote xs

margin :: IORef Int
margin = unsafePerformIO $ newIORef 0 

log_failures :: IORef Bool
log_failures = unsafePerformIO $ newIORef True

failure_number :: IORef Int
failure_number = unsafePerformIO $ newIORef 0

new_failure :: String -> String -> String -> IO ()
new_failure name actual expected = do
    b <- readIORef log_failures
    if b then do
        n <- readIORef failure_number
        writeIORef failure_number $ n+1
        withFile (format "actual-{0}.txt" n) WriteMode $ \h -> do
            hPutStrLn h $ "; " ++ name
            hPutStrLn h actual
        withFile (format "expected-{0}.txt" n) WriteMode $ \h -> do
            hPutStrLn h $ "; " ++ name
            hPutStrLn h expected
    else return ()

test_suite :: (Typeable a, Show a) => [(String, IO a, a)] -> IO Bool
test_suite xs = test_cases $ map f xs 
    where
        f (x,y,z) = Case x y z

test_cases :: [TestCase] -> IO Bool
test_cases xs = 
        mapM f xs >>= test_suite_string
    where
        f (Case x y z) = return ( Nothing
                                , x
                                , (do a <- y ; return $ disp a)
                                , disp z
                                , cast z == (Nothing :: Maybe Bool))
        f (CalcCase x y z) = do 
                r <- z
                return ( Nothing
                       , x
                       , (do a <- y ; return $ disp a)
                       , disp r
                       , True  )
        f (StringCase x y z) = return (Nothing, x, y, z, True)
        f (POCase x y z)     = return (Just $ snd `liftM` y, x, fst `liftM` y, z, True)
        f (LineSetCase x y z) = f (StringCase x 
                                    ((unlines . sort . lines) `liftM` y) 
                                    (unlines $ sort $ lines z))


disp :: (Typeable a, Show a) => a -> String
disp x = maybe (show x) id (cast x)

print_po :: Maybe (IO (M.Map Label Sequent)) -> String -> String -> String -> IO ()
print_po pos name actual expected = do
        let ma = f actual
            me = f expected
            f xs = M.map (== "  o  ") $ M.fromList $ map (swap . splitAt 5) $ lines xs
            mr = M.keys $ M.filter not $ M.unionWith (==) (me `M.intersection` ma) ma
        case pos of
            Just pos -> do
                pos <- pos
                n <- readIORef failure_number
                forM_ (zip [0..] mr) $ \(i,po) -> do
--                    hPutStrLn stderr $ "writing po file: " 
--                    forM_ (M.keys ma) $ hPutStrLn stderr . show
--                    hPutStrLn stderr $ "---"
--                    forM_ (M.keys me) $ hPutStrLn stderr . show
                    if label po `M.member` pos then do
                        withFile (format "po-{0}-{1}.z3" n i) WriteMode $ \h -> do
                            hPutStrLn h $ "; " ++ name
                            hPutStrLn h $ "; " ++ po
                            hPutStrLn h $ "; " ++ if not $ ma M.! po 
                                                  then  "does {not discharge} automatically"
                                                  else  "{discharges} automatically"
                            hPutStrLn h $ concatMap pretty_print' $ z3_code $ pos M.! label po
                    else return ()
            Nothing  -> return ()

test_suite_string :: [(Maybe (IO (M.Map Label Sequent)), String, IO String, String, Bool)] -> IO Bool
test_suite_string xs = do
        n  <- readIORef margin
        let bars = concat $ take n $ repeat "|  "
            putLn xs = putStr $ unlines $ map (bars ++) $ lines xs 
        writeIORef margin (n+1)
        xs <- forM xs (\(s,x,y,z,b) -> do
            putLn ("+- " ++ x)
            r <- catch 
                (do r <- y; return $ Right r) 
                (\e -> return $ Left $ show (e :: SomeException))
            case r of
                Right r -> 
                    if (r == z)
                    then return True
                    else if b then do
                         print_po s x r z
                         new_failure x r z
                         putLn $ diff r z
                         return False 
                    else return False
                Left m -> do
                    putLn ("   Exception:  " ++ m)
                    return False )
        let x = length xs
            y = length $ filter id xs
        writeIORef margin n
        putLn (format "+- [ Success: {0} / {1} ]" y x)
        return (and xs)
