{-# LANGUAGE ExistentialQuantification #-} 
{-# LANGUAGE TupleSections             #-}
module Tests.UnitTest 
    ( TestCase(..), run_test_cases, test_cases )
where

    -- Modules
import Logic.Expr hiding ( name )
import Logic.Proof

import Z3.Z3

    -- Libraries
import Control.Arrow
import Control.Concurrent
import Control.Exception
import Control.Monad

import           Data.Char
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
    | Suite String [TestCase]

diff :: String -> String -> String
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

interleave :: [String] -> [String] -> [String]
interleave [] xs = xs
interleave xs [] = xs
interleave (x:xs) (y:ys) = x:y:d : interleave xs ys
    where
        d = map (f . uncurry (==)) $ zip x y
        f True = ' '
        f False = '-'

quote :: String -> String
quote [] = []
quote (x:xs)
    | x == ' '  = "_." ++ quote xs
    | x == '\t' = "\\t" ++ quote xs
    | x == '\n' = "\\n\n" ++ quote xs
    | True      = x : quote xs

margin :: MVar Int
margin = unsafePerformIO $ newMVar 0 

log_failures :: MVar Bool
log_failures = unsafePerformIO $ newMVar True

failure_number :: MVar Int
failure_number = unsafePerformIO $ newMVar 0

new_failure :: String -> String -> String -> IO ()
new_failure name actual expected = do
    b <- readMVar log_failures
    if b then do
        n <- takeMVar failure_number
        putMVar failure_number $ n+1
        withFile (format "actual-{0}.txt" n) WriteMode $ \h -> do
            hPutStrLn h $ "; " ++ name
            hPutStrLn h actual
        withFile (format "expected-{0}.txt" n) WriteMode $ \h -> do
            hPutStrLn h $ "; " ++ name
            hPutStrLn h expected
    else return ()

test_cases :: String -> [TestCase] -> TestCase
test_cases = Suite

data UnitTest = UT 
    { name :: String
    , routine :: IO (String, Maybe (M.Map Label Sequent))
    , outcome :: String
    , is_unit :: Bool }
    | Node { name :: String, _children :: [UnitTest] }

run_test_cases :: TestCase -> IO Bool
run_test_cases xs = 
        f xs >>= test_suite_string . (:[])
    where
        f (Case x y z) = return UT
                            { name = x
                            , routine = do a <- y ; return (disp a,Nothing)
                            , outcome = disp z
                            , is_unit = cast z == (Nothing :: Maybe Bool) }
        f (CalcCase x y z) = do 
                r <- z
                return UT
                    { name = x
                    , routine = do a <- y ; return (disp a, Nothing)
                    , outcome = disp r
                    , is_unit = True }
        f (StringCase x y z) = return UT 
                                { name = x
                                , routine = (,Nothing) `liftM` y
                                , outcome = z
                                , is_unit = True }
        f (POCase x y z)     = do
                let cmd = catch (second Just `liftM` y) f
                    f x = putStrLn "*** EXCEPTION ***" >> return (show (x :: SomeException), Nothing)
                    -- get_po = catch (snd `liftM` y) g
                    -- g :: SomeException -> IO (M.Map Label Sequent)
                    -- g = const $ putStrLn "EXCEPTION!!!" >> return M.empty
                return UT
                    { name = x
                    , routine = cmd 
                    , outcome = z 
                    , is_unit = True }
        f (LineSetCase x y z) = f (StringCase x 
                                    ((unlines . sort . lines) `liftM` y) 
                                    (unlines $ sort $ lines z))
        f (Suite n xs) = Node n `liftM` mapM f xs


disp :: (Typeable a, Show a) => a -> String
disp x = maybe (show x) id (cast x)

print_po :: Maybe (M.Map Label Sequent) -> String -> String -> String -> IO ()
print_po pos name actual expected = do
        let ma = f actual
            me = f expected
            f xs = M.map (== "  o  ") $ M.fromList $ map (swap . splitAt 5) $ lines xs
            mr = M.keys $ M.filter not $ M.unionWith (==) (me `M.intersection` ma) ma
        case pos of
            Just pos -> do
                n <- readMVar failure_number
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

test_suite_string :: [UnitTest] -> IO Bool
test_suite_string xs = do
        n  <- takeMVar margin
        let bars = concat $ take n $ repeat "|  "
            putLn xs = putStr $ unlines $ map (bars ++) $ lines xs 
        putMVar margin (n+1)
        xs <- forM xs $ \ut -> do
            case ut of
              (UT x y z b) -> do
                putLn ("+- " ++ x)
                r <- catch 
                    (do r <- y; return $ Right r) 
                    (\e -> return $ Left $ show (e :: SomeException))
                case r of
                    Right (r,s) -> 
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
                        return False 
              Node n xs -> do
                putLn ("+- " ++ n)
                test_suite_string xs
        let x = length xs
            y = length $ filter id xs
        swapMVar margin n
        putLn (format "+- [ Success: {0} / {1} ]" y x)
        return (and xs)
