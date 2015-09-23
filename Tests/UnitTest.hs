{-# LANGUAGE ExistentialQuantification  #-} 
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TemplateHaskell            #-}
module Tests.UnitTest 
    ( TestCase(..), run_test_cases, test_cases 
    , tempFile, takeLeaves, leafCount
    , selectLeaf, dropLeaves, leaves
    , makeTestSuite
    , allLeaves, nameOf )
where

    -- Modules
import Logic.Expr hiding ( name )
import Logic.Proof

import Z3.Z3

    -- Libraries
import Control.Arrow
import Control.Applicative
import Control.Concurrent
import Control.Concurrent.SSem
import Control.Exception
import Control.Monad
import Control.Monad.Loops
import Control.Monad.Trans
import Control.Monad.Trans.RWS

import           Data.Either
import           Data.List
import qualified Data.Map as M
import           Data.Maybe
import           Data.Tuple
import           Data.Typeable

import Prelude

import Utilities.Format
import Utilities.Indentation

import System.FilePath
import System.IO
import System.IO.Unsafe

import Text.Printf

import Language.Haskell.TH

data TestCase = 
      forall a . (Show a, Typeable a) => Case String (IO a) a
    | POCase String (IO (String, M.Map Label Sequent)) String
    | forall a . (Show a, Typeable a) => CalcCase String (IO a) (IO a) 
    | StringCase String (IO String) String
    | LineSetCase String (IO String) String
    | Suite String [TestCase]

type M = RWST Int [Either (MVar [String]) String] Int IO

instance Indentation Int M where
    -- func = 
    margin_string = do
        n <- margin
        return $ concat $ replicate n "|  "
    _margin _ = id
            
log_failures :: MVar Bool
log_failures = unsafePerformIO $ newMVar True

failure_number :: MVar Int
failure_number = unsafePerformIO $ newMVar 0

take_failure_number :: M ()
take_failure_number = do
    n <- lift $ takeMVar failure_number
    lift $ putMVar failure_number $ n+1
    put n

new_failure :: String -> String -> String -> M ()
new_failure name actual expected = do
    b <- lift $ readMVar log_failures
    if b then do
        n <- get
        lift $ withFile (format "actual-{0}.txt" n) WriteMode $ \h -> do
            hPutStrLn h $ "; " ++ name
            hPutStrLn h actual
        lift $ withFile (format "expected-{0}.txt" n) WriteMode $ \h -> do
            hPutStrLn h $ "; " ++ name
            hPutStrLn h expected
    else return ()

test_cases :: String -> [TestCase] -> TestCase
test_cases = Suite

data UnitTest = UT 
    { name :: String
    , routine :: IO (String, Maybe (M.Map Label Sequent))
    , outcome :: String
    -- , _source :: FilePath
    }
    | Node { name :: String, _children :: [UnitTest] }

-- strip_line_info :: String -> String
-- strip_line_info xs = unlines $ map f $ lines xs
--     where
--         f xs = takeWhile (/= '(') xs

run_test_cases :: TestCase -> IO Bool
run_test_cases xs = do
        swapMVar failure_number 0
        c        <- f xs 
        (b,_,w) <- runRWST (test_suite_string [c]) 0 undefined
        forM_ w $ \ln -> do
            case ln of
                Right xs -> putStrLn xs
                Left xs -> takeMVar xs >>= mapM_ putStrLn
        x <- fmap (uncurry (==)) <$> takeMVar b
        either throw return x
    where
        f (POCase x y z)     = do
                let cmd = catch (second Just `liftM` y) f
                    f x = do
                        putStrLn "*** EXCEPTION ***"
                        print x
                        return (show (x :: SomeException), Nothing)
                    -- get_po = catch (snd `liftM` y) g
                    -- g :: SomeException -> IO (M.Map Label Sequent)
                    -- g = const $ putStrLn "EXCEPTION!!!" >> return M.empty
                return UT
                    { name = x
                    , routine = cmd 
                    , outcome = z 
                    }
        f (Suite n xs) = Node n <$> mapM f xs
        -- f t = return (Node (nameOf t) [])
        f (Case x y z) = return UT
                            { name = x
                            , routine = do a <- y ; return (disp a,Nothing)
                            , outcome = disp z
                            }
        f (CalcCase x y z) = do 
                r <- z
                return UT
                    { name = x
                    , routine = do a <- y ; return (disp a, Nothing)
                    , outcome = disp r
                    }
        f (StringCase x y z) = return UT 
                                { name = x
                                , routine = (,Nothing) `liftM` y
                                , outcome = z
                                }
        f (LineSetCase x y z) = f $ StringCase x 
                                    ((unlines . sort . lines) `liftM` y) 
                                    (unlines $ sort $ lines z)

disp :: (Typeable a, Show a) => a -> String
disp x = fromMaybe (show x) (cast x)

print_po :: Maybe (M.Map Label Sequent) -> String -> String -> String -> M ()
print_po pos name actual expected = do
    n <- get
    lift $ do
        let ma = f actual
            me = f expected
            f xs = M.map (== "  o  ") $ M.fromList $ map (swap . splitAt 5) $ lines xs
            mr = M.keys $ M.filter not $ M.unionWith (==) (me `M.intersection` ma) ma
        case pos of
            Just pos -> do
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
                            hPutStrLn h $ unlines $ map pretty_print' (z3_code $ pos M.! label po) ++ ["; " ++ po]
                    else return ()
            Nothing  -> return ()

test_suite_string :: [UnitTest] -> M (MVar (Either SomeException (Int,Int)))
test_suite_string xs = do
        let putLn xs = do
                ys <- mk_lines xs
                -- lift $ putStr $ unlines ys
                tell $ map Right ys
        xs <- forM xs $ \ut -> do
            case ut of
              (UT x y z) -> forkTest $ do
                putLn ("+- " ++ x)
                r <- lift $ catch 
                    (Right `liftM` y) 
                    (\e -> return $ Left $ show (e :: SomeException))
                case r of
                    Right (r,s) -> 
                        if (r == z)
                        then return (1,1)
                        else do
                            take_failure_number
                            print_po s x r z
                            new_failure x r z
                            putLn "*** FAILED ***"
                            return (0,1) 
                    Left m -> do
                        putLn ("   Exception:  " ++ m)
                        return (0,1)
              Node n xs -> do
                putLn ("+- " ++ n)
                indent 1 $ test_suite_string xs
        forkTest $ do
            xs' <- mergeAll xs
            let xs = map (either (const (0,1)) id) xs' :: [(Int,Int)]
                x = sum $ map snd xs
                y = sum $ map fst xs
            putLn (format "+- [ Success: {0} / {1} ]" y x)
            return (y,x)

nameOf :: TestCase -> String
nameOf (Suite n _) = n
nameOf (Case n _ _) = n
nameOf (POCase n _ _) = n
nameOf (CalcCase n _ _) = n
nameOf (StringCase n _ _) = n
nameOf (LineSetCase n _ _) = n

leaves :: TestCase -> [String]
leaves (Suite _ xs) = concatMap leaves xs
leaves t = [nameOf t]

setName :: String -> TestCase -> TestCase
setName n (Suite _ xs) = Suite n xs
setName n (Case _ x y) = Case n x y
setName n (POCase _ x y) = POCase n x y
setName n (CalcCase _ x y) = CalcCase n x y
setName n (StringCase _ x y) = StringCase n x y
setName n (LineSetCase _ x y) = LineSetCase n x y

allLeaves :: TestCase -> [TestCase]
allLeaves = allLeaves' ""
    where
        allLeaves' n (Suite n' xs) = concatMap (allLeaves' (n ++ n' ++ "/")) xs
        allLeaves' n t = [setName (n ++ nameOf t) t]

selectLeaf :: Int -> TestCase -> TestCase 
selectLeaf n = takeLeaves (n+1) . dropLeaves n

dropLeaves :: Int -> TestCase -> TestCase
dropLeaves n (Suite name xs) = Suite name (drop (length ws) xs)
    where
        ys = map leafCount xs
        zs = map sum $ inits ys
        ws = dropWhile (<= n) zs
dropLeaves _ x = x

takeLeaves :: Int -> TestCase -> TestCase
takeLeaves n (Suite name xs) = Suite name (take (length ws) xs)
    where
        ys = map leafCount xs
        zs = map sum $ inits ys
        ws = takeWhile (<= n) zs
takeLeaves _ x = x

leafCount :: TestCase -> Int
leafCount (Suite _ xs) = sum $ map leafCount xs
leafCount _ = 1

capabilities :: SSem
capabilities = unsafePerformIO $ new 16

forkTest :: M a -> M (MVar (Either SomeException a))
forkTest cmd = do
    result <- lift $ newEmptyMVar
    output <- lift $ newEmptyMVar
    r <- ask
    lift $ wait capabilities
    let handler e = do
        putMVar result $ Left e
        putMVar output $ [show e]
    lift $ forkIO $ do
        finally (handle handler $ do
            (x,_,w) <- runRWST cmd r (-1)
            putMVar result (Right x)
            xs <- forM w $ \ln -> do
                either 
                    takeMVar 
                    (return . (:[])) 
                    ln
            putMVar output $ concat xs)
            (signal capabilities)
    tell [Left output]
    return result

mergeAll :: [MVar a] -> M [a]
mergeAll xs = lift $ do
    forM xs takeMVar

tempFile_num :: MVar Int
tempFile_num = unsafePerformIO $ newMVar 0

tempFile :: FilePath -> IO FilePath
tempFile path = do
    n <- takeMVar tempFile_num
    putMVar tempFile_num (n+1)
    -- path <- canonicalizePath path
    let path' = dropExtension path ++ "-" ++ show n <.> takeExtension path
    --     finalize = do
    --         b <- doesFileExist path'
    --         when b $
    --             removeFile path'
    -- mkWeakPtr path' (Just finalize)
    return path'

makeTestSuite :: String -> ExpQ
makeTestSuite title = do
    let names n' = [ "name" ++ n' 
                   , "case" ++ n' 
                   , "result" ++ n' ]
        titleE = litE $ stringL title
        f n = do
            let n' = show n
            any isJust <$> mapM lookupValueName (names n')
        g n = do
            let n' = show n
            es <- filterM (fmap isNothing . lookupValueName) (names n')
            if null es then return $ Right n
                       else return $ Left es
    xs <- concat <$> sequence
        [ takeWhileM f [0..0]
        , takeWhileM f [1..] ]
    (es,ts) <- partitionEithers <$> mapM g xs
    if null es then do
        let namei i = varE $ mkName $ "name" ++ show i
            casei i = varE $ mkName $ "case" ++ show i
            resulti i = varE $ mkName $ "result" ++ show (i :: Int)
            cases = [ [e| Case $(namei i) $(casei i) $(resulti i) |] | i <- ts ]
        [e| test_cases $titleE $(listE cases) |]
    else do
        mapM_ (reportError.printf "missing test component: '%s'") (concat es)
        fail ""
