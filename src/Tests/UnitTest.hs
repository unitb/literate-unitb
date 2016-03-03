{-# LANGUAGE ExistentialQuantification #-} 
module Tests.UnitTest 
    ( TestCase(..), run_test_cases, test_cases 
    , tempFile, takeLeaves, leafCount
    , selectLeaf, dropLeaves, leaves
    , makeTestSuite, makeTestSuiteOnly
    , testName, TestName
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
import Control.Lens hiding ((<.>))
import Control.Monad
import Control.Monad.Loops
import Control.Monad.Reader
import Control.Monad.RWS

import           Data.Either
import           Data.IORef
import           Data.List
import           Data.List.NonEmpty as NE (sort)
import           Data.Maybe
import           Data.String.Indentation
import           Data.String.Lines hiding (lines,unlines)
import           Data.Tuple
import           Data.Typeable

import GHC.Stack
import GHC.SrcLoc

import Language.Haskell.TH

import Prelude
import PseudoMacros

import qualified Utilities.Map as M hiding ((!))
import Utilities.Partial
import Utilities.Table

import System.FilePath
import System.IO
import System.IO.Unsafe

import Text.Printf.TH

data TestCase = 
      forall a . (Show a, Eq a, Typeable a) => Case String (IO a) a
    | POCase String (IO (String, Table Label Sequent)) String
    | forall a . (Show a, Eq a, Typeable a) => CalcCase String (IO a) (IO a) 
    | StringCase String (IO String) String
    | LineSetCase String (IO String) String
    | Suite CallStack String [TestCase]
    | WithLineInfo CallStack TestCase

newtype M a = M { runM :: RWST Int [Either (MVar [String]) String] Int (ReaderT (IORef [ThreadId]) IO) a }
    deriving ( Monad,Functor,Applicative,MonadIO
             , MonadReader Int
             , MonadState Int
             , MonadWriter [Either (MVar [String]) String])

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
    n <- liftIO $ takeMVar failure_number
    liftIO $ putMVar failure_number $ n+1
    put n

callStackLineInfo :: CallStack -> [String]
callStackLineInfo cs = reverse $ map f $ filter (($__FILE__ /=) . srcLocFile) $ map snd $ getCallStack cs
    where
        f c = [printf|%s:%d:%d|] (srcLocFile c) (srcLocStartLine c) (srcLocStartCol c)


new_failure :: CallStack -> String -> String -> String -> M ()
new_failure cs name actual expected = do
    b <- liftIO $ readMVar log_failures
    if b then do
        n <- get
        liftIO $ withFile ([printf|actual-%d.txt|] n) WriteMode $ \h -> do
            hPutStrLn h $ "; " ++ name
            forM_ (callStackLineInfo cs) $ hPutStrLn h . ("; " ++)
            hPutStrLn h actual
        liftIO $ withFile ([printf|expected-%d.txt|] n) WriteMode $ \h -> do
            hPutStrLn h $ "; " ++ name
            forM_ (callStackLineInfo cs) $ hPutStrLn h . ("; " ++)
            hPutStrLn h expected
    else return ()

test_cases :: (?loc :: CallStack) => String -> [TestCase] -> TestCase
test_cases = Suite ?loc

data UnitTest = forall a. Eq a => UT 
    { name :: String
    , routine :: IO (a, Maybe (Table Label Sequent))
    , outcome :: a
    , _mcallStack :: Maybe CallStack
    , _display :: a -> String
    -- , _source :: FilePath
    }
    | Node { _callStack :: CallStack, name :: String, _children :: [UnitTest] }

-- strip_line_info :: String -> String
-- strip_line_info xs = unlines $ map f $ lines xs
--     where
--         f xs = takeWhile (/= '(') xs

run_test_cases :: (?loc :: CallStack) => TestCase -> IO Bool
run_test_cases xs = do
        swapMVar failure_number 0
        c        <- f Nothing xs 
        ref      <- newIORef []
        (b,_,w)  <- runReaderT (runRWST (runM $ test_suite_string ?loc c) 0 (assertFalse' "??")) ref
        forM_ w $ \ln -> do
            case ln of
                Right xs -> putStrLn xs
                Left xs -> takeMVar xs >>= mapM_ putStrLn
        x <- fmap (uncurry (==)) <$> takeMVar b
        either throw return x
    where        
        f _ (WithLineInfo cs t) = f (Just cs) t
        f cs (POCase x y z)     = do
                let cmd = catch (second Just `liftM` y) handler
                    handler exc = do
                        putStrLn "*** EXCEPTION ***"
                        putStrLn x
                        print exc
                        return (show (exc :: SomeException), Nothing)
                    -- get_po = catch (snd `liftM` y) g
                    -- g :: SomeException -> IO (Table Label Sequent)
                    -- g = const $ putStrLn "EXCEPTION!!!" >> return M.empty
                return UT
                    { name = x
                    , routine = cmd 
                    , outcome = z 
                    , _mcallStack = cs
                    , _display = id
                    }
        f _ (Suite cs n xs) = Node cs n <$> mapM (f $ Just cs) xs
        -- f t = return (Node (nameOf t) [])
        f cs (Case x y z) = return UT
                            { name = x
                            , routine = (,Nothing) <$> y
                            , outcome = z
                            , _mcallStack = cs
                            , _display = disp
                            }
        f cs (CalcCase x y z) = do 
                r <- z
                return UT
                    { name = x
                    , routine  = (,Nothing) <$> y
                    , outcome  = r
                    , _mcallStack = cs
                    , _display = disp
                    }
        f cs (StringCase x y z) = return UT 
                                { name = x
                                , routine = (,Nothing) <$> y
                                , outcome = z
                                , _mcallStack = cs
                                , _display = id
                                }
        f cs (LineSetCase x y z) = f cs $ StringCase x 
                                    ((asLines %~ NE.sort) <$> y) 
                                    (z & asLines %~ NE.sort)

disp :: (Typeable a, Show a) => a -> String
disp x = fromMaybe (reindent $ show x) (cast x)

print_po :: CallStack -> Maybe (Table Label Sequent) -> String -> String -> String -> M ()
print_po cs pos name actual expected = do
    n <- get
    liftIO $ do
        let ma = f actual
            me = f expected
            f :: String -> Table String Bool
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
                        withFile ([printf|po-%d-%d.z3|] n i) WriteMode $ \h -> do
                            hPutStrLn h $ "; " ++ name
                            hPutStrLn h $ "; " ++ po
                            hPutStrLn h $ "; " ++ if not $ ma ! po 
                                                  then  "does {not discharge} automatically"
                                                  else  "{discharges} automatically"
                            forM_ (callStackLineInfo cs) $ hPutStrLn h . ("; " ++)
                            hPutStrLn h $ unlines $ map pretty_print' (z3_code $ pos ! label po) ++ ["; " ++ po]
                    else return ()
            Nothing  -> return ()

test_suite_string :: CallStack
                  -> UnitTest 
                  -> M (MVar (Either SomeException (Int,Int)))
test_suite_string cs' ut = do
        let putLn xs = do
                ys <- mk_lines xs
                -- lift $ putStr $ unlines ys
                tell $ map Right ys
        case ut of
          (UT x y z mli disp) -> forkTest $ do
            let cs = fromMaybe cs' mli
            putLn ("+- " ++ x)
            r <- liftIO $ catch 
                (Right `liftM` y) 
                (\e -> return $ Left $ show (e :: SomeException))
            case r of
                Right (r,s) -> 
                    if (r == z)
                    then return (1,1)
                    else do
                        take_failure_number
                        print_po cs s x (disp r) (disp z)
                        new_failure cs x (disp r) (disp z)
                        putLn "*** FAILED ***"
                        forM_ (callStackLineInfo cs) $ tell . (:[]) . Right
                        return (0,1) 
                Left m -> do
                    putLn ("   Exception:  " ++ m)
                    return (0,1)
          Node cs n xs -> do
            putLn ("+- " ++ n)
            xs <- indent 1 $ mapM (test_suite_string cs) xs
            forkTest $ do
                xs' <- mergeAll xs
                let xs = map (either (const (0,1)) id) xs' :: [(Int,Int)]
                    x = sum $ map snd xs
                    y = sum $ map fst xs
                putLn ([printf|+- [ Success: %d / %d ]|] y x)
                return (y,x)

nameOf :: TestCase -> String
nameOf (WithLineInfo _ c) = nameOf c
nameOf (Suite _ n _) = n
nameOf (Case n _ _) = n
nameOf (POCase n _ _) = n
nameOf (CalcCase n _ _) = n
nameOf (StringCase n _ _) = n
nameOf (LineSetCase n _ _) = n

leaves :: TestCase -> [String]
leaves (Suite _ _ xs) = concatMap leaves xs
leaves t = [nameOf t]

setName :: String -> TestCase -> TestCase
setName n (WithLineInfo cs t) = WithLineInfo cs $ setName n t
setName n (Suite cs _ xs) = Suite cs n xs
setName n (Case _ x y) = Case n x y
setName n (POCase _ x y) = POCase n x y
setName n (CalcCase _ x y) = CalcCase n x y
setName n (StringCase _ x y) = StringCase n x y
setName n (LineSetCase _ x y) = LineSetCase n x y

allLeaves :: TestCase -> [TestCase]
allLeaves = allLeaves' ""
    where
        allLeaves' n (Suite _ n' xs) = concatMap (allLeaves' (n ++ n' ++ "/")) xs
        allLeaves' n t = [setName (n ++ nameOf t) t]

selectLeaf :: Int -> TestCase -> TestCase 
selectLeaf n = takeLeaves (n+1) . dropLeaves n

dropLeaves :: Int -> TestCase -> TestCase
dropLeaves n (Suite cs name xs) = Suite cs name (drop (length ws) xs)
    where
        ys = map leafCount xs
        zs = map sum $ inits ys
        ws = dropWhile (<= n) zs
dropLeaves _ x = x

takeLeaves :: Int -> TestCase -> TestCase
takeLeaves n (Suite cs name xs) = Suite cs name (take (length ws) xs)
    where
        ys = map leafCount xs
        zs = map sum $ inits ys
        ws = takeWhile (<= n) zs
takeLeaves _ x = x

leafCount :: TestCase -> Int
leafCount (Suite _ _ xs) = sum $ map leafCount xs
leafCount _ = 1

capabilities :: SSem
capabilities = unsafePerformIO $ new 16

forkTest :: M a -> M (MVar (Either SomeException a))
forkTest cmd = do
    result <- liftIO $ newEmptyMVar
    output <- liftIO $ newEmptyMVar
    r <- ask
    liftIO $ wait capabilities
    --tid <- liftIO myThreadId
    ref <- M $ lift ask
    t <- liftIO $ do
        ref <- newIORef []
        let handler e = do
                ts <- readIORef ref
                mapM_ (`throwTo` e) ts
                putStrLn "failed"
                print e
                putMVar result $ Left e
                putMVar output $ [show e]
        forkIO $ do
            finally (handle handler $ do
                (x,_,w) <- runReaderT (runRWST (runM cmd) r (-1)) ref
                putMVar result (Right x)
                xs <- forM w $ \ln -> do
                    either 
                        takeMVar 
                        (return . (:[])) 
                        ln
                putMVar output $ concat xs)
                (signal capabilities)
    liftIO $ modifyIORef ref (t:)
    tell [Left output]
    return result

mergeAll :: [MVar a] -> M [a]
mergeAll xs = liftIO $ do
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

data TestName = TestName String CallStack

testName :: (?loc :: CallStack) => String -> TestName
testName str = TestName str ?loc

fooNameOf :: TestName -> String
fooNameOf (TestName str _)   = str

fooCallStack :: TestName -> CallStack
fooCallStack (TestName _ cs) = cs

makeTestSuiteOnly :: String -> [Int] -> ExpQ
makeTestSuiteOnly title ts = do
        let namei :: Int -> ExpQ
            namei i = [e| fooNameOf $(varE $ mkName $ "name" ++ show i) |]
            casei i = varE $ mkName $ "case" ++ show i
            loci i = [e| fooCallStack $(varE $ mkName $ "name" ++ show i) |]
            resulti i = varE $ mkName $ "result" ++ show (i :: Int)
            cases = [ [e| WithLineInfo $(loci i) (Case $(namei i) $(casei i) $(resulti i)) |] | i <- ts ]
            titleE = litE $ stringL title
        [e| test_cases $titleE $(listE cases) |]

makeTestSuite :: String -> ExpQ
makeTestSuite title = do
    let names n' = [ "name" ++ n' 
                   , "case" ++ n' 
                   , "result" ++ n' ]
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
        makeTestSuiteOnly title ts
    else do
        mapM_ (reportError.[printf|missing test component: '%s'|]) (concat es)
        [e| undefined |]
