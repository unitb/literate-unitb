{-# LANGUAGE ExistentialQuantification, ImplicitParams #-} 
module Test.UnitTest 
    ( TestCase(..)
    , run_quickCheck_suite
    , run_quickCheck_suite_with
    , run_test_cases, test_cases 
    , tempFile, takeLeaves, leafCount
    , selectLeaf, dropLeaves, leaves
    , makeTestSuite, makeTestSuiteOnly
    , testName, TestName
    , stringCase
    , callStackLineInfo
    , M, UnitTest(..) 
    , IsTestCase(..)
    , logNothing, PrintLog
    , allLeaves )
where

    -- Libraries
import Control.Applicative
import Control.Concurrent
import Control.Concurrent.SSem
import Control.Concurrent.STM
import Control.DeepSeq
import Control.Exception
import Control.Exception.Lens
import Control.Lens hiding ((<.>))
import Control.Monad
import Control.Monad.Loops
import Control.Monad.Reader
import Control.Monad.RWS
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Control.Precondition

import           Data.Either
import           Data.IORef
import           Data.List
import           Data.List.NonEmpty as NE (sort)
import           Data.String.Indentation
import           Data.String.Lines hiding (lines,unlines)
import           Data.Tuple
import           Data.Typeable

import GHC.Stack
import GHC.SrcLoc

import Language.Haskell.TH

import Prelude
import PseudoMacros

import System.FilePath
import System.IO
import System.IO.Unsafe

import Test.QuickCheck
import Test.QuickCheck.Report

import Text.Printf.TH

data TestCase = 
      forall a . (Show a, Eq a, Typeable a, NFData a) => Case String (IO a) a
    | forall a . (Show a, Eq a, Typeable a, NFData a) 
        => CalcCase String (IO a) (IO a) 
    | StringCase String (IO String) String
    | LineSetCase String (IO String) String
    | Suite CallStack String [TestCase]
    | WithLineInfo CallStack TestCase
    | QuickCheckProps String (forall a. (PropName -> Property -> IO (a,Result)) -> IO ([a],Bool))
    | forall test. IsTestCase test => Other test

stringCase :: Pre
           => String 
           -> IO String 
           -> String
           -> TestCase
stringCase n test res = WithLineInfo (?loc) $ StringCase n test res

class IsTestCase c where
    makeCase :: Maybe CallStack -> c -> ReaderT Args IO UnitTest
    nameOf :: Lens' c String

instance IsTestCase TestCase where
    makeCase _ (WithLineInfo cs t) = makeCase (Just cs) t
    makeCase _ (Suite cs n xs) = Node cs n <$> mapM (makeCase $ Just cs) xs
    makeCase cs (Case x y z) = return UT
                        { name = x
                        , routine = (,logNothing) <$> y
                        , outcome = z
                        , _mcallStack = cs
                        , _displayA = disp
                        , _displayE = disp
                        , _criterion = id
                        }
    makeCase cs (CalcCase x y z) = do 
            r <- lift z
            return UT
                { name = x
                , routine  = (,logNothing) <$> y
                , outcome  = r
                , _mcallStack = cs
                , _displayA = disp
                , _displayE = disp
                , _criterion = id
                }
    makeCase cs (StringCase x y z) = return UT 
                            { name = x
                            , routine = (,logNothing) <$> y
                            , outcome = z
                            , _mcallStack = cs
                            , _displayA = id
                            , _displayE = id
                            , _criterion = id
                            }
    makeCase cs (LineSetCase x y z) = makeCase cs $ stringCase x 
                                ((asLines %~ NE.sort) <$> y) 
                                (z & asLines %~ NE.sort)
    makeCase cs (QuickCheckProps n prop) = do
            args <- ask
            return UT
                            { name = n
                            , routine = (,logNothing) <$> prop (quickCheckWithResult' args)
                            , outcome = True
                            , _mcallStack = cs
                            , _displayA = intercalate "\n" . fst
                            , _displayE = const ""
                            , _criterion = snd
                            }
    makeCase cs (Other c) = makeCase cs c
    nameOf f (WithLineInfo x0 c) = WithLineInfo x0 <$> nameOf f c
    nameOf f (Suite x0 n x1) = (\n' -> Suite x0 n' x1) <$> f n
    nameOf f (Case n x0 x1) = (\n' -> Case n' x0 x1) <$> f n
    nameOf f (QuickCheckProps n prop) = (\n' -> QuickCheckProps n' prop) <$> f n
    nameOf f (Other c) = Other <$> nameOf f c
    nameOf f (CalcCase n x0 x1) = (\n' -> CalcCase n' x0 x1) <$> f n
    nameOf f (StringCase n x0 x1) = (\n' -> stringCase n' x0 x1) <$> f n
    nameOf f (LineSetCase n x0 x1) = (\n' -> LineSetCase n' x0 x1) <$> f n

newtype M a = M { runM :: RWST Int [Either (STM [String]) String] Int (ReaderT (IORef [ThreadId]) IO) a }
    deriving ( Monad,Functor,Applicative,MonadIO
             , MonadReader Int
             , MonadState Int
             , MonadWriter [Either (STM [String]) String])

instance Indentation Int M where
    -- func = 
    margin_string = do
        n <- margin
        return $ concat $ replicate n "|  "
    _margin _ = id
            
onlyQuickCheck :: TestCase -> Maybe TestCase
onlyQuickCheck (Suite cs n ts) = Suite cs n <$> nonEmpty (mapMaybe onlyQuickCheck ts)
    where
        nonEmpty [] = Nothing
        nonEmpty xs@(_:_) = Just xs
onlyQuickCheck (WithLineInfo cs t) = WithLineInfo cs <$> onlyQuickCheck t
onlyQuickCheck p@(QuickCheckProps _ _) = Just p
onlyQuickCheck _ = Nothing

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

test_cases :: Pre => String -> [TestCase] -> TestCase
test_cases = Suite ?loc

logNothing :: PrintLog
logNothing = const $ const $ const $ const $ return ()

type PrintLog = CallStack -> String -> String -> String -> M ()

data UnitTest = forall a b. (Eq a,NFData b) => UT 
    { name :: String
    , routine :: IO (b, PrintLog)
    , outcome :: a
    , _mcallStack :: Maybe CallStack
    , _displayA :: b -> String
    , _displayE :: a -> String
    , _criterion :: b -> a
    -- , _source :: FilePath
    }
    | Node { _callStack :: CallStack, name :: String, _children :: [UnitTest] }

-- strip_line_info :: String -> String
-- strip_line_info xs = unlines $ map f $ lines xs
--     where
--         f xs = takeWhile (/= '(') xs

run_quickCheck_suite :: Pre => TestCase -> IO Bool
run_quickCheck_suite t = run_quickCheck_suite_with t $ return ()

run_quickCheck_suite_with :: Pre => TestCase -> State Args k -> IO Bool
run_quickCheck_suite_with t = maybe noProps run_test_cases_with (onlyQuickCheck t)
    where
        noProps _ = putStrLn "No QuickCheckProps" >> return True

run_test_cases :: (Pre,IsTestCase testCase) 
               => testCase -> IO Bool
run_test_cases xs = run_test_cases_with xs (return ())

run_test_cases_with :: (Pre,IsTestCase testCase) 
                    => testCase 
                    -> State Args k
                    -> IO Bool
run_test_cases_with xs opts = do
        let args = execState opts stdArgs
        swapMVar failure_number 0
        c        <- runReaderT (makeCase Nothing xs) args
        ref      <- newIORef []
        (b,_,w)  <- runReaderT (runRWST 
                        (runM $ test_suite_string ?loc c) 0 
                        (assertFalse' "??")) ref
        forM_ w $ \ln -> do
            case ln of
                Right xs -> putStrLn xs
                Left xs -> atomically xs >>= mapM_ putStrLn
        x <- fmap (uncurry (==)) <$> atomically b
        either throw return x

disp :: (Typeable a, Show a) => a -> String
disp x = fromMaybe (reindent $ show x) (cast x)

putLn :: String -> M ()
putLn xs = do
        ys <- mk_lines xs
        tell $ map Right ys

test_suite_string :: CallStack
                  -> UnitTest 
                  -> M (STM (Either SomeException (Int,Int)))
test_suite_string cs' ut = do
        case ut of
          (UT title test expected mli dispA dispE cri) -> forkTest $ do
            let cs = fromMaybe cs' mli
            putLn ("+- " ++ title)
            r <- liftIO $ catch 
                (Right <$> (liftIO . evaluate . force =<< test)) 
                (\e -> return $ Left $ show (e :: SomeException))
            case r of
                Right (r,printLog) -> 
                    if (cri r == expected)
                    then return (1,1)
                    else do
                        take_failure_number
                        printLog cs title (dispA r) (dispE expected)
                        new_failure cs title (dispA r) (dispE expected)
                        putLn "*** FAILED ***"
                        forM_ (callStackLineInfo cs) $ tell . (:[]) . Right
                        return (0,1) 
                Left m -> do
                    tell [Right $ "   Exception:  \n" ++ m]
                    take_failure_number
                    new_failure cs title m (dispE expected)
                    putLn "*** FAILED ***"
                    forM_ (callStackLineInfo cs) $ tell . (:[]) . Right
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


leaves :: TestCase -> [String]
leaves (Suite _ _ xs) = concatMap leaves xs
leaves t = [t^.nameOf]


allLeaves :: TestCase -> [TestCase]
allLeaves = allLeaves' ""
    where
        allLeaves' n (Suite _ n' xs) = concatMap (allLeaves' (n ++ n' ++ "/")) xs
        allLeaves' n t = [t & nameOf %~ (n ++)]

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
capabilities = unsafePerformIO $ new 32

newtype Handled = Handled SomeException 
    deriving (Show, Exception)

_Handled :: Prism' SomeException Handled
_Handled = prism' toException fromException

forkTest :: M (Int,Int) -> M (STM (Either SomeException (Int,Int)))
forkTest cmd = do
    result <- liftIO $ newEmptyTMVarIO
    output <- liftIO $ newEmptyTMVarIO
    r <- ask
    liftIO $ wait capabilities
    ref <- M $ lift ask
    t <- liftIO $ do
        ref <- newIORef []
        let handler e = do
                putStrLn "failed"
                print e
                atomically $ do 
                    putTMVar result $ Left e
                    putTMVar output $ [show e]
        forkIO $ do
            finally (handling id handler $ do
                (x,_,w) <- runReaderT (runRWST (runM cmd) r (-1)) ref
                atomically $ putTMVar result (Right x)
                xs <- forM w $ \ln -> do
                    either 
                        atomically 
                        (return . (:[])) 
                        ln
                atomically $ putTMVar output $ concat xs
                )
                (signal capabilities)
    liftIO $ modifyIORef ref (t:)
    tell [Left $ readTMVar output]
    return $ readTMVar result

mergeAll :: [STM a] -> M [a]
mergeAll xs = liftIO $ do
    forM xs atomically

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

data TestCaseGen = PropCaseGen Name Name | CaseGen Name Name Name

caseGenName :: TestCaseGen -> Name
caseGenName (PropCaseGen n _) = n
caseGenName (CaseGen n _ _)   = n

matchTestCase :: Int -> Q (Either Int TestCaseGen)
matchTestCase n = fmap (maybe (Left n) Right) 
            $ runMaybeT $ msum
        [ liftA2 PropCaseGen (valueName namei) (valueName propi)
        , CaseGen <$> valueName namei <*> valueName casei <*> valueName resulti ]
    where
        valueName = MaybeT . lookupValueName
        namei = "name" ++ show n
        casei = "case" ++ show n
        resulti = "result" ++ show n
        propi = "prop" ++ show n

genTestCase :: TestCaseGen -> ExpQ
genTestCase (CaseGen n c r) = [e| Case (fooNameOf $(varE n)) $(varE c) $(varE r) |]
genTestCase (PropCaseGen n prop) = [e| QuickCheckProps (fooNameOf $(varE n)) $(varE prop) |]        

testName :: Pre => String -> TestName
testName str = TestName str ?loc

fooNameOf :: TestName -> String
fooNameOf (TestName str _)   = str

fooCallStack :: TestName -> CallStack
fooCallStack (TestName _ cs) = cs

makeTestSuiteOnly :: String -> [TestCaseGen] -> ExpQ
makeTestSuiteOnly title ts = do
        let loci i = [e| fooCallStack $(varE $ caseGenName i) |]
            cases = [ [e| WithLineInfo $(loci i) $(genTestCase i) |] | i <- ts ]
            titleE = litE $ stringL title
        [e| test_cases $titleE $(listE cases) |]

makeTestSuite :: String -> ExpQ
makeTestSuite title = do
    let names n' = [ "name" ++ n' 
                   , "case" ++ n' 
                   , "result" ++ n' 
                   , "prop" ++ n' ]
        f :: Int -> Q Bool
        f n = do
            let n' = show n
            any isJust <$> mapM lookupValueName (names n')
    xs <- concat <$> sequence
        [ takeWhileM f [0..0]
        , takeWhileM f [1..] ]
    (es,ts) <- partitionEithers <$> mapM matchTestCase xs
    if null es then do
        makeTestSuiteOnly title ts
    else do
        mapM_ (reportError . [printf|missing component for test case # %d|]) es
        [e| undefined |]
