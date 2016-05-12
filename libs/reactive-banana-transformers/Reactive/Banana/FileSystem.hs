{-# LANGUAGE TypeFamilies #-}
module Reactive.Banana.FileSystem 
    ( FSMomentT
    , FSMoment
    , runFSMoment
    , interpretFSMomentT
    , reactimateFS, reactimateFS', mapEventFS 
    , run_tests )
where

import Control.Invariant hiding ((===))
import Control.Lens hiding (uncurried)
import Control.Monad
import Control.Monad.Fix
import Control.Monad.IO.Class
import Control.Monad.Reader
import Control.Monad.RWS
import Control.Monad.Writer
import Control.Monad.State

import Data.List.NonEmpty as NE (NonEmpty(..),toList)
import qualified Data.Map as M
import Data.Maybe

import Prelude hiding (writeFile,readFile)

import Reactive.Banana
import Reactive.Banana.Combinators.Extras
import Reactive.Banana.Frameworks
import Reactive.Banana.IO
import Reactive.Banana.Property hiding (run_tests)

import System.IO.FileSystem

import Test.QuickCheck

type FSMoment = FSMomentT MomentIO

newtype FSMomentT m a = FileSystemMomentT 
        { unFSMomentT :: forall w. Monoid w 
                      => ReaderT (ReactimateType w m) (WriterT w m) a }
    -- deriving ( Functor )
             -- , MonadTrans
             -- , Monad
             -- , MonadMoment
             -- , MonadMomentIO
             -- , MonadFix )

newtype ReactimateType w m = ReactimateType 
        { runReactimate :: Event (Future (FileSystemM (IO ())))
                        -> WriterT w m () }

instance MonadTrans FSMomentT where
    lift m = FileSystemMomentT $ lift $ lift m
instance Functor m => Functor (FSMomentT m) where
    fmap f (FileSystemMomentT x) = FileSystemMomentT $ fmap f x
instance Applicative m => Applicative (FSMomentT m) where
    pure x = FileSystemMomentT $ pure x
    {-# INLINE (<*>) #-}
    FileSystemMomentT f <*> FileSystemMomentT x = FileSystemMomentT $ f <*> x
instance MonadIO m => MonadIO (FSMomentT m) where
    liftIO m = FileSystemMomentT $ liftIO m
instance MonadMoment m => MonadMoment (FSMomentT m) where
    liftMoment m = FileSystemMomentT $ liftMoment m
instance MonadMomentIO m => MonadMomentIO (FSMomentT m) where
    liftMomentIO m = FileSystemMomentT $ liftMomentIO m
instance MonadFix m => MonadFix (FSMomentT m) where
    mfix f = FileSystemMomentT $ mfix $ unFSMomentT . f
instance Monad m => Monad (FSMomentT m) where
    {-# INLINE (>>=) #-}
    FileSystemMomentT m >>= f = FileSystemMomentT $ m >>= unFSMomentT . f
instance Frameworks m => Frameworks (FSMomentT m) where
    type EventList (FSMomentT m) a = EventList m a
    type InitF (FSMomentT m) = (MockFileSystemState,InitF m) 
    interpret' = interpretFSMomentT

reactimateFS :: Monad m'
             => Event (FileSystemM ())
             -> FSMomentT m' ()
reactimateFS e = reactimateFS' $ pure <$> e

reactimateFS' :: Event (Future (FileSystemM ()))
              -> FSMomentT m' ()
reactimateFS' e = reactimateFSImpl $ e & mapped.mapped.mapped %~ return

reactimateFSImpl :: Event (Future (FileSystemM (IO ())))
                 -> FSMomentT m' ()
reactimateFSImpl e = FileSystemMomentT $ ReaderT $ \react -> runReactimate react e

mapEventFS :: MonadMomentIO m'
           => (a -> FileSystemM b)
           -> Event a
           -> FSMomentT m' (Event b)
mapEventFS f e = do
        (e',h) <- liftMomentIO newEvent
        reactimateFSImpl $ e & mapped %~ pure.fmap h.f
        return e'

ioReactimate :: MonadMomentIO m => ReactimateType () m 
ioReactimate = ReactimateType $ \e -> 
    liftMomentIO $ reactimate' $ e & mapped.mapped %~ join.runFS

mockFSReactimate :: Monad m
                 => ReactimateType [Event (Future (FileSystemM (IO ())))] m 
mockFSReactimate = ReactimateType $ \e -> do
    tell [e]
    -- liftMomentIO _

runFSMoment :: MonadMomentIO m => FSMomentT m a -> m a
runFSMoment (FileSystemMomentT cmd) = fst <$> runWriterT (runReaderT cmd ioReactimate)

interpretFSMomentT :: Frameworks m
                   => (Event a -> FSMomentT m (Event b))
                   -> (MockFileSystemState, InitF m) 
                   -> [EventList m a] 
                   -> IO ([EventList m a], [Maybe b])
interpretFSMomentT f (initS,s) xs = do
    let f' e = do
                (x,es) <- runWriterT (runReaderT (unFSMomentT $ f e) mockFSReactimate)
                let ioEvt = unionsWith (liftA2 $ liftA2 (>>)) es
                    mock = ioEvt & mapped.mapped %~ runState . mockFS
                mock' <- fromFuture mock 
                (e',_) <- mapAccum initS mock'
                liftMomentIO $ reactimate e'
                    -- mappendWith f x y = liftA2 _ x y
                return x
    interpret' f' s xs

lockStep :: [NonEmpty a] -> [a]
lockStep = f 0
    where
        f _ [] = []
        f n (x:xs) = drop n (NE.toList x) ++ f ((n `max` length x) - 1) xs

lockStep' :: [NonEmpty a] -> [a]
lockStep' [] = []
lockStep' (x:xs) = NE.toList x ++ drop (length x - 1) (lockStep xs)

prop_lockStep :: (Eq a, Show a) => [NonEmpty a] -> Property
prop_lockStep xs = lockStep xs === lockStep' xs

prop_file_io :: String
             -> [Maybe (Maybe String,Maybe String,Maybe ())] 
             -> Property
prop_file_io c = satisfiesWith' showInput showOutput prog' prop (fs,())
    where
        showInput :: [Maybe (Maybe String, Maybe String, Maybe ())]
                  -> [[String]]
        showInput xs = [ xs & traverse %~ show . join . fmap (view _1)
                       , xs & traverse %~ show . join . fmap (view _2)
                       , xs & traverse %~ show . join . fmap (view _3) ]
        showOutput :: [Maybe (Maybe (Maybe String), Maybe (Maybe String))]
                   -> [[String]]
        showOutput xs = [ xs & traverse %~ show . join . fmap (view _1)
                        , xs & traverse %~ show . join . fmap (view _2) ]
        f1 = "/f1"
        f2 = "./f2"
        fs :: MockFileSystemState
        fs = create' $ do
                files %= M.insert f1 (Just c)
        prog' :: Event (Maybe String,Maybe String,Maybe ()) 
              -> FSMoment (Event (Maybe (Maybe String),Maybe (Maybe String)))
        prog' = prog^.packageEventFun'
        prog :: Event String -> Event String -> Event ()
             -> FSMoment (Event (Maybe String), Event (Maybe String))
        prog ioF1 ioF2 readF = do
                reactimateFS $ writeFile f1 <$> ioF1
                reactimateFS $ writeFile f2 <$> ioF2
                liftA2 (,)
                    (mapEventFS id $ ifFileExists f1 readFile <$ readF)
                    (mapEventFS id $ ifFileExists f2 readFile <$ readF)
                
        prop :: [Maybe (Maybe String, Maybe String,Maybe ())]
             -> [Maybe (Maybe (Maybe String), Maybe (Maybe String))] 
             -> Property
        prop input output = flip evalState (Just c,Nothing) $ do
                let runReadWrite :: (Maybe String, Maybe String, Maybe ())
                                 -> State
                                      (Maybe String, Maybe String)
                                      (NonEmpty (Maybe (Maybe (Maybe String), Maybe (Maybe String))))
                    runReadWrite (x,y,tick) = do
                            mapM_ (assign _1 . Just) x
                            mapM_ (assign _2 . Just) y
                            sequence $ 
                                (return Nothing)
                                :| (maybeToList tick >> [readFirst,readSecond])
                    readFirst :: State (Maybe String,Maybe String)
                                       (Maybe (Maybe (Maybe String), Maybe (Maybe String)))
                    readFirst  = Just . (_1 %~ Just) . (_2 .~ Nothing) <$> get
                    readSecond = Just . (_2 %~ Just) . (_1 .~ Nothing) <$> get
                xs <- input & traverse (maybe (return $ pure Nothing) runReadWrite)
                return $ lockStep xs === output

return []

run_tests :: IO Bool
run_tests = $quickCheckAll
