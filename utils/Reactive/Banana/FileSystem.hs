{-# LANGUAGE TypeFamilies,StandaloneDeriving #-}
module Reactive.Banana.FileSystem 
    ( module Utilities.FileSystem
    , FSMomentT
    , FSMoment
    , runFSMoment
    , interpretFSMomentT
    , MonadFSMoment(..)
    , fileSystemEvent
    , reactimateFS
    , run_tests )
where

import Control.Invariant hiding ((===))
import Control.Lens hiding (uncurried)
import Control.Monad
import Control.Monad.Fix
import Control.Monad.IO.Class
import Control.Monad.Reader
import Control.Monad.RWS
import Control.Monad.State
import Control.Monad.Trans.Lens
import Control.Monad.Writer

import Data.List.NonEmpty as NE (NonEmpty(..),toList)
import qualified Data.Map as M
import Data.Maybe

import Prelude hiding (writeFile,readFile)

import Reactive.Banana
import Reactive.Banana.Combinators.Extras
import Reactive.Banana.FileSystem.Class
import Reactive.Banana.IO
import Reactive.Banana.Keyboard.Class
import Reactive.Banana.Property hiding (run_tests,(===))

import Test.QuickCheck

import Utilities.FileSystem

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
    newtype EventList (FSMomentT m) a = FSEvent { getFSEvent :: EventList m a }
    type InitF (FSMomentT m) = (MockFileSystemState,InitF m) 
    getEvent f = getEvent f . getFSEvent
    interpret' f = convertEventList FSEvent getFSEvent . interpretFSMomentT f

fileSystemEvent :: Iso (EventList (FSMomentT m) a)
                       (EventList (FSMomentT m) b)
                       (EventList m a)
                       (EventList m b)
fileSystemEvent = iso getFSEvent FSEvent

deriving instance Functor (EventList m) => Functor (EventList (FSMomentT m))

instance MonadMomentIO m => MonadFSMoment (FSMomentT m) where 
    reactimateFS' e = reactimateFSImpl $ e & mapped.mapped.mapped %~ return
    mapEventFS f e = do
            (e',h) <- liftMomentIO newEvent
            reactimateFSImpl $ e & mapped %~ pure.fmap h.f
            return e'

instance KeyboardMonad m => KeyboardMonad (FSMomentT m) where
    specializeKeyboard b (FileSystemMomentT m) = FileSystemMomentT $
            m & insideReaderT . insideWriterT %~ specializeKeyboard b

reactimateFS :: MonadFSMoment m
             => Event (FileSystemM ())
             -> m ()
reactimateFS e = reactimateFS' $ pure <$> e


reactimateFSImpl :: Event (Future (FileSystemM (IO ())))
                 -> FSMomentT m' ()
reactimateFSImpl e = FileSystemMomentT $ ReaderT $ \react -> runReactimate react e

ioReactimate :: MonadMomentIO m => ReactimateType () m 
ioReactimate = ReactimateType $ \e -> 
    reactimate' $ e & mapped.mapped %~ join.runFS

mockFSReactimate :: Monad m
                 => ReactimateType [Event (Future (FileSystemM (IO ())))] m 
mockFSReactimate = ReactimateType $ \e -> tell [e]

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
                reactimate e'
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
prop_file_io c = satisfiesWith' showInput showOutput prog' prop (fs,()) . map (FSEvent . MomentIOEvent)
    where
        showInput :: [EventList FSMoment (Maybe String, Maybe String, Maybe ())]
                  -> [[String]]
        showInput xs = [ xs & traverse %~ show . getEvent (view _1)
                       , xs & traverse %~ show . getEvent (view _2)
                       , xs & traverse %~ show . getEvent (view _3) ]
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
                
        prop :: [EventList FSMoment (Maybe String, Maybe String,Maybe ())]
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
                xs <- input & traverse (maybe (return $ pure Nothing) runReadWrite . getMomentIOEvent . getFSEvent)
                return $ lockStep xs === output

return []

run_tests :: IO Bool
run_tests = $quickCheckAll
