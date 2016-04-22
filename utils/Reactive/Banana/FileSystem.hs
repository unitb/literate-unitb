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

import qualified Data.Map as M
-- import           Data.TypeList

import Prelude hiding (writeFile,readFile)

import Reactive.Banana
import Reactive.Banana.Combinators.Extras
import Reactive.Banana.Frameworks
import Reactive.Banana.IO
import Reactive.Banana.Property hiding (run_tests)

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

prop_ :: String
     -> [Maybe (Maybe String,Maybe String,Maybe ())] -> Property
prop_ c = satisfies' prog' prop (fs,())
    where
        f1 = "/f1"
        f2 = "./f2"
        fs :: MockFileSystemState
        fs = create' $ do
                files %= M.insert f1 (Just c)
        prog' :: Event (Maybe String,Maybe String,Maybe ()) 
              -> FSMoment (Event (Maybe (Maybe String),Maybe (Maybe String)))
        -- prog' = prog^.uncurriedEvent' . mapping (mapping $ splittingEvent')
        prog' = prog^.packageEventFun'
        -- p :: Event (Maybe String,Maybe String,Maybe ()) 
        --   -> FSMoment ((Event (Maybe String),Event (Maybe String)))
        -- p = prog^.uncurriedEvent' . mapping (mapping $ iso _ _)
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
                xs <- forM input $ maybe (return Nothing) $ \(x,y,tick) -> do
                    mapM_ (assign _1 . Just) x
                    mapM_ (assign _2 . Just) y
                    forM tick $ \_ -> do
                        liftA2 (,) 
                            (Just <$> use _1)
                            (Just <$> use _2)
                return $ xs === output

return []

run_tests :: IO Bool
run_tests = $quickCheckAll
