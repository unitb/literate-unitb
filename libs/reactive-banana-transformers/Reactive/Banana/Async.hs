module Reactive.Banana.Async where

import Control.Concurrent
import Control.Concurrent.STM
import Control.Monad.Fix
import Control.Monad.Reader
import Control.Monad.RWS
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Either
import Control.Monad.Writer

import Data.Either
import Data.IORef
import Data.List as L
import Data.List.NonEmpty as N
import Data.Maybe

import Reactive.Banana
import Reactive.Banana.Frameworks
import Reactive.Banana.IO

import Safe

type AsyncMoment = AsyncMomentT MomentIO

type Output a = a -> STM ()
type Input a  = STM a

type Pipe a b = Input a -> Output b -> IO ()

type Payload = ()

newtype AsyncMomentT m a = AsyncMoment { _asyncMoment :: WriterT ([STM (IO Payload)],[ThreadId]) m a }
    deriving (Functor,Applicative,MonadIO,MonadTrans
             ,MonadMoment,MonadMomentIO,MonadFix)

instance Monad m => Monad (AsyncMomentT m) where
    {-# INLINE (>>=) #-}
    AsyncMoment m >>= f = AsyncMoment $ m >>= _asyncMoment . f

class Monad m => MonadAsyncMoment m where
    asyncEvent :: Event a 
               -> Pipe a b
               -> m (Event b)
    asyncBehavior :: Behavior a 
                  -> Pipe a b
                  -> m (Event b)
    eventSource :: (Output a -> IO ())
                -> m (Event a)


instance MonadAsyncMoment m => MonadAsyncMoment (EitherT e m) where
    asyncEvent    = fmap lift <$> asyncEvent 
    asyncBehavior = fmap lift <$> asyncBehavior 
    eventSource   = lift <$> eventSource
instance MonadAsyncMoment m => MonadAsyncMoment (MaybeT m) where
    asyncEvent    = fmap lift <$> asyncEvent 
    asyncBehavior = fmap lift <$> asyncBehavior 
    eventSource   = lift <$> eventSource
instance MonadAsyncMoment m => MonadAsyncMoment (ReaderT r m) where
    asyncEvent    = fmap lift <$> asyncEvent 
    asyncBehavior = fmap lift <$> asyncBehavior 
    eventSource   = lift <$> eventSource
instance (MonadAsyncMoment m,Monoid w) => MonadAsyncMoment (RWST r w s m) where
    asyncEvent    = fmap lift <$> asyncEvent 
    asyncBehavior = fmap lift <$> asyncBehavior 
    eventSource   = lift <$> eventSource
instance MonadAsyncMoment m => MonadAsyncMoment (StateT s m) where
    asyncEvent    = fmap lift <$> asyncEvent 
    asyncBehavior = fmap lift <$> asyncBehavior 
    eventSource   = lift <$> eventSource
instance (MonadAsyncMoment m,Monoid w) => MonadAsyncMoment (WriterT w m) where
    asyncEvent    = fmap lift <$> asyncEvent 
    asyncBehavior = fmap lift <$> asyncBehavior 
    eventSource   = lift <$> eventSource

oneof :: [STM (IO a)] -> IO (NonEmpty a)
oneof xs = sequence =<< oneof' xs

oneof' :: [STM a] -> IO (NonEmpty a)
oneof' xs = do
        atomically $ do
            ys <- catMaybes <$> mapM try xs
            maybe retry return $ nonEmpty ys
    where
        try :: STM a -> STM (Maybe a)
        try x = (Just <$> x) `orElse` return Nothing

-- asyncEvent :: MonadMomentIO m
--            => Event a 
--            -> Pipe a b
--            -> AsyncMomentT m (Event b)

instance MonadMomentIO m => MonadAsyncMoment (AsyncMomentT m) where
    asyncEvent input f = AsyncMoment $ do
            (output,h) <- liftMomentIO newEvent        
            inV  <- liftIO newEmptyTMVarIO
            outV <- liftIO newEmptyTMVarIO
            t <- liftIO $ do
                forkIO $ f (takeTMVar inV) (putTMVar outV)
            -- let h' x = h x >> return 3
            tell ([h <$> takeTMVar outV],[t])
            liftMomentIO $ reactimate $ atomically . putTMVar inV <$> input
            return output
    asyncBehavior input f = AsyncMoment $ do
            (output,h) <- liftMomentIO newEvent        
            inV  <- liftIO newEmptyTMVarIO
            outV <- liftIO newEmptyTMVarIO
            t <- liftIO $ do
                forkIO $ f (takeTMVar inV) (putTMVar outV)
            -- let h' x = h x >> return 7
            tell ([h <$> takeTMVar outV],[t])
            liftMomentIO $ do
                initInput <- valueB input
                liftIOLater $ atomically $ putTMVar inV initInput
                reactimate' =<< changes (atomically . putTMVar inV <$> input)
            return output

    eventSource f = AsyncMoment $ do
            (output,h) <- liftMomentIO newEvent        
            outV <- liftIO newEmptyTMVarIO
            t <- liftIO $ do
                forkIO $ f (putTMVar outV)
            tell ([h <$> takeTMVar outV],[t])
            return output

pollKeyboard :: MonadAsyncMoment m
             => m (Event String)
pollKeyboard = do
    eventSource $ \out -> forever $ do
        atomically . out =<< getLine

makeTimer :: MonadAsyncMoment m
          => Int 
          -> m (Event ())
makeTimer t = do
    eventSource $ \out -> forever $ do
        timer <- registerDelay t
        atomically $ do
            guard =<< readTVar timer
        
        atomically $ out ()

{-# INLINE runAsync #-}
runAsync :: AsyncMoment (Event a)
         -> IO a
runAsync m = runAsyncT m id

{-# INLINE runAsyncT #-}
runAsyncT :: AsyncMomentT m (Event a)
          -> (forall a. m a -> MomentIO a)
          -> IO a
runAsyncT (AsyncMoment moment) run = do
        exit  <- newEmptyTMVarIO
        watch <- newIORef ([],[])
        net   <- compile $ do
            (e,w) <- run $ runWriterT moment
            liftIO $ writeIORef watch w
            reactimate $ atomically . putTMVar exit <$> e
        (ws,ts) <- readIORef watch
        actuate net
        x <- fix $ \rec -> do
            xs <- oneof $ 
                    (return . Right <$> takeTMVar exit) : 
                    L.map (fmap $ fmap Left) ws
            maybe rec return $ headMay $ rights $ N.toList xs
        forM_ ts killThread
        return x

