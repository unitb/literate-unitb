{-# LANGUAGE GADTs,KindSignatures,TypeFamilies #-}
module Reactive.Banana.IO where

import Control.Lens
import Control.Monad.Reader
import Control.Monad.RWS
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Either
import Control.Monad.Writer

import Data.IORef
import Data.List.Ordered

import Reactive.Banana as R hiding (interpret,apply)
import Reactive.Banana.Combinators.Extras
import Reactive.Banana.Frameworks as R

class (MonadMoment m,MonadIO m) => MonadMomentIO m where
    liftMomentIO :: MomentIO a -> m a
    default liftMomentIO :: (m ~ t m', MonadMomentIO m',MonadTrans t) 
                         => MomentIO a -> t m' a
    liftMomentIO = lift . liftMomentIO

class MonadMomentIO m => Frameworks m where
    type EventList m a :: *
    type InitF m :: *
    type InitF m = ()
    interpret' :: (Event a -> m (Event b)) 
               -> InitF m
               -> [EventList m a] 
               -> IO ([EventList m a],[Maybe b])

interpretFrameworks' :: (Event a -> MomentIO (Event b))
                     -> [Maybe a] 
                     -> IO ([Maybe a],[Maybe b])
interpretFrameworks' f xs = do
        output <- newIORef []
        let insertH k e = ((k,e):)
            elemsH = map snd . sortOn fst . reverse
            run e = do
                e' <- f $ filterJust e
                n <- accumB 0 $ unionWith const (succ <$ e) (succ <$ e')
                reactimate 
                    $ fmap (modifyIORef output) 
                    $ insertH <$> n <@> (eventPair e e' & mapped._1 %~ join)
        (add,h) <- newAddHandler
        n <- compile $ do
            run =<< fromAddHandler add
        actuate n
        forM_ xs h
        unzip.elemsH <$> readIORef output

instance MonadMoment m => MonadMoment (ReaderT r m) where
    liftMoment = lift . liftMoment
instance (MonadMoment m,Monoid w) => MonadMoment (RWST r w s m) where
    liftMoment = lift . liftMoment
instance MonadMoment m => MonadMoment (StateT s m) where
    liftMoment = lift . liftMoment
instance MonadMoment m => MonadMoment (MaybeT m) where
    liftMoment = lift . liftMoment
instance MonadMoment m => MonadMoment (EitherT e m) where
    liftMoment = lift . liftMoment
instance (MonadMoment m,Monoid w) => MonadMoment (WriterT w m) where
    liftMoment = lift . liftMoment

instance MonadMomentIO MomentIO where
    liftMomentIO = id

instance Frameworks MomentIO where
    type EventList MomentIO a = Maybe a
    interpret' f () = interpretFrameworks' f

instance MonadMomentIO m => MonadMomentIO (ReaderT r m) where
instance (MonadMomentIO m,Monoid w) => MonadMomentIO (RWST r w s m) where
instance MonadMomentIO m => MonadMomentIO (StateT s m) where
instance MonadMomentIO m => MonadMomentIO (MaybeT m) where
instance MonadMomentIO m => MonadMomentIO (EitherT e m) where
instance (MonadMomentIO m,Monoid w) => MonadMomentIO (WriterT w m) where

reactimateB :: MonadMomentIO m
            => Behavior (IO ())
            -> m ()
reactimateB b = liftMomentIO $ do
        liftIOLater =<< valueB b
        reactimate' =<< changes b

display :: MonadMomentIO m
        => Behavior String
        -> m ()
display str = 
    reactimateB $ putStrLn <$> str

fromFuture :: MonadMomentIO m
           => Event (Future a)
           -> m (Event a)
fromFuture e = liftMomentIO $ do
        (e',h) <- newEvent
        reactimate' $ fmap h <$> e
        return e'
