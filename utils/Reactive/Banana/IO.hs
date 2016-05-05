{-# LANGUAGE GADTs,KindSignatures,TypeFamilies,StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Reactive.Banana.IO 
    ( module Reactive.Banana.IO 
    , module R
    , tell )
where

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
import Reactive.Banana.Frameworks as R hiding (reactimate,reactimate')
import qualified Reactive.Banana.Frameworks as R

import Test.QuickCheck

class (MonadMoment m,MonadIO m) => MonadMomentIO m where
    liftMomentIO :: MomentIO a -> m a
    default liftMomentIO :: (m ~ t m', MonadMomentIO m',MonadTrans t) 
                         => MomentIO a -> t m' a
    liftMomentIO = lift . liftMomentIO

class (MonadMomentIO m,Functor (EventList m)) => Frameworks m where
    data EventList m :: * -> *
    type InitF m :: *
    type InitF m = ()
    getEvent :: (a -> Maybe b) 
             -> EventList m a
             -> Maybe b
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

convertEventList :: Functor m
                 => (fb -> gb)
                 -> (ga -> fa)
                 -> ([fa] -> m ([fb],c))
                 -> ([ga] -> m ([gb],c))
convertEventList f g cmd = (mapped._1.traverse %~ f) . cmd . map g

convertEventList' :: Functor m
                  => Iso ga gb fa fb
                  -> ([fa] -> m ([fb],c))
                  -> ([ga] -> m ([gb],c))
convertEventList' i = withIso i $ flip convertEventList

instance Frameworks MomentIO where
    newtype EventList MomentIO a = MomentIOEvent { getMomentIOEvent :: Maybe a }
        deriving (Functor,Show,Arbitrary)
    getEvent f (MomentIOEvent x) = x >>= f
    interpret' f () = convertEventList MomentIOEvent getMomentIOEvent
                    $ interpretFrameworks' f

instance Frameworks m => Frameworks (ReaderT r m) where
    newtype EventList (ReaderT r m) a = ReaderEvent { getReaderEvent :: EventList m a }
    type InitF (ReaderT r m) = (r,InitF m)
    getEvent f = getEvent f . getReaderEvent
    interpret' f (r,x) = convertEventList ReaderEvent getReaderEvent
                $ interpret' (\e -> runReaderT (f e) r) x

readerEvent :: Iso (EventList (ReaderT r m) a)
                   (EventList (ReaderT r m) b)
                   (EventList m a) 
                   (EventList m b) 
readerEvent = iso getReaderEvent ReaderEvent

deriving instance Functor (EventList m) => Functor (EventList (ReaderT r m))

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
        R.reactimate' =<< changes b

display :: MonadMomentIO m
        => Behavior String
        -> m ()
display str = 
    reactimateB $ putStrLn <$> str

displayM :: MonadMomentIO m
         => Behavior a
         -> (a -> Writer String z)
         -> m ()
displayM b f = 
    reactimateB $ putStrLn.execWriter .f <$> b

reactimate :: MonadMomentIO m 
           => Event (IO ()) -> m ()
reactimate = liftMomentIO . R.reactimate

reactimate' :: MonadMomentIO m 
            => Event (Future (IO ())) -> m ()
reactimate' = liftMomentIO . R.reactimate'

fromFuture :: MonadMomentIO m
           => Event (Future a)
           -> m (Event a)
fromFuture e = liftMomentIO $ do
        (e',h) <- newEvent
        R.reactimate' $ fmap h <$> e
        return e'
