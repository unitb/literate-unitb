module Reactive.Banana.IO where

import Control.Monad.Reader
import Control.Monad.RWS
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Either
import Control.Monad.Writer

import Reactive.Banana
import Reactive.Banana.Frameworks

class (MonadMoment m,MonadIO m) => MonadMomentIO m where
    liftMomentIO :: MomentIO a -> m a

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

instance MonadMomentIO m => MonadMomentIO (ReaderT r m) where
    liftMomentIO = lift . liftMomentIO
instance (MonadMomentIO m,Monoid w) => MonadMomentIO (RWST r w s m) where
    liftMomentIO = lift . liftMomentIO
instance MonadMomentIO m => MonadMomentIO (StateT s m) where
    liftMomentIO = lift . liftMomentIO
instance MonadMomentIO m => MonadMomentIO (MaybeT m) where
    liftMomentIO = lift . liftMomentIO
instance MonadMomentIO m => MonadMomentIO (EitherT e m) where
    liftMomentIO = lift . liftMomentIO
instance (MonadMomentIO m,Monoid w) => MonadMomentIO (WriterT w m) where
    liftMomentIO = lift . liftMomentIO
