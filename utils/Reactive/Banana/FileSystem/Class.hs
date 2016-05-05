{-# LANGUAGE TypeFamilies #-}
module Reactive.Banana.FileSystem.Class where

import Control.Monad.Reader
import Control.Monad.RWS
import Control.Monad.State
import Control.Monad.Writer

import Reactive.Banana
import Reactive.Banana.IO

import Utilities.FileSystem

class Monad m => MonadFSMoment m where
    reactimateFS' :: Event (Future (FileSystemM ()))
                  -> m ()
    mapEventFS :: (a -> FileSystemM b)
               -> Event a
               -> m (Event b)

      -- Defaults
    default reactimateFS' :: (t m' ~ m,MonadTrans t,MonadFSMoment m')
                          => Event (Future (FileSystemM ()))
                          -> t m' ()
    reactimateFS' = lift . reactimateFS'
    default mapEventFS :: (t m' ~ m,MonadTrans t,MonadFSMoment m')
                       => (a -> FileSystemM b)
                       -> Event a
                       -> t m' (Event b)
    mapEventFS = fmap lift . mapEventFS

instance MonadFSMoment m => MonadFSMoment (ReaderT r m)
instance MonadFSMoment m => MonadFSMoment (StateT s m)
instance (MonadFSMoment m,Monoid w) => MonadFSMoment (WriterT w m)
instance (MonadFSMoment m,Monoid w) => MonadFSMoment (RWST r w s m)
