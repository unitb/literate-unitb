{-# LANGUAGE TypeFamilies #-}
module Reactive.Banana.Async.Class where

import Control.Lens
import Control.Monad.Reader
import Control.Monad.RWS
import Control.Monad.State
import Control.Monad.Writer

import Data.Default
import Data.Map
import Data.Time

import GHC.Generics.Instances

import Reactive.Banana
import Reactive.Banana.Discrete
import Reactive.Banana.IO

type JobBatch lbl a b = JobBatch' (Map lbl) a b
data JobBatch' map a b = JobBatch 
              { _initJobs :: map (a,Either b (IO b))
              , _updateJobs :: Event (map (Maybe (a,IO b)))
              , _killTasks  :: Event ()
              }

makeLenses ''JobBatch'

class MonadMomentIO m => MonadAsyncMoment m where
    pollKeyboard :: m (Event String)
    makeTimer :: NominalDiffTime -> m (Event ())
    jobBatch' :: Ord lbl
              => State (JobBatch lbl a b) z
              -> m (Discrete (Map lbl (a,b)),Discrete (Map lbl (a,())))

        -- Defaults
    default pollKeyboard :: forall m' t. 
                            (t m' ~ m, MonadAsyncMoment m',MonadTrans t) 
                         => t m' (Event String)
    pollKeyboard = lift pollKeyboard
    default makeTimer :: forall m' t. 
                         (t m' ~ m, MonadAsyncMoment m',MonadTrans t) 
                      => NominalDiffTime -> m (Event ())
    makeTimer = lift . makeTimer
    default jobBatch' :: forall m' t a b lbl z. 
                         (t m' ~ m, MonadAsyncMoment m',MonadTrans t,Ord lbl)
              => State (JobBatch lbl a b) z
              -> m (Discrete (Map lbl (a,b)),Discrete (Map lbl (a,())))
    jobBatch' = lift . jobBatch'

instance Monoid1 map => Default (JobBatch' map a b) where
    def = JobBatch mempty1 never never

instance MonadAsyncMoment m => MonadAsyncMoment (ReaderT r m) where
instance MonadAsyncMoment m => MonadAsyncMoment (StateT s m) where
instance (MonadAsyncMoment m,Monoid w) => MonadAsyncMoment (RWST r w s m) where
instance (MonadAsyncMoment m,Monoid w) => MonadAsyncMoment (WriterT w m) where
