module Pipes.Lift.Async where

import Control.Concurrent.Async.Priority
import Control.Lens
import Control.Monad.Catch

import Pipes
import Pipes.Safe ()
import Pipes.Lift

withSchedulerP :: (MonadMask m,MonadIO m)
               => Int
               -> (forall s. Proxy a' a b' b (SchedT s m) r)
               -> Proxy a' a b' b m r
withSchedulerP n p = withScheduler n $ distribute p

instance MFunctor (SchedT s) where
    hoist = over insideSchedT
