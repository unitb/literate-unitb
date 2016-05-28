module Control.Concurrent.Async.Queue (
        -- * TQueue
        Queue,
        newQueue,
        newQueueIO,
        filterQueue,
        readQueue,
        tryReadQueue,
        peekQueue,
        tryPeekQueue,
        writeQueue,
        unGetQueue,
        isEmptyQueue,
        sizeQueue,
  ) where

import GHC.Conc

import Control.Concurrent.STM
import Control.Monad

import Data.Typeable (Typeable)

-- | 'Queue' is an abstract type representing an unbounded FIFO channel.
--
-- @since 2.4
data Queue a = Queue {-# UNPACK #-} !(TVar Int)
                     {-# UNPACK #-} !(TVar [a])
                     {-# UNPACK #-} !(TVar Int)
                     {-# UNPACK #-} !(TVar [a])
  deriving Typeable

instance Eq (Queue a) where
  Queue a _ _ _ == Queue b _ _ _ = a == b

-- |Build and returns a new instance of 'Queue'
newQueue :: STM (Queue a)
newQueue = do
  nRead  <- newTVar 0
  read   <- newTVar []
  nWrite <- newTVar 0
  write  <- newTVar []
  return (Queue nRead read nWrite write)

-- |@IO@ version of 'newQueue'.  This is useful for creating top-level
-- 'Queue's using 'System.IO.Unsafe.unsafePerformIO', because using
-- 'atomically' inside 'System.IO.Unsafe.unsafePerformIO' isn't
-- possible.
newQueueIO :: IO (Queue a)
newQueueIO = do
  nRead  <- newTVarIO 0
  read   <- newTVarIO []
  nWrite <- newTVarIO 0
  write  <- newTVarIO []
  return (Queue nRead read nWrite write)

-- |Write a value to a 'Queue'.
writeQueue :: Queue a -> a -> STM ()
writeQueue (Queue _ _read nWrite write) a = do
  listend <- readTVar write
  modifyTVar nWrite succ
  writeTVar write (a:listend)

-- |Read the next value from the 'Queue'.
readQueue :: Queue a -> STM a
readQueue (Queue nRead read nWrite write) = do
  xs <- readTVar read
  case xs of
    (x:xs') -> do writeTVar read xs'
                  modifyTVar nRead pred
                  return x
    [] -> do ys <- readTVar write
             case ys of
               [] -> retry
               _  -> case reverse ys of
                       [] -> error "readQueue"
                       (z:zs) -> do writeTVar write []
                                    writeTVar nRead =<< readTVar nWrite
                                    writeTVar nWrite 0
                                    writeTVar read zs
                                    return z

-- | A version of 'readQueue' which does not retry. Instead it
-- returns @Nothing@ if no value is available.
tryReadQueue :: Queue a -> STM (Maybe a)
tryReadQueue c = fmap Just (readQueue c) `orElse` return Nothing

-- | Get the next value from the @Queue@ without removing it,
-- retrying if the channel is empty.
peekQueue :: Queue a -> STM a
peekQueue c = do
  x <- readQueue c
  unGetQueue c x
  return x

-- | A version of 'peekQueue' which does not retry. Instead it
-- returns @Nothing@ if no value is available.
tryPeekQueue :: Queue a -> STM (Maybe a)
tryPeekQueue c = do
  m <- tryReadQueue c
  case m of
    Nothing -> return Nothing
    Just x  -> do
      unGetQueue c x
      return m

-- |Put a data item back onto a channel, where it will be the next item read.
unGetQueue :: Queue a -> a -> STM ()
unGetQueue (Queue nRead read _nWrite _write) a = do
  xs <- readTVar read
  modifyTVar nRead succ
  writeTVar read (a:xs)

-- |Returns 'True' if the supplied 'Queue' is empty.
isEmptyQueue :: Queue a -> STM Bool
isEmptyQueue (Queue _ read _ write) = do
  xs <- readTVar read
  case xs of
    (_:_) -> return False
    [] -> do ys <- readTVar write
             case ys of
               [] -> return True
               _  -> return False

filterQueue :: (a -> STM Bool) 
            -> Queue a -> STM ()
filterQueue f (Queue nRead read nWrite write) = do
      modify read  $ filterM f
      writeTVar nRead . length =<< readTVar read
      modify write $ filterM f
      writeTVar nWrite . length =<< readTVar write
    where
      modify v f = writeTVar v =<< f =<< readTVar v

sizeQueue :: Queue a -> STM Int
sizeQueue (Queue _nRead read _nWrite write) = 
    -- liftM2 (+) (readTVar nRead) (readTVar nWrite)
    liftM2 (+) (length <$> readTVar read) (length <$> readTVar write)
