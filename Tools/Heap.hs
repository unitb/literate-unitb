module Tools.Heap where

import Data.Map

import Control.Monad.Trans
import Control.Monad.Trans.State

data HeapT a b m c = HeapT { runHeapT :: StateT (Map a b) m c }

instance Monad m => Monad (HeapT a b m) where
    (>>=) x y = HeapT $ do
        z <- runHeapT x
        runHeapT (y z)
    return x = HeapT $ return x

instance MonadTrans (HeapT a b) where
    lift x = HeapT $ lift x
    
instance MonadIO m => MonadIO (HeapT a b m) where
    liftIO x = HeapT $ liftIO x
    
focus :: (Monad m,Ord a) => a -> StateT b m c -> HeapT a b m c
focus x m = HeapT $ StateT $ \s -> do
        let s0 = s ! x
        (y,s1) <- runStateT m s0
        return (y, insert x s1 s)

new :: (Ord a, Monad m) => a -> HeapT a b m b -> HeapT a b m ()
new x m = do
        y <- m
        HeapT $ modify $ insert x y

execHeapT :: Monad m
          => HeapT a1 b m a -> m (Map a1 b)
execHeapT m = execStateT (runHeapT m) empty

evalHeapT :: Monad m
          => HeapT a1 b m a -> m a
evalHeapT m = evalStateT (runHeapT m) empty
