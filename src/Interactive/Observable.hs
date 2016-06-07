module Interactive.Observable where

import Control.Concurrent
import Control.Concurrent.STM
import Control.Monad

data Observable a = Obs (TVar a) (TVar [STM ()])

new_obs :: a -> IO (Observable a)
new_obs x = do
    v  <- newTVarIO x
    vs <- newTVarIO []
    return $ Obs v vs

read_obs :: Observable a -> IO a
read_obs = atomically . read_obs_STM

read_obs_STM :: Observable a -> STM a
read_obs_STM (Obs v _) = readTVar v

reads_obs :: Observable a -> (a -> b) -> IO b
reads_obs = fmap atomically . reads_obs_STM

reads_obs_STM :: Observable a -> (a -> b) -> STM b
reads_obs_STM obs f = do
        x <- read_obs_STM obs
        return $ f x

write_obs :: Eq a => Observable a -> a -> IO ()
write_obs = fmap atomically . write_obs_STM

write_obs_STM :: Eq a => Observable a -> a -> STM ()
write_obs_STM v x = modify_obs_STM' v (const x)

write_obs_fast_STM :: Observable a -> a -> STM ()
write_obs_fast_STM v x = modify_obs_fast_STM' v (const x)

write_obs_fast :: Observable a -> a -> IO ()
write_obs_fast v x = modify_obs_fast' v (const x)

modify_obs_fast' :: Observable a -> (a -> a) -> IO ()
modify_obs_fast' obs = atomically . modify_obs_fast_STM' obs


modify_obs_fast_STM' :: Observable a -> (a -> a) -> STM ()
modify_obs_fast_STM' obs = modify_obs_fast_STM obs . fmap return

modify_obs_fast_STM :: Observable a -> (a -> STM a) -> STM ()
modify_obs_fast_STM (Obs v vs) f = do
        writeTVar v =<< f =<< readTVar v
        vs <- readTVar vs
        sequence_ vs

modify_obs' :: Eq a => Observable a -> (a -> a) -> IO ()
modify_obs' obs = atomically . modify_obs_STM' obs

modify_obs_STM' :: Eq a => Observable a -> (a -> a) -> STM ()
modify_obs_STM' obs = modify_obs_STM obs . fmap return

modify_obs_STM :: Eq a => Observable a -> (a -> STM a) -> STM ()
modify_obs_STM (Obs v vs) f = do
        x <- readTVar v
        y <- f x
        writeTVar v y
        if x /= y then do
            vs <- readTVar vs
            sequence_ vs
        else
            return ()

observe :: Observable a -> TMVar () -> IO ()
observe (Obs _ vs) v = atomically $ do
        modifyTVar vs $ \vs -> do
            void (tryPutTMVar v ()) : vs
        
observe_with :: Observable a -> TQueue b -> b -> IO ()
observe_with (Obs _ vs) ch t = atomically $ do
        modifyTVar vs $ \vs -> do
            writeTQueue ch t : vs

test :: IO ()
test = do
        ch <- newTQueueIO :: IO (TQueue String)
        o1 <- new_obs (3 :: Int)
        o2 <- new_obs "allo"
        observe_with o1 ch "salut"
        observe_with o2 ch "bonjour"
        forkIO $ replicateM_ 3 $ do
            x <- atomically $ readTQueue ch 
            putStrLn x
            threadDelay 1000000
        write_obs o1 7
        write_obs o2 "oo"
        write_obs o1 3
        