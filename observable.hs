module Observable 
	( Observable, new_obs, modify_obs
	, write_obs, read_obs, observe
	, observe_with )
where

import Control.Concurrent
import Control.Monad

data Observable a = Obs (MVar a) (MVar [IO ()])

new_obs :: a -> IO (Observable a)
new_obs x = do
	v  <- newMVar x
	vs <- newMVar []
	return $ Obs v vs

read_obs :: Observable a -> IO a
read_obs (Obs v _) = readMVar v

write_obs :: Observable a -> a -> IO ()
write_obs v x = modify_obs v (const $ return x)

modify_obs :: Observable a -> (a -> IO a) -> IO ()
modify_obs (Obs v vs) f = do
		modifyMVar_ v f
		vs <- readMVar vs
		sequence vs
		return ()

observe :: Observable a -> MVar () -> IO ()
observe (Obs _ vs) v = do
		modifyMVar_ vs $ \vs -> do
			return $ void (tryPutMVar v ()) : vs
		
observe_with :: Observable a -> Chan b -> b -> IO ()
observe_with (Obs _ vs) ch t = do
		modifyMVar_ vs $ \vs -> do
			return $ writeChan ch t : vs

test = do
		ch <- newChan :: IO (Chan String)
		o1 <- new_obs (3 :: Int)
		o2 <- new_obs "allo"
		observe_with o1 ch "salut"
		observe_with o2 ch "bonjour"
		forkIO $ forM_ [1..3] $ const $ do
			x <- readChan ch 
			putStrLn x
			threadDelay 1000000
		write_obs o1 7
		write_obs o2 "oo"
		write_obs o1 3
		