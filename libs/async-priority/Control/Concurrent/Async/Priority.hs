{-# LANGUAGE LambdaCase #-}
module Control.Concurrent.Async.Priority 
    ( SchedT, Sched, Priority (..), SchedSTM 
    , Async
    , async, cancel, waitSTM, wait
    , withScheduler
    , try', trying'
    , unfail'
    , atomically', onException' )
where

import Control.Applicative
import qualified Control.Concurrent.Async as A
import Control.Concurrent.STM hiding (TQueue)
import Control.Concurrent.Async.Queue 
import Control.DeepSeq
import Control.Exception.Lens
import Control.Lens

import Control.Monad.Catch
import Control.Monad.Reader
import Control.Monad.Trans.Lens

import Control.Precondition

import GHC.Generics

import Data.Monoid

newtype SchedT s m a = SchedT { runSchedT :: ReaderT Scheduler m a }
    deriving (Functor,Applicative,Monad,MonadTrans
             ,MonadIO,MonadCatch,MonadThrow
             ,Alternative )
type Sched s = SchedT s IO
type SchedSTM s = SchedT s STM

data Priority = High | Low
    deriving (Show,Eq,Generic)

instance NFData Priority where

data Task = Task (TVar Bool) (IO ())
data Scheduler = Scheduler
        { high :: Queue Task 
        , low  :: Queue Task 
        , currently :: TVar Int 
        , cancelled :: TVar Int }

data Async s a = Async (IO ()) (TMVar (Maybe (A.Async a)))

isActive :: Task -> STM Bool
isActive (Task c _) = readTVar c

start :: Task -> IO ()
start (Task _ t) = t

async :: MonadIO m
      => Priority 
      -> IO a 
      -> SchedT s m (Async s a)
async p cmd = SchedT $ do
    q <- case p of 
        High -> asks high
        Low  -> asks low
    count <- asks currently
    can   <- asks cancelled
    liftIO $ do
        v <- newEmptyTMVarIO
        enabled <- newTVarIO True
        let cancel = mapM_ (mapM_ A.cancel) =<< 
                atomically (do
                    modifyTVar can succ
                    writeTVar enabled False 
                    x <- tryTakeTMVar v
                    putTMVar v Nothing
                    return x)
            trigger x = do
                A.async x >>= atomically . putTMVar v . Just
        atomically $ writeQueue q $ Task enabled $ trigger $ do
            finally cmd $ 
                atomically (modifyTVar count pred)
        return $ Async cancel v

cancel :: MonadIO m 
       => Async s a -> SchedT s m ()
cancel (Async c _) = liftIO c

waitSTM :: Pre => Async s a -> SchedSTM s a
waitSTM (Async _ v) = lift $ do
    maybe undefined' A.waitSTM =<< readTMVar v

wait :: (Pre,MonadIO m) => Async s a -> SchedT s m a
wait = atomically' . waitSTM

onException' :: Sched s a -> Sched s b -> Sched s a
onException' (SchedT (ReaderT m0)) (SchedT (ReaderT m1)) = SchedT $ ReaderT $ \r -> onException (m0 r) (m1 r)

try' :: Exception e
     => Sched s a -> Sched s (Either e a)
try' = insideSchedT %~ try

insideSchedT :: Setter (SchedT s m a) (SchedT s m' b) (m a) (m' b)
insideSchedT = iso runSchedT SchedT . insideReaderT

trying' :: MonadCatch m
        => Getting (First e) SomeException e 
        -> SchedT s m a 
        -> SchedT s m (Either e a)
trying' ln = insideSchedT %~ trying ln

atomically' :: MonadIO m => SchedSTM s a -> SchedT s m a
atomically' = insideSchedT %~ liftIO . atomically

-- withScheduler :: Int 
--               -> (forall s. Sched s a) 
--               -> IO a
-- withScheduler = withScheduler'

unfail' :: (a -> SchedSTM s b) -> a -> SchedSTM s (Either a b)
unfail' f x = f x & insideSchedT %~ fmap (maybe (Left x) Right) . unfail

unfail :: STM a -> STM (Maybe a)
unfail cmd = (Just <$> cmd) `orElse` return Nothing

oneOf :: [STM a] -> STM [a]
oneOf = (\xs -> guard (not $ null xs) >> return xs) . catMaybes <=< mapM unfail

when' :: Bool -> STM a -> STM a
when' True  = id
when' False = const retry

withScheduler :: (MonadMask m,MonadIO m)
              => Int 
              -> (forall s. SchedT s m a) 
              -> m a
withScheduler bound (SchedT m) = do
        (th,sch) <- liftIO $ makeScheduler bound
        finally  
            (runReaderT m sch)
            (liftIO $ A.cancel th)

pullMany :: Int -> Queue Task -> STM [Task]
pullMany 0 _ = return []
pullMany n q = pullOne q >>= \case
        Just x -> (x:) <$> pullMany (n-1) q
        Nothing -> return []

pullOne :: Queue Task -> STM (Maybe Task)
pullOne q = do
    tryReadQueue q >>= \case
        Just x -> do
            active <- isActive x
            if active then return $ Just x
                      else pullOne q
        Nothing -> return Nothing

makeScheduler :: Int -> IO (A.Async (),Scheduler)
makeScheduler bound = do
        high  <- newQueueIO
        low   <- newQueueIO
        count <- newTVarIO 0
        can   <- newTVarIO 0
        let pull n = do
                xs <- pullMany n high
                ys <- pullMany (n - length xs) low
                return $ xs ++ ys
        sch <- A.async $ forever $ do
            xs <- atomically $ do
                n <- readTVar count
                c <- readTVar can
                hLn <- sizeQueue high
                lLn <- sizeQueue low
                oneOf 
                    [ when' (hLn + lLn < 2*c) $ do
                        filterQueue isActive high
                        filterQueue isActive low
                        writeTVar can 0
                        return []
                    , when' (n < bound) $ do
                        xs <- pull (bound - n)
                        guard (not $ null xs)
                        modifyTVar count (length xs +)
                        return $ map start xs
                    ]
            sequence_ $ concat xs
        return (sch,Scheduler high low count can)
