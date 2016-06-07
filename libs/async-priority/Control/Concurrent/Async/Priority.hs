{-# LANGUAGE LambdaCase #-}
module Control.Concurrent.Async.Priority 
    ( SchedT, Sched, Priority (..), SchedSTM 
    , Async
    , async, cancel, waitSTM, wait
    , mapConcurrently
    , forConcurrently
    , withScheduler
    , insideSchedT
    , unfail' 
    , unfail
    , atomically' 
    , Concurrently
    , concurrently )
where

import Control.Applicative
import qualified Control.Concurrent.Async as A
import Control.Concurrent.STM hiding (TQueue)
import Control.Concurrent.Async.Queue 
import Control.Concurrent
import Control.DeepSeq
import qualified Control.Exception as Exc
import Control.Lens

import Control.Monad.Catch
import Control.Monad.Reader
import Control.Monad.Trans.Lens

import Control.Precondition

import Data.Semigroup

import GHC.Generics

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

insideSchedT :: Setter (SchedT s m a) (SchedT s m' b) (m a) (m' b)
insideSchedT = iso runSchedT SchedT . insideReaderT

atomically' :: MonadIO m => SchedSTM s a -> SchedT s m a
atomically' = insideSchedT %~ liftIO . atomically

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

newtype Concurrently s a = Concurrently { runConcurrently :: Sched s a }

instance Functor (Concurrently s) where
  fmap f (Concurrently a) = Concurrently $ f <$> a

instance Applicative (Concurrently s) where
  pure = Concurrently . return
  Concurrently fs <*> Concurrently as =
    Concurrently $ (\(f, a) -> f a) <$> concurrently fs as

instance Semigroup a => Semigroup (Concurrently s a) where
  (<>) = liftA2 (<>)

instance (Monoid a) => Monoid (Concurrently s a) where
  mempty = pure mempty
  mappend = liftA2 mappend

concurrently :: Sched s a
             -> Sched s b
             -> Sched s (a,b)
concurrently left right = concurrently' left right (collect [])
  where
    collect [Left a, Right b] _ = return (a,b)
    collect [Right b, Left a] _ = return (a,b)
    collect xs m = do
        e <- liftIO $ takeMVar m
        case e of
            Left ex -> throwSched ex
            Right r -> collect (r:xs) m

concurrently' :: Sched s a -> Sched s b
             -> (MVar (Either SomeException (Either a b)) -> Sched s r)
             -> Sched s r
concurrently' left right collect = do
    let run = runReaderT . runSchedT
    done <- liftIO newEmptyMVar
    SchedT $ ReaderT $ \s -> mask $ \restore -> do
        lid <- forkIO $ restore (run left s >>= putMVar done . Right . Left)
                             `catchAll` (putMVar done . Left)
        rid <- forkIO $ restore (run right s >>= putMVar done . Right . Right)
                             `catchAll` (putMVar done . Left)
        let stop = killThread rid >> killThread lid
                   -- kill right before left, to match the semantics of
                   -- the version using withAsync. (#27)
        r <- restore (run (collect done) s) `onException` stop
        stop
        return r

mapConcurrently :: Traversable t => (a -> Sched s b) -> t a -> Sched s (t b)
mapConcurrently f = runConcurrently . traverse (Concurrently . f)

forConcurrently :: Traversable t => t a -> (a -> Sched s b)-> Sched s (t b)
forConcurrently = flip mapConcurrently

throwSched :: (Exception e,MonadIO m) 
           => e 
           -> SchedT s m a
throwSched = SchedT . liftIO . Exc.throwIO
