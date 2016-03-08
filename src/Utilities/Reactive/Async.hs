{-# LANGUAGE TupleSections
    , ScopedTypeVariables
    , RecursiveDo
    , TemplateHaskell #-}
module Utilities.Reactive.Async where

import Control.Concurrent.Async
import Control.Exception
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Control.Lens

import Data.Foldable as F
import Data.Map.Class as M (mapEither)
import qualified Data.Map.Class as M
import Data.Maybe
import Data.Proxy

import Reactive.Banana
import Reactive.Banana.Frameworks

import Utilities.Table

type JobQueue = JobQueue' Proxy
type JobQueueInternal = JobQueue' Async

data JobQueue' f k a b = JobQueue 
        { _pendingJobs'  :: Table k (a,f b)
        , _completedJobs :: Table k (a,Either SomeException b) }

makeLenses ''JobQueue'

pendingJobs :: Lens' (JobQueue k a b) (Table k a)
pendingJobs = pendingJobs'.lens (M.map fst) (const $ M.map (,Proxy))

updateQueue :: (M.IsKey Table k,Eq a)
            => (k -> a -> IO b)
            -> Future (Table k a)
            -> Future (JobQueueInternal k a b -> MaybeT IO (JobQueueInternal k a b))
updateQueue f = fmap $ updateQueue' f

newQueue :: (k -> a -> IO b)
         -> Table k a
         -> IO (JobQueueInternal k a b)
newQueue f m = JobQueue <$> M.traverseWithKey (launch . f) m <*> pure M.empty

launch :: (t -> IO a) -> t -> IO (t, Async a)
launch f x = (x,) <$> async (f x)

updateQueue' :: (M.IsKey Table k,Eq a)
             => (k -> a -> IO b)
             -> Table k a
             -> JobQueueInternal k a b 
             -> MaybeT IO (JobQueueInternal k a b)
updateQueue' f m' m = do
        let new = m' `diffNew` (m^.pendingJobs') `diffNew` (m^.completedJobs)
            old = (m^.pendingJobs') `diffOld` m'
            diffNew = M.differenceWith isNew
            diffOld = M.differenceWith isOld
            isNew x (y,_) = guard (x /= y) >> return x
            isOld (x,a) y = guard (x /= y) >> return (x,a)
            isSame (x,a) y = guard (x == y) >> return (x,a)
            completed = M.mapMaybe id $ M.intersectionWith isSame (m^.completedJobs) m'
            obsolete  = M.mapMaybe id $ M.intersectionWith isOld (m^.completedJobs) m'
        lift $ for_ old (traverse cancel) 
        new' <- lift $ M.traverseWithKey (launch . f) new
        guard $ not $ and [M.null new', M.null old, M.null obsolete]
        return $ m
            & pendingJobs'  %~ (\m -> new' `M.union` (m `M.difference` old))
            & completedJobs .~ completed
                    --JobQueue _ _
                --return $ new' `M.union` (m `M.difference` old)

collectResults :: M.IsKey Table k => JobQueueInternal k a b -> MaybeT IO (JobQueueInternal k a b)
collectResults jobs = do
     let collect (y,x) = maybe (Left (y,x)) (Right.(y,)) <$> poll x
     (pend,comp) <- lift $ mapEither id <$> traverse collect (jobs^.pendingJobs')
     guard $ not $ M.null comp
     return $ jobs
        & pendingJobs' .~ pend
        & completedJobs %~ M.union comp

asyncTraverse :: (Show k,Show a,M.IsKey Table k,Eq a)
              => Event z 
              -> (a -> IO b)
              -> Behavior (Table k a)
              -> MomentIO (Behavior (Table k b))
asyncTraverse e f = asyncTraverseWithKey e (const f)

asyncTraverseWithKey :: (Show k,Show a,M.IsKey Table k,Eq a)
                     => Event z 
                     -> (k -> a -> IO b)
                     -> Behavior (Table k a)
                     -> MomentIO (Behavior (Table k b))
asyncTraverseWithKey e f m = fst <$> asyncTraverseWithKeyPend e f m

asyncTraverseWithKeyPend :: (Show k,Show a,M.IsKey Table k,Eq a)
                     => Event z 
                     -> (k -> a -> IO b)
                     -> Behavior (Table k a)
                     -> MomentIO (Behavior (Table k b),Behavior (Table k ()))
asyncTraverseWithKeyPend e f m = (_1 %~ fmap raise) <$> asyncTraverseWithKeyPend' e f m
    where
        raise = M.map $ either throw id

asyncTraverse' :: (Show k,Show a,M.IsKey Table k,Eq a)
               => Event z 
               -> (a -> IO b)
               -> Behavior (Table k a)
               -> MomentIO (Behavior (Table k (Either SomeException b)))
asyncTraverse' e f = asyncTraverseWithKey' e (const f)

asyncTraverseWithKey' :: (Show k,Show a,M.IsKey Table k,Eq a)
                      => Event z 
                      -> (k -> a -> IO b)
                      -> Behavior (Table k a)
                      -> MomentIO (Behavior (Table k (Either SomeException b)))
asyncTraverseWithKey' e f m = fst <$> asyncTraverseWithKeyPend' e f m

asyncTraverseWithKeyPend' :: (Show k,Show a,M.IsKey Table k,Eq a)
                      => Event z 
                      -> (k -> a -> IO b)
                      -> Behavior (Table k a)
                      -> MomentIO (Behavior (Table k (Either SomeException b)), Behavior (Table k ()))
asyncTraverseWithKeyPend' e f m = do
    q <- queue e f m
    let r = M.map snd . view completedJobs <$> q
        p = (() <$) . view pendingJobs <$> q
    return (r,p)

queue :: (Show k,Show a,M.IsKey Table k,Eq a)
      => Event z 
      -> (k -> a -> IO b)
      -> Behavior (Table k a)
      -> MomentIO (Behavior (JobQueue k a b))
queue e f m = do
    init <- valueB $ newQueue f <$> m
    ch   <- changes m
    let combine f g x = MaybeT $ do
            y <- runMaybeT $ f x
            z <- runMaybeT $ g $ fromMaybe x y
            return $ z <|> y <|> Just x
        combine' op f g = op <$> f <*> g
        pollAll = return <$> (collectResults <$ e)
        updateAll = updateQueue f <$> ch
    r <- fromIO' init $ unionWith (combine' combine) updateAll pollAll
    return $ (pendingJobs'.traverse._2 .~ Proxy) <$> r

adjust :: Eq a => Behavior a -> MomentIO (Behavior a)
adjust b = do
        init <- valueB b
        ch   <- changes b
        let f x m = do
                y <- m
                if x == y 
                    then return $ pure Nothing
                    else return $ pure $ Just y
        e    <- eventIO' $ f <$> b <@> ch
        stepper init $ filterJust e

eventIO :: Event (IO a) -> MomentIO (Event a)
eventIO e = do
    (e',f) <- newEvent
    reactimate $ (f =<<) <$> e
    return e'

eventIO' :: Event (Future (IO a)) -> MomentIO (Event a)
eventIO' e = do
    (e',f) <- newEvent
    reactimate' $ fmap (f =<<) <$> e
    return e'

behaviorIO :: Behavior (IO a) -> MomentIO (Behavior a)
behaviorIO b = do
    init <- valueB =<< fromPoll =<< valueB b 
    step <- eventIO' =<< changes b    
    stepper init step

fromIO :: IO a
    -> Event (a -> IO a)
    -> MomentIO (Behavior a)
fromIO init step = fromIO' init $ return . fmap lift <$> step

fromIO' :: forall a. IO a
    -> (Event (Future (a -> MaybeT IO a)))
    -> MomentIO (Behavior a)
fromIO' init step = mdo
    i <- valueB =<< fromPoll init
    let f x y = (>>=) <$> x <*> y
        step' = fmap (fmap runMaybeT) <$> step
        b'    = pure . pure <$> b
    e <- eventIO' $ f <$> b' <@> step'
    b <- stepper i $ filterJust e
    return b
