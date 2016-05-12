{-# LANGUAGE ScopedTypeVariables,GADTs
        ,KindSignatures,DataKinds
        ,RecursiveDo
        ,ScopedTypeVariables
        ,UndecidableInstances
        ,TypeFamilies
        ,PolyKinds
        ,StandaloneDeriving
        ,TypeOperators #-}
module Reactive.Banana.Async where

import Control.Arrow
import Control.CoApplicative
import Control.Concurrent
import Control.Concurrent.Async
import Control.Concurrent.STM
import Control.Exception hiding (Handler)
import Control.Lens
import Control.Monad.Loops
import Control.Monad.Reader
import Control.Monad.Random as R
import Control.Monad.RWS
import Control.Monad.State
import Control.Monad.Writer
import Control.Precondition

import Data.Default
import Data.Either
import Data.List as L
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as M 
import Data.Proxy.TH
import Data.Semigroup.Monad
import Data.Time
import Data.These
import Data.TypeList

import GHC.Generics.Instances

import Reactive.Banana
import Reactive.Banana.Combinators.Extras
import Reactive.Banana.Discrete
import Reactive.Banana.Frameworks
import           Reactive.Banana.IO as R hiding (interpretFrameworks')
import qualified Reactive.Banana.IO as R
import Reactive.Banana.Property

import Test.QuickCheck

data JobBatch' map a b = JobBatch 
              { _initJobs :: map (a,Either b (IO b))
              , _updateJobs :: Event (map (Maybe (a,IO b)))
              , _killTasks  :: Event ()
              }

makeLenses ''JobBatch'

type Pipe' s a b = a -> Future (StateT s IO b)
type Pipe s a b = a -> StateT s IO b

type Scaffolding = (IO () -> IO ())
    -- put operation for the event queue
    -- 

type KBEvent = ( Maybe (Event String)
               , Map NominalDiffTime (Event ()))

type AsyncMoment = AsyncMomentT MomentIO

newtype AsyncMomentT m a = AsyncMoment { _impl :: forall t. MonadAsyncMomentImpl t m => t a }
    deriving (Functor)

newtype AsyncMomentImplT m a = AsyncMomentImpl { _asyncMoment :: RWST Scaffolding [AsyncEvent] KBEvent m a }
    deriving (Functor,Applicative,MonadIO,MonadTrans
             ,MonadMoment,MonadMomentIO,MonadFix)

data AsyncEvent = 
            forall k a b. Ord k => Pipeline 
                (Jobs' k a b) 
                (Input k a b) 
                (Outbut k a b) 
            | Source (IO ())

-- newtype Apply f (m :: k) a = Apply (f m a)

-- type Jobs  k a b = (Map k (a,b), Map k (a,Async b))
type Jobs' k a b = (Map k (a,Either b (IO b)))

type Input k a b = STM (Map k (Maybe (a,IO b)))
type Outbut k a b = Map k (a,Either SomeException b) -> Map k (a,()) -> IO ()

instance Applicative m => Applicative (AsyncMomentT m) where
    pure x = AsyncMoment $ pure x
    {-# INLINE (<*>) #-}
    AsyncMoment f <*> AsyncMoment x = AsyncMoment $ f <*> x
instance MonadFix m => MonadFix (AsyncMomentT m) where
    mfix f = AsyncMoment $ mfix $ _impl . f
instance MonadIO m => MonadIO (AsyncMomentT m) where
    liftIO = lift . liftIO
instance MonadMoment m => MonadMoment (AsyncMomentT m) where
    liftMoment = lift . liftMoment
instance MonadMomentIO m => MonadMomentIO (AsyncMomentT m) where
instance MonadTrans AsyncMomentT where
    lift m = AsyncMoment $ liftIntern m

instance Monad m => Monad (AsyncMomentT m) where
    {-# INLINE (>>=) #-}
    AsyncMoment m >>= f = AsyncMoment $ m >>= _impl . f

instance Monad m => Monad (AsyncMomentImplT m) where
    {-# INLINE (>>=) #-}
    AsyncMomentImpl m >>= f = AsyncMomentImpl $ m >>= _asyncMoment . f

type JobBatch lbl a b = JobBatch' (Map lbl) a b

instance Monoid1 map => Default (JobBatch' map a b) where
    def = JobBatch mempty1 never never

class MonadMomentIO m => MonadAsyncMoment m where
    -- asyncEvent' :: s
    --             -> Pipe s a b
    --             -> Event (Future a) 
    --             -> m (Event b)
    pollKeyboard :: m (Event String)
    makeTimer :: NominalDiffTime -> m (Event ())
    jobBatch' :: Ord lbl
              => State (JobBatch lbl a b) z
              -> m (Discrete (Map lbl (a,b)),Discrete (Map lbl (a,())))
    default pollKeyboard :: forall m' (t :: (* -> *) -> * -> *). 
                            (t m' ~ m, MonadAsyncMoment m',MonadTrans t) 
                         => t m' (Event String)
    pollKeyboard = lift pollKeyboard
    default makeTimer :: forall m' (t :: (* -> *) -> * -> *). 
                         (t m' ~ m, MonadAsyncMoment m',MonadTrans t) 
                      => NominalDiffTime -> m (Event ())
    makeTimer = lift . makeTimer
    default jobBatch' :: forall m' (t :: (* -> *) -> * -> *) a b lbl z. 
                         (t m' ~ m, MonadAsyncMoment m',MonadTrans t,Ord lbl)
              => State (JobBatch lbl a b) z
              -> m (Discrete (Map lbl (a,b)),Discrete (Map lbl (a,())))
    jobBatch' = lift . jobBatch'

instance MonadMomentIO m => MonadAsyncMoment (AsyncMomentT m) where
    pollKeyboard = AsyncMoment pollKeyboardImpl
    makeTimer t = AsyncMoment $ makeTimerImpl t
    jobBatch' p = AsyncMoment $ jobBatchImpl' p

class (MonadIO t,MonadFix t) => MonadAsyncMomentImpl t (m :: * -> *) | t -> m where
    -- asyncEvent' :: s
    --             -> Pipe s a b
    --             -> Event (Future a) 
    --             -> m (Event b)
    liftIntern :: m a -> t a
    pollKeyboardImpl :: t (Event String)
    makeTimerImpl :: NominalDiffTime -> t (Event ())
    jobBatchImpl' :: (Ord lbl)
                  => State (JobBatch lbl a b) z
                  -> t (Discrete (Map lbl (a,b)),Discrete (Map lbl (a,())))
    -- default pollKeyboardImpl :: forall m' (t :: (* -> *) -> * -> *). 
    --                         (t m' ~ m, MonadAsyncMoment m',MonadTrans t) 
    --                      => t m' (Event String)
    -- pollKeyboardImpl = lift pollKeyboard
    -- default makeTimerImpl :: forall m' (t :: (* -> *) -> * -> *). 
    --                      (t m' ~ m, MonadAsyncMoment m',MonadTrans t) 
    --                   => NominalDiffTime -> m (Event ())
    -- makeTimerImpl = lift . makeTimer
    -- default jobBatch' :: forall m' (t :: (* -> *) -> * -> *) a b lbl z. 
    --                      (t m' ~ m, MonadAsyncMoment m',MonadTrans t,Ord lbl)
    --           => State (JobBatch lbl a b) z
    --           -> m (Discrete (Map lbl (a,b)),Discrete (Map lbl (a,())))
    -- jobBatch' = lift . jobBatch'

_MaybeToMap :: Iso (Maybe a) (Maybe b) (Map () a) (Map () b)
_MaybeToMap = iso (maybe M.empty (M.singleton ())) (M.lookup ())

maybeToEither :: Maybe a -> Either () a
maybeToEither = maybe (Left ()) Right

mapOnUnion :: Ord k 
           => (These a b -> c)
           -> Map k a
           -> Map k b
           -> Map k c
mapOnUnion f = mapOnUnionWithKey (const f)

mapOnUnionWithKey :: Ord k 
                  => (k -> These a b -> c)
                  -> Map k a
                  -> Map k b
                  -> Map k c
mapOnUnionWithKey f m0 m1 = M.unions [left,middle,right]
    where
        left   = M.mapWithKey (\k -> f k.This) (m0 `M.difference` m1)
        right  = M.mapWithKey (\k -> f k.That) (m1 `M.difference` m0)
        middle = M.intersectionWithKey (\k x y -> f k $ These x y) m0 m1

onRight :: These a b -> Either a (Maybe a,b)
onRight (These x y) = Right (Just x,y)
onRight (That y)    = Right (Nothing,y)
onRight (This x)    = Left x

onBatchAux :: (forall a. ms a -> mt a)
           -> (JobBatch' ms a b) 
           -> (JobBatch' mt a b)
onBatchAux f (JobBatch b c e) = JobBatch
        (f b)
        (f <$> c) 
        e

onBatch :: (forall a. Iso' (ms a) (mt a))
        -> Iso' (JobBatch' ms a b) (JobBatch' mt a b)
onBatch ln = iso (onBatchAux $ view ln) (onBatchAux $ view $ from ln)

jobBatch :: MonadAsyncMoment m
         => State (JobBatch' Maybe a b) z
         -> m (Discrete (Maybe (a,b)),Discrete (Maybe (a,())))
jobBatch param = (fmap (M.lookup ()) *** fmap (M.lookup ())) 
            <$> jobBatch' (zoom (onBatch $ from _MaybeToMap) param)                    

-- asyncEvent :: MonadAsyncMoment m
--            => s
--            -> Pipe s a b
--            -> Event a
--            -> m (Event b)
-- asyncEvent s cmd e = asyncEvent' s cmd (pure <$> e)

-- asyncBehavior :: MonadAsyncMoment m
--               => s
--               -> Pipe s a b
--               -> Behavior a 
--               -> m (Behavior b)
-- asyncBehavior s cmd b = do
--     v  <- liftMoment $ valueB b
--     (v',s') <- liftIO $ runStateT (cmd v) s
--     e  <- asyncEvent' s' cmd =<< liftMomentIO (changes b)
--     stepper v' e

{-# INLINE eventSource #-}
eventSource :: MonadMomentIO m
            => Lens' KBEvent (Maybe (Event a))
            -> ((a -> IO ()) -> IO ())
            -> AsyncMomentImplT m (Event a)
eventSource ln loop = AsyncMomentImpl $ zoom ln $ do
        x <- get
        case x of 
            Just e -> return e
            Nothing -> do
                send   <- ask
                (e,h)  <- liftMomentIO newEvent
                -- let thread = forever $ loop $ atomically . writeTBQueue q . h
                tell [Source $ loop $ send . h]
                put $ Just e
                return e

thread :: AsyncEvent -> IO ()
thread (Source loop) = forever loop
thread (Pipeline first input output) = do
    first <- (traverse._2._Right) async first
    let (firstRes,first') = M.mapEither ((_Left._2 %~ Right).view distr) first
    flip evalStateT (firstRes,first') $ forever $ do
        (ended,pend) <- get
        (ended',old,delete,new) <- lift $ atomically $ do
            changes' <- unfail input
            xs <- pend & (traverse._2) (unfail' waitCatchSTM)
            let (ys,zs) = M.mapEither (view distr) xs
                changes = changes' & traverse %~ M.mapEither (maybe (Left ()) Right)
                new    = maybe M.empty snd changes
                delete = maybe M.empty fst changes `M.union` (() <$ new `M.intersection` pend)
                -- new :: Map lbl (a, IO b)                
                ended' = (ended `M.difference` delete) `M.union` zs
            guard $ not (M.null zs) || isJust changes
            return (ended',ys,delete,new)
        lift $ mapM_ (cancel.snd) (old `M.intersection` delete)
        new' <- lift $ new & (traverse._2) async
        let pending' = (old `M.difference` delete) `M.union` new'
        lift $ output ended' $ pending' & traverse._2 .~ () 
        put (ended',pending')

newtype MockAsyncMomentT m a = MockAsyncMoment { _unMockAsyncMoment :: RWST (Event String) () (Event StdGen) m a } 
    deriving (Functor,Applicative,MonadIO
             ,MonadMoment,MonadMomentIO,MonadFix)

instance MonadTrans MockAsyncMomentT where
    lift = MockAsyncMoment . lift
instance Monad m => Monad (MockAsyncMomentT m) where
    {-# INLINE (>>=) #-}
    MockAsyncMoment m >>= f = MockAsyncMoment $ m >>= _unMockAsyncMoment . f

mapEventIO' :: (a -> IO b) -> Event a -> MomentIO (Event b)
mapEventIO' f e1 = do
     (e2, handler) <- newEvent
     reactimate' $ (\a -> pure $ f a >>= handler) <$> e1
     return e2

accumEventIO :: (MonadMomentIO m,MonadFix m)
             => a
             -> Event (a -> IO a)
             -> m (Event a)
accumEventIO x e = mdo
    b  <- stepper x e'
    e' <- liftMomentIO $ mapEventIO' id (flip ($) <$> b <@> e)
    return e'

instance (MonadMomentIO m,MonadFix m) => MonadAsyncMomentImpl (MockAsyncMomentT m) m where
    liftIntern = lift
    pollKeyboardImpl = MockAsyncMoment $ ask
    makeTimerImpl _  = return never
    jobBatchImpl' param = MockAsyncMoment $ do
        let (JobBatch first update terminate) = execState param def
            completeTasks :: StdGen
                          -> (Map lbl (a, Either b (IO b))
                              -> IO (Map lbl (a, Either b (IO b))))
            completeTasks g = (\m -> evalRandT (traverse (_2 completeOne) m) g)
            completeOne (Right m) = do 
                b <- getRandom 
                if b 
                    then Left <$> lift m 
                    else return $ Right m
            completeOne m@(Left _) = return m
            replace :: These (Maybe (a, IO b)) 
                             (a, Either b (IO b))
                    -> Maybe (a, Either b (IO b))
            replace (This x) = x & mapped._2 %~ Right
            replace (That y) = Just y
            replace (These x _) = x & mapped._2 %~ Right
        -- tick  <- get
        tick <- state $ (fmap fst &&& fmap snd) . fmap R.split
        let complete = completeTasks <$> tick
        let update' = fmap (return.M.mapMaybe id) . mapOnUnion replace <$> update
            terminate' = (return . M.mapMaybe id . (traverse %~ _2 (fmap Left . leftToMaybe))) <$ terminate
        upd   <- accumEventIO first $ unionsM
                [ complete 
                , update'
                , terminate'
                ]
        -- upd'  <- liftMomentIO $ mapEventIO _ upd
        let state = stepperD first upd
        -- cmp  <- lift $ newIORef $ M.mapMaybe (_2 $ fmap Right . leftToMaybe) first
        -- pend <- lift $ newIORef $ M.mapMaybe (_2 rightToMaybe) first
        -- r <- lift.newIORef =<< getSplit
        -- let updEvt = do
        --         putStrLn "\nbefore"
        --         k <- atomically $ unfail input
        --         putStrLn "after"
        --         let del = maybe M.empty (M.mapMaybe $ leftToMaybe.maybeToEither) k
        --             new = maybe M.empty (M.mapMaybe id) k
        --         modifyIORef cmp  (`M.difference` del)
        --         modifyIORef pend (`M.difference` del)
        --         modifyIORef pend (new `M.union`)
        --     compl  = do  
        --         p <- lift $ readIORef pend
        --         (rem,c') <- randomSplit p
        --         lift $ do
        --             c <- readIORef cmp
        --             done <- c' & (traverse._2) (fmap Right)
        --             output (M.union c done) (rem & mapped._2 .~ ())
        --             writeIORef cmp (M.union c done)
        --             writeIORef pend rem
        -- return (Mon updEvt,Mon $ runRandOn r compl)
        return ( M.mapMaybe (_2 $ leftToMaybe) <$> state
               , M.mapMaybe (_2 $ rightToMaybe.(_Right .~ ())) <$> state)


instance (MonadMomentIO m,MonadFix m) => MonadAsyncMomentImpl (AsyncMomentImplT m) m where
    liftIntern = AsyncMomentImpl . lift
    pollKeyboardImpl = eventSource _1 $ \h -> h =<< getLine
    makeTimerImpl dt = eventSource (_2.at dt) $ \h -> do
            b <- registerDelay $ floor (dt * 1000000)
            h ()
            atomically $ guard =<< readTVar b
    jobBatchImpl' param = AsyncMomentImpl $ do
        send <- ask
        let (JobBatch first update terminate) = execState param def
        input  <- liftIO newEmptyTMVarIO
        (e,h)  <- liftMomentIO newEvent
        let newPend  = filterE (not.M.null) $ snd <$> e
            newCompl = filterE (not.M.null) $ fst <$> e
            pending  = stepperD (M.mapMaybe (_2 $ (_Just .~ ()).rightToMaybe) first) newPend
            compl    = stepperD (M.mapMaybe (_2 leftToMaybe) first) newCompl
            handler ended pending = do
                send $ do
                    xs' <- mapM (_2 $ either throw pure) ended
                    h (xs',pending)
        terminate' <- sampleD (pending & mapped.traverse .~ Nothing) terminate
        tell [ Pipeline 
                    first 
                    (takeTMVar input)
                    handler ]
        liftMomentIO $ do
            reactimate 
                $ (atomically . putTMVar input) <$> unionWith M.union update terminate'
        return (compl,pending & mapped.mapped._2 .~ ())

instance MonadAsyncMoment m => MonadAsyncMoment (ReaderT r m) where
instance MonadAsyncMoment m => MonadAsyncMoment (StateT s m) where
instance (MonadAsyncMoment m,Monoid w) => MonadAsyncMoment (RWST r w s m) where
instance (MonadAsyncMoment m,Monoid w) => MonadAsyncMoment (WriterT w m) where

atomically' :: StateT s STM b -> StateT s IO b
atomically' cmd = do
    s <- get
    (x,s') <- lift $ atomically $ do
        runStateT cmd s
    put s'
    return x

compile' :: MomentIO a -> IO (a,EventNetwork)
compile' m = do
    r <- newIORef undefined'
    n <- compile $ do
        x <- m
        liftIO $ writeIORef r x
    (,n) <$> readIORef r

{-# INLINE runAsync #-}
runAsync :: AsyncMoment (Event a)
         -> IO a
runAsync m = runAsyncT m id

unfail :: STM a -> STM (Maybe a)
unfail m = (Just <$> m) `orElse` (return Nothing)

unfail' :: (a -> STM b) -> a -> STM (Either a b)
unfail' f x = (Right <$> f x) `orElse` (return $ Left x)

pollAllSTM :: [Async a] -> STM ([a],[Async a])
pollAllSTM xs = do
    ys <- forM xs $ \a -> 
        (Left <$> waitSTM a) `orElse` (return $ Right a)
    return $ partitionEithers ys

-- mockChan :: ChanM
-- mockChan = Chan $ do
--     cmp  <- newIORef _ -- $ M.mapMaybe (_2 $ fmap Right . leftToMaybe) first
--     pend <- newIORef _ -- $ M.mapMaybe (_2 rightToMaybe) first
--     let handle k = do
--                 let del = M.mapMaybe (leftToMaybe.maybeToEither) k
--                     new = M.mapMaybe id k
--                 modifyIORef cmp  (`M.difference` del)
--                 modifyIORef pend (`M.difference` del)
--                 modifyIORef pend (new `M.union`)
--     return (undefined',_)

-- tvarChan :: ChanM
-- tvarChan = Chan $ do
--     cmp  <- newIORef _ -- $ M.mapMaybe (_2 $ fmap Right . leftToMaybe) first
--     pend <- newIORef _ -- $ M.mapMaybe (_2 rightToMaybe) first
--     v <- newEmptyTMVarIO
--     return (takeTMVar v, atomically . putTMVar v)

{-# INLINE runAsyncT #-}
runAsyncT :: (MonadMomentIO m,MonadFix m)
          => AsyncMomentT m (Event a)
          -> (forall a. m a -> MomentIO a)
          -> IO a
runAsyncT (AsyncMoment (AsyncMomentImpl cmd)) run = do
    q <- newTBQueueIO 20
    exit <- newEmptyTMVarIO
    (w,n) <- compile' $ do
        (e,_,w) <- run $ runRWST cmd 
                (atomically . writeTBQueue q) 
                (Nothing, M.empty)
        reactimate $ atomically . putTMVar exit <$> e
        return w
    putStrLn "inside runAsyncT"
    actuate n
    ts <- mapM (forkIO.thread) w
    x  <- fix $ \proc -> do
        (r,ys) <- atomically $ do
            r  <- unfail $ readTMVar exit
            xs <- untilM (readTBQueue q) (isEmptyTBQueue q)
            -- (ys',xs') <- pollAllSTM ys
            guard (isJust r || not (null xs))
            return (r,xs)
        let _ = ys :: [IO ()]
            -- _ = hs :: [IO ()]
        -- put ys
        sequence_ ys
        maybe proc return r
    mapM_ killThread ts
    return x

-- curriedEvent :: Iso (Event a -> Event b -> r) 
--                     (Event a' -> Event b' -> r')
--                     (Event (Maybe a, Maybe b) -> r)
--                     (Event (Maybe a', Maybe b') -> r')
-- curriedEvent = iso 
--         (\f e -> f (filterJust $ fst <$> e) (filterJust $ snd <$> e)) 
--         (\f e0 e1 -> f $ unionWith combine ((,Nothing).Just <$> e0) ((Nothing,).Just <$> e1)) 
--     where
--         combine (x0,x1) (y0,y1) = (x0<|>y0,x1<|>y1)

-- uncurriedEvent :: Iso (Event (Maybe a, Maybe b) -> r)
--                       (Event (Maybe a', Maybe b') -> r')
--                       (Event a -> Event b -> r) 
--                       (Event a' -> Event b' -> r')
-- uncurriedEvent = from curriedEvent

-- splittingEvents :: Iso' (Event (List' Maybe as)) (List' Event as)
-- splittingEvents = iso splitEvents splitEvents'

randomSplit :: MonadRandom m 
            => Map k a 
            -> m (Map k a,Map k a)
randomSplit m = do
    let cmd x = do
            b <- getRandom
            return $ if b then Left x else Right x
    M.mapEither id <$> (m & traverse cmd)

runRandOn :: IORef StdGen 
          -> RandT StdGen IO a
          -> IO a
runRandOn r cmd = do
        g <- readIORef r
        (x,g') <- runRandT cmd g
        writeIORef r g'
        return x

interpretJobs :: StdGen 
              -> [AsyncEvent]
              -> IO (IO (),IO ())
interpretJobs gen xs = (mapped.each %~ getMon) $ evalRandT (getMon $ foldMap interpretOne xs) gen
    where
        interpretOne :: AsyncEvent
                     -> Mon (RandT StdGen IO) (Mon IO (), Mon IO ())
        interpretOne (Pipeline first input output) = Mon $ do
            -- first' <- lift $ first & (traverse._2) (either return id)
            cmp  <- lift $ newIORef $ M.mapMaybe (_2 $ fmap Right . leftToMaybe) first
            pend <- lift $ newIORef $ M.mapMaybe (_2 rightToMaybe) first
            r <- lift.newIORef =<< getSplit
            let updEvt = do
                    k <- atomically $ unfail input
                    let del = maybe M.empty (M.mapMaybe $ leftToMaybe.maybeToEither) k
                        new = maybe M.empty (M.mapMaybe id) k
                    modifyIORef cmp  (`M.difference` del)
                    modifyIORef pend (`M.difference` del)
                    modifyIORef pend (new `M.union`)
                compl  = do  
                    p <- lift $ readIORef pend
                    (rem,c') <- randomSplit p
                    lift $ do
                        c <- readIORef cmp
                        done <- c' & (traverse._2) (fmap Right)
                        output (M.union c done) (rem & mapped._2 .~ ())
                        writeIORef cmp (M.union c done)
                        writeIORef pend rem
            return (Mon updEvt,Mon $ runRandOn r compl)
        interpretOne (Source _) = return mempty

interpretFrameworks' :: forall t t' b f.
                        ( Curried t (MomentIO (Event b)) f
                        , SameLength t t'
                        , t' ~ ReplaceF Maybe t
                        , AsTypeList t Event
                        , AsTypeList t' Maybe)
                     => f -> [t'] -> IO ([t'],[Maybe b])
interpretFrameworks' f xs = do
    -- input  <- newIORef []
    -- output <- newIORef []
    let f' :: Event t' -> MomentIO (Event b)
        f' = f^.uncurriedEvent'
            -- e' <- f^.uncurriedEvent' $ e
            -- reactimate $ (\(x,y) -> modifyIORef input (listToMaybe x :) >> modifyIORef output (listToMaybe y :))
            --     <$> unionWith mappend ((\x -> ([x],[])) <$> e) ((\x -> ([],[x])) <$> e')
            -- return e'
    R.interpretFrameworks' f' (Just <$> xs)
        & mapped._1.traverse %~ fromMaybe (replicateL' Nothing)
    -- liftA2 (,) (reverse.map (fromMaybe $ replicateL' Nothing) <$> readIORef input)
    --            (reverse <$> readIORef output)    

instance (Frameworks m,MonadFix m) => Frameworks (AsyncMomentT m) where
    type EventList (AsyncMomentT m) a = EventList m (Maybe a,Maybe String,Maybe StdGen)
    type InitF (AsyncMomentT m) = InitF m
    interpret' = interpretAsyncT

interpretAsync :: forall a b. 
                  (Event a -> AsyncMoment (Event b))
               -> [Maybe (Maybe a,Maybe String,Maybe StdGen)] 
               -> IO ([Maybe (Maybe a, Maybe String, Maybe StdGen)],[Maybe b])
interpretAsync f = interpretAsyncT f ()

interpretAsyncT :: forall a b m. (Frameworks m,MonadFix m)
                => (Event a -> AsyncMomentT m (Event b))
                -> InitF m
                -> [EventList m (Maybe a,Maybe String,Maybe StdGen)] 
                -> IO ([EventList m (Maybe a, Maybe String, Maybe StdGen)],[Maybe b])
interpretAsyncT f init xs = do
    -- input  <- newIORef []
    -- output <- newIORef []
    let 
        -- g (Nothing,Nothing) = Nothing
        -- g x = Just x
        run' = run^.uncurriedEvent' :: Event (Maybe a,Maybe String,Maybe StdGen) -> m (Event b)
        -- run :: Event _ -> Event String -> MomentIO (Event _)
        run :: Event a -> Event String -> Event StdGen -> m (Event b)
        run e kb tick = do
            (e',_,_) <- runRWST (_unMockAsyncMoment $ _impl $ f e) kb tick
            return e'
    -- interpretFrameworks (_ . ($ q) . runRWST . _asyncMoment . f . _) (g <$> xs)
    interpret' run' init xs
        -- & mapped._1.mapped %~ fromMaybe (Nothing,Nothing,Nothing)
        -- :: IO [Maybe b]
    -- liftA2 (,) (reverse <$> readIORef input) 
    --            (reverse <$> readIORef output)

-- mapping' :: Getting r s a 
--          -> Getting _ (f s) (f a)
-- mapping' ln f x = _ $ ln _ _

instance Arbitrary StdGen where
    arbitrary = mkStdGen <$> arbitrary

t0 :: [Int]
t0 = [0]

t2 :: [Maybe (Maybe (Maybe Int,Maybe ()), Maybe String, Maybe StdGen)]
t2 = [Just (Just (Just 0,Nothing),Nothing,Nothing)]

-- test :: IO ()
-- test = quickCheck $ prop_check_interpret

-- test' :: IO ([Maybe (Maybe (Maybe Int, Maybe ()), Maybe String, Maybe StdGen)],
--              [Maybe String])
-- test' = prop_check_interpret t0 t2

-- testResult :: IO ()
-- testResult = do
--     (xs,ys) <- test'
--     let showLine x = ShowString $ maybe "Nothing" format x ++ "\n"
--         format   = asLines %~ (neTail.traverse %~ ("  " ++)).(_head %~ (' ':))
--     print (map ShowLine t2)
--     print (map ShowLine xs)
--     print (map showLine ys)

newtype ShowLine a = ShowLine a

instance Show a => Show (ShowLine a) where
    show (ShowLine x) = " " ++ show x ++ "\n"

prop_check_interpret :: [Int] -> ()
                     -> [EventList AsyncMoment (Maybe Int,Maybe ())] 
                     -> Property
                     -- -> [Maybe (Maybe (Maybe Int,Maybe ()), Maybe String, Maybe StdGen)] 
                     -- -> IO ([Maybe (Maybe (Maybe Int,Maybe ()), Maybe String, Maybe StdGen)],[Maybe String])
prop_check_interpret xs = satisfies $ do 
    selectM [pr|AsyncMoment|]
    program $ \e -> do
        let (e0,_e1) = e^.splittingEvent'
            e0  :: Event Int
            _e1 :: Event ()
        n <- accumB (sort xs) $ drop 1 <$ e0
        (res,p) <- jobBatch' $ do
                updateJobs .= (M.fromList . map (id &&& Just .((),).return).take 1 <$> n <@ e0)
        res' <- changePairD res
        m <- stepper 0 $ unionWith const (1 <$ e0) (2 <$ res')
        let _ = m :: Behavior Int
        -- liftMomentIO $ do
            -- reactimate $ putStrLn.[printf|a: %s|].show <$> res'
            -- reactimate $ putStrLn.[printf|b: %s|].show <$> p'
            -- reactimate $ putStrLn "tick" <$ e0
            -- reactimate $ putStrLn "a" <$ res'
            -- reactimate $ putStrLn "b" <$ p'
            -- reactimate $ print.M.keys <$> changesD p
        do
            res' <- behavior res
            p'   <- behavior p
            specify (liftA2 (,) res' p') $ do
                invariant' (\(m0,m1) -> M.null $ M.intersection m0 m1)
                togetherOnly (changesD res) (changesD p)
            -- specify (pure ())
            --     (watchSpec (liftA2 (,) b 
            --             (liftA2 M.union (res' & mapped.traverse._2 .~ ()) p')) $ do
            --     -- magnify (to $ fmap $ \(x,y) -> M.union (x & mapped._2 .~ ()) y) $ 
            --         constantUnlessB (M.keys.snd) fst)
        return (never :: Event ())
    specification $ \_ _ -> True
            -- [ disp_ "e0" e0 
            -- -- , disp_ "e1" e1
            -- , dispB "during change" b
            -- , dispB "assert A" a0
            -- , dispStr  "assert B" $ invariantMessage <$> a1
            -- , disp  "delta res" (changesD res)
            -- , disp  "delta p  " (changesD p)
            -- -- , dispB "n" n
            -- -- , dispB "m" m
            -- -- , disp  "p'  " $ p' & mapped.each %~ M.keys 
            -- -- , disp  "res'" $ res' & mapped.each %~ M.keys
            -- ]
            -- [ ["e"]   <$ e0 
            -- , pure.[printf|b@e: %s|].show <$> b <@ e0
            -- , pure.[printf|b@res: %s|].show <$> b <@ res'
            -- , ["res"] <$ changesD res
            -- , ["p"]   <$ changesD p 
            -- , pure.[printf|n: %s|].show <$> unionWith const (n <@ e0) (n <@ res')
            -- , pure.[printf|res: %s|].show.(each %~ M.keys) <$> res'
            -- , pure.[printf|m@res: %s|].show <$> m <@ res'
            -- , pure.[printf|m@e0: %s|].show  <$> m <@ e0
            -- , pure.[printf|m@e1: %s|].show  <$> m <@ e1
            -- , pure.[printf|p: %s|].show.(each %~ M.keys) <$> p' 
            -- ]

-- test2 = satisfy ()

return []

run_tests :: IO Bool
run_tests = $quickCheckAll
