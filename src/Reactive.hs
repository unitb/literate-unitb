{-# LANGUAGE RecursiveDo #-}
module Reactive where

    -- Modules
import Document.Document ()

import Logic.Expr

import UnitB.UnitB (machines,MachineId,System,proof_obligation)

import Z3.Z3

    -- Libraries
import Control.Concurrent ()
import Control.Concurrent.Async
import Control.Concurrent.STM
import Control.Exception
import Control.Invariant
import Control.Lens
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State ()
import Control.Monad.Trans.Lens

import Data.Either.Combinators
import Data.List.NonEmpty ()
import Data.Map.Class  as M hiding (split)
import Data.Maybe
import Data.PartialOrd
import Data.String
import Data.Time ()

import Reactive.Banana as B
import Reactive.Banana.Async
import Reactive.Banana.Discrete
import Reactive.Banana.Frameworks
import Reactive.Banana.IO
import Reactive.Banana.Keyboard

import System.Directory
import System.Console.ANSI
import System.IO.FileFormat

import Text.Printf.TH

import Utilities.Syntactic
import Utilities.Table

import Interactive.Pipeline (Params)
import Interactive.Serialize (seqFileFormat,Seq)

type Key = (MachineId,Label)

type POs = Table Key Seq
-- type ResultSet = Table Key PO
type Results = Table Key (Maybe Bool)
type PO  = (Seq,Maybe Bool)
type Prover = (Seq,Async Bool)
type ProverSet = Table Key Prover
type M = Mt MomentIO

-- type MExc = Either (NonEmpty SomeException)

newtype Mt m a = M { _mt :: ReaderT Params (KeyboardT (AsyncMomentT m)) a }
    deriving ( Functor, Applicative
             , MonadIO, MonadReader Params
             -- , MonadAsyncMoment
             , MonadMomentIO
             , MonadMoment, MonadFix )

newtype ManyExceptions = ManyExceptions (NonEmpty SomeException)
    deriving (Show)

instance Monad m => Monad (Mt m) where
    {-# INLINE (>>=) #-}
    M m >>= f = M $ m >>= _mt . f

-- instance MonadAsyncMoment m => MonadAsyncMoment (KeyboardT m) where
--     asyncEvent    = fmap lift . asyncEvent 
--     asyncBehavior = fmap lift . asyncBehavior
--     eventSource   = lift . eventSource

makeLenses ''Mt

instance Exception ManyExceptions where


-- period :: MonadMomentIO m
--        => NominalDiffTime 
--        -> Mt m (Event UTCTime)
-- period dt = do
--     t <- liftMomentIO $ fromPoll getCurrentTime
--     first <- valueB t
--     timer <- makeTimer $ fst $ properFraction $ 0.5 * 1000000.0 * dt
--     -- ch    <- changes t
--     let nextF t y
--             | t >= y    = dt `addUTCTime` y
--             | otherwise = y
--     next  <- accumB (dt `addUTCTime` first) 
--             $ nextF <$> t <@ timer
--     return $ t <@ whenE ((<=) <$> next <*> t) timer

-- fileChanges :: MonadMomentIO m
--             => FilePath -> Mt m (Event ())
-- fileChanges fn = do
--     let dt = 0.5
--     p   <- period dt
--     ts  <- liftMomentIO $ fromPoll $ getModificationTime fn
--     ts0 <- valueB ts
--     let hasChanged ts (ts',_) = (ts,ts /= ts')
--     ch  <- accumE (ts0,False) $ hasChanged <$> ts <@ p
--     return $ () <$ filterApply (pure snd) ch

-- parser :: MonadMomentIO m
--        => FilePath 
--        -> Mt m (Discrete POs, Behavior [Error])
-- parser fn = do
--     -- _r <- liftMomentIO $ fromPoll $ 
--     r0   <- liftIO $ parse_system fn
--     ch   <- fileChanges fn
--     rEvt <- liftMomentIO $ mapEventIO parse_system (fn <$ ch)
--     let err0 = fromLeft [] r0
--         s0   = fromRight empty_system r0
--         (err,s) = split rEvt
--         pos = proof_obligation' <$> stepperD s0 s
--     (pos,) <$> stepper err0 err

-- data POState = POState

-- mapEventAsync :: (a -> IO b)
--             -> Event a
--             -> m (Event b)
-- mapEventAsync f e = do
--     e'  <- mapEventIO (async . f) e
--     e'' <- asyncEvent e' $ \input output -> do
--             fix $ \rec st -> do
--                 atomically input 
--                 _
--     _

--asyncJobs :: (a -> IO b) 
--          -> Behavior (Map k a)
--          -> MomentIO (Behavior (Map k b))
--asyncJobs f m = do
--    --job0  <- valueB =<< fmap _ <$> m
--    let start x = (x,) <$> async (f x)
--    m' <- changes m
--    --stepper 
--    m0 <- valueB =<< fromPoll =<< valueB (traverse start <$> m)
--    (ev,h) <- newEvent
--    let g x y   = f' <$> x <*> y
--        f' m m' = differenceWith (\x y -> guard (x /= y) >> return x) m' m
--    reactimate' $ fmap (h =<<) . fmap (traverse start) <$> (g <$> (pure <$> m) <@> m')
--    tasks <- stepper m0 _
--    _

runM :: M (Event a) 
     -> Params
     -> IO a
runM (M m) p = runAsync $ do
        kb <- pollKeyboard
        e  <- withKeyboard_ kb (runReaderT m p)
        return e

instance Monad m => KeyboardMonad (Mt m) where
    command' = M . lift . command'
    specializeKeyboard b = mt.insideReaderT %~ specializeKeyboard b

instance MonadTrans Mt where
    lift = M . lift . lift . lift

makeProverSet :: Map Key PO -> Discrete POs -> M (Behavior ProverSet)
makeProverSet initPos pos = mdo
        let update (s,r) (s',_) 
                | s == s'   = (s,r)
                | otherwise = (s',Nothing)
            pos' = valueD pos & traverse %~ (,Nothing)
            initPos' = M.unionWith update initPos pos'
        liftIO $ putStrLn $ "size = " ++ show (M.size initPos')
        initProvers <- liftIO $ traverseWithKey makeProver initPos'
                
        -- reset <- command "reset"
        -- let update :: Event (NonEmpty (Either POs ()))
        --     update = B.unionWith (<>) (pure.Left <$> pos) (pure.Right <$> reset)
        newProver <- lift $ mapEventIO id $ 
            updateProverSet <$> prover <@> changesD pos
        prover <- stepper initProvers newProver
        return prover

-- prover :: Event ()
--        -> Discrete POs
--        -> M ( Behavior (Table Key (Maybe Bool))
--             , Behavior Int)
-- prover exit pos = do
--     fn <- asks path
--     let stateFile = fn ++ ".state"
--     withFile seqFileFormat' stateFile exit M.empty $ \initPos -> do
--         prover <- makeProverSet initPos pos
--         let _ = prover :: Behavior ProverSet
--         res    <- asyncBehavior prover gatherResults
--         let exc  = fst <$> res
--             res' = snd <$> res
--         results <- stepper initPos res'
--         let pending = M.filter (isNothing.snd) <$> results
--         lift $ reactimate $ throw . ManyExceptions <$> filterJust (nonEmpty <$> exc)
--         return $ ((fmap snd <$> results,M.size <$> pending),results)

splitProver :: Prover -> STM (Either Prover (Either SomeException (Seq,Bool)))
splitProver p@(s,_) = maybe (Left p) (Right . fmap (s,)) <$> pollSTM (snd p)

splitProverSet :: Map lbl Prover 
               -> STM ( Map lbl Prover 
                      , Map lbl SomeException 
                      , Map lbl (Seq,Maybe Bool) )
splitProverSet ps = do
        rs <- traverse splitProver ps
        let (ps,(es,os)) = mapEither id rs & _2 %~ mapEither id
        return (ps,es,(_2 %~ Just) <$> os)

-- gatherResults :: Ord lbl 
--               => Pipe 
--                     (Map lbl Prover) 
--                     ([SomeException], Map lbl (Seq, Maybe Bool))
-- gatherResults input output = 
--         flip evalStateT (M.empty,M.empty) $ do
--             forever $ do
--                 let initResults m = (m & traverse._2 .~ Nothing,m)
--                 (cs,ps) <- get
--                     -- (completed,pending)
--                 -- lift $ print =<< getCurrentTime
--                 lift $ putStrLn $ "completed: " ++ show (M.size ps)
--                 m' <- lift $ atomically $ (initResults <$> input) `orElse` do
--                     (ps',es,rs) <- splitProverSet ps
--                     guard $ not (M.null es && M.null rs)
--                     let cs' = rs `M.union` cs
--                     output (M.elems es,cs')
--                     return (cs',ps')
--                 put m'

-- getResultSet :: ProverSet -> STM (MExc ResultSet,ProverSet)
-- getResultSet prover = do
--         p' <- traverse (\(s,p) -> (s,p,) <$> pollSTM p) prover
--         let (prover',res) = M.mapEither reformat p'
--             reformat (s,p,r) = maybe (Left (s,p)) (Right . (s,)) r
--             res' = traverseValidation 
--                     (mapBoth pure (_2 %~ Just).sequenceA) 
--                     res
--         when (M.null res) $ retry
--         return (res',prover')

-- neList :: e -> NonEmpty e
-- neList = (:|[]) 

-- mapEventSTM :: (a -> STM b) 
--             -> Event a
--             -> MomentIO (Event b)
-- mapEventSTM = _

-- fromPollSTM :: Behavior (STM a)
--             -> M (Event a)
-- fromPollSTM b = do
--     (e,h) <- lift $ newEvent
--     -- initB <- valueB b
--     -- chB <- changes b
--     M $ tell [fmap h <$> b]
--     return e

-- fromFile :: FileFormat a
--          -> FilePath
--          -> Event ()
--          -> a 
--          -> Behavior a
--          -> MomentIO a
-- fromFile format fn exit x b = do
--     r <- liftIO $ do
--         b <- doesFileExist fn
--         if b then
--           rightToMaybe <$> readFormat' format fn
--         else return Nothing
--     reactimate $ writeFormat format fn <$> b <@ exit
--     return $ fromMaybe x r

withFile :: MonadMomentIO m
         => FileFormat a 
         -> FilePath
         -> Event ()
         -> a
         -> (a -> m (b,Behavior a))
         -> m b
withFile format fn exit x f = do
    r <- liftIO $ do
        b <- doesFileExist fn
        if b then
          rightToMaybe <$> readFormat' format fn
        else return Nothing
    (y,b) <- f $ fromMaybe x r
    liftMomentIO $ reactimate $ writeFormat format fn <$> b <@ exit
    return y

poLabel :: Key -> Label
poLabel = uncurry (</>) . (_1 %~ as_label)

makeProver :: Key -> PO -> IO Prover
makeProver k (po,Nothing) = do 
    -- t <- getCurrentTime
    -- putStrLn $ "spark: " ++ show t
    prover <- async $ (Valid ==) <$> discharge (poLabel k) po
    return (po,prover)
makeProver _k (po,Just x) = do 
    -- t <- getCurrentTime
    -- putStrLn $ "fail:  " ++ show t
    prover <- async $ return x
    return (po,prover)

updateProver :: Key -> Seq -> Prover -> IO Prover
updateProver k po' (po,prover) = case cmp of
        Comp EQ -> return (po,prover)
        _ -> do

            newProver <- async $ 
                withAsync (cancel prover) $ \oldProver -> do
                    delay
                    x <- discharge (poLabel k) po'
                    wait oldProver
                    return (x == Valid)
            return (po',newProver)
    where
        cmp = partCompare po po'
        delay = do
            d <- poll prover
            if (d^?_Just._Right) == Just True && isLeq cmp then do
                timer <- registerDelay $ 5 * 60 * 1000000
                atomically $ guard =<< readTVar timer
            else return ()

deleteProver :: Key -> Prover -> IO (Async ())
deleteProver _ (_,p) = async (cancel p)

updateProverSet :: ProverSet -> POs -> IO ProverSet
updateProverSet provers pos = do
    let new = traverseWithKey makeProver $ (,Nothing) <$> pos `M.difference` provers
        old = traverseWithKey deleteProver $ provers `M.difference` pos
        changed = sequenceA $ M.intersectionWithKey updateProver pos provers
    _ <- old
    liftA2 M.union new changed

printReport :: (Results, [Error], Int) -> IO ()
printReport (pos,errs,ws) = do
        let pos' = M.filter (Just False /=) pos
            _lns0 = [printf|  x  %s|] . show . poLabel <$> keys pos'
            lns1 = report <$> errs
            lns2 = [[printf|workers: %d|] ws]
            lns  = lns1 ++ lns2
        cursorUpLine (length lns)
        clearFromCursorToScreenBeginning
        forM_ lns $ \ln -> do
            putStr ln
            clearFromCursorToLineEnd
            putStrLn ""

-- display :: Behavior Results
--         -> Behavior [Error]
--         -> Behavior Int
--         -> M ()
-- display pos errs ws = do
--         p <- period 0.2
--         let r = printReport <$> 
--                 liftA3 (,,) pos errs ws
--         lift $ liftIOLater =<< valueB r
--         ch <- lift $ changes r
--         --let ev = B.unionWith const ch $ pure <$> r <@> p
--         b <- stepper True $ B.unionWith const (True <$ p) (False <$ ch)
--         lift $ reactimate' $ whenE b ch

seqFileFormat' :: FileFormat (Table Key (Seq, Maybe Bool))
seqFileFormat' = prismFormat (keyIso (_1 %~ fromString . pretty) (_1 %~ as_label)) $ seqFileFormat
    where
        keyIso :: (Ord k0,Ord k1)
               => (k0 -> k1)
               -> (k1 -> k0)
               -> Iso' (Table k0 a) (Table k1 a)
        keyIso f g = iso (mapKeys f) (mapKeys g)

proof_obligation' :: System -> Table Key Seq
proof_obligation' = M.unions . fmap (uncurry $ M.mapKeys . (,)) 
                             . M.toList . M.map proof_obligation 
                             . view' machines

-- interactiveSystem :: M (Event ())
-- interactiveSystem = do
--         -- quit <- makeTimer $ 3 * 60 * 1000000
--         -- _tick <- makeTimer $ 100000
--         fn   <- asks path
--         quit <- command "quit"
--         (sys,_errs) <- parser fn
--         liftMomentIO $ reactimate $ putStrLn "done parsing" <$ changesD sys
--         (_res,_ws)   <- prover quit sys
--         -- display res errs ws
--         return quit
--         -- dump
--         -- summary
--         -- serialize

-- gather :: [STM a] -> STM (NonEmpty a)
-- gather xs = do
--     let try x = (Just <$> x) `orElse` return Nothing
--     ys <- catMaybes <$> mapM try xs
--     maybe retry return $ nonEmpty ys

-- main :: Params -> IO ()
-- main args = do
--     setNumCapabilities 8
--     -- let mySystem = do
--     --         t <- period 1.0
--     --         liftMomentIO $ reactimate $ putStrLn . [printf|current time: %s|] . show <$> t
--     --         period 30.0
--     runM interactiveSystem args
    -- return ()
    -- print =<< runM mySystem args
    -- (hTime,fTime) <- newAddHandler
    -- (hKB,fKB) <- newAddHandler
    -- var <- newEmptyTMVarIO
    -- writer <- newTVarIO $ return (return ())
    -- actuate =<< compile (do
    --     eTime <- fromAddHandler hTime
    --     eKB   <- fromAddHandler hKB
    --     let system = do
    --             interactiveSystem (path args) eTime
    --     ((),w) <- runM system args eKB
    --     let v = fmap sequence_ . gather <$> sequenceA w
    --         -- stmB  = (block =<<) . sequenceA <$> sequenceA w
    --         -- block = maybe retry (return.sequence_).nonEmpty
    --     initSTM <- valueB v
    --     liftIOLater $ atomically $ 
    --         writeTVar writer initSTM
    --     chSTM <- changes $ atomically . writeTVar writer <$> v
    --     reactimate' chSTM
    --     )
    -- forkIO $ forever $ do
    --     ln <- getLine
    --     atomically $ putTMVar var $ fKB ln
    -- forkIO $ forever $ do
    --     d <- registerDelay 100000
    --     atomically $ do
    --         guard =<< readTVar d
    --         tryPutTMVar var $ fTime ()
    -- replicateM_ 20 $ do
    --     join $ fmap sequence_ $ atomically $ 
    --         gather 
    --             [ takeTMVar var
    --             , join $ readTVar writer ]
    -- putStrLn "Hello World"
