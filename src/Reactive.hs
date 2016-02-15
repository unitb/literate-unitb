module Reactive where

    -- Modules
import Document.Document

import Logic.Expr

import UnitB.UnitB (empty_system,machines,MachineId,System,proof_obligation)

import Z3.Z3

    -- Libraries
import Control.Concurrent
import Control.Concurrent.STM
import Control.Lens
import Control.Monad

import Data.Either.Combinators
import Data.Time

import Reactive.Banana as B
import Reactive.Banana.Frameworks

import System.Directory
import System.Environment
import System.Console.ANSI

import Utilities.Invariant
import Utilities.Map  as M hiding (split)
import Utilities.PrintfTH
import Utilities.Reactive.Async
import Utilities.Syntactic
import Utilities.Table

period :: NominalDiffTime -> MomentIO (Event UTCTime)
period dt = do
    t <- fromPoll $ getCurrentTime
    first <- valueB t
    ch    <- changes t
    let nextF t y
            | t >= y    = dt `addUTCTime` y
            | otherwise = y
    next  <- accumB (dt `addUTCTime` first) 
            $ nextF <$> t <@ ch
    return $ t <@ whenE ((<=) <$> next <*> t) ch

fileChanges :: FilePath -> MomentIO (Event ())
fileChanges fn = do
    let dt = 0.1
    p   <- period dt
    ts  <- fromPoll $ getModificationTime fn
    ts0 <- valueB ts
    let hasChanged ts (ts',_) = (ts,ts /= ts')
    ch  <- accumE (ts0,False) $ hasChanged <$> ts <@ p
    return $ () <$ filterApply (pure snd) ch

parser :: FilePath -> MomentIO (Behavior System, Behavior [Error])
parser fn = do
    r  <- fromPoll $ parse_system fn
    r0 <- valueB r
    ch <- fileChanges fn
    let (err,s) = split $ r <@ ch
    (,) <$> stepper (fromRight empty_system r0) s
        <*> stepper (fromLeft [] r0) err

data POState = POState

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

type Key = (MachineId,Label)

prover :: Behavior System 
       -> MomentIO ( Behavior (Table Key Validity)
                   , Behavior Int)
prover sys = do
    let pos  = fmap proof_obligation.view' machines <$> sys
    --ch   <- changes m
    tick <- period 0.1
    --let nextPOS x y = fromRight y x
    --pos0 <- valueB m
    --pos  <- accumB 
    --    pos0
    --    (nextPOS <$> m <@ ch)
    let pos' = foldMapWithKey (\k -> mapKeys (k,)) <$> pos
        poLabel = uncurry (</>) . (_1 %~ as_label)
    (res,ws) <- asyncTraverseWithKeyPend tick (discharge . poLabel) pos'
    return (res,M.size <$> ws)

printReport :: (Table Key Validity, [Error], Int) -> IO ()
printReport (pos,errs,ws) = do
        let pos' = M.filter (Valid /=) pos
            lns0 = [printf| x %s|] . show . uncurry (</>) . (_1 %~ as_label) <$> keys pos'
            lns1 = report <$> errs
            lns2 = [[printf|workers: %d|] ws]
            lns  = lns0 ++ lns1 ++ lns2
        cursorUpLine (length lns)
        clearFromCursorToScreenBeginning
        forM_ lns $ \ln -> do
            putStr ln
            clearFromCursorToLineEnd
            putStrLn ""

display :: Behavior (Table Key Validity)
        -> Behavior [Error]
        -> Behavior Int
        -> MomentIO ()
display pos errs ws = do
        p <- period 0.2
        let r = printReport <$> ((,,) <$> pos <*> errs <*> ws)
        liftIOLater =<< valueB r
        ch <- changes r
        --let ev = B.unionWith const ch $ pure <$> r <@> p
        b <- stepper True $ B.unionWith const (True <$ p) (False <$ ch)
        reactimate' $ whenE b ch

interactiveSystem :: FilePath
                  -> Event () -> Event String
                  -> MomentIO ()
interactiveSystem fn _tick _kb = do
        (sys,errs) <- parser fn
        (res,ws)   <- prover sys
        display res errs ws
        -- dump
        -- summary
        -- serialize

main :: IO ()
main = do
    [args] <- getArgs
    (hTime,fTime) <- newAddHandler
    (hKB,fKB) <- newAddHandler
    actuate =<< compile (do
        eTime <- fromAddHandler hTime
        eKB   <- fromAddHandler hKB
        interactiveSystem args eTime eKB
        )
    var <- newEmptyTMVarIO
    forkIO $ forever $ do
        ln <- getLine
        atomically $ putTMVar var $ fKB ln
    forkIO $ forever $ do
        d <- registerDelay 100000
        atomically $ do
            guard =<< readTVar d
            tryPutTMVar var $ fTime ()
    replicateM_ 20 $ do
        join $ atomically $ takeTMVar var
    putStrLn "Hello World"
