{-# LANGUAGE BangPatterns #-}
module Utilities.Trace where

import Control.Arrow
import Control.Concurrent
import Control.DeepSeq
import Control.Exception
import Control.Monad.IO.Class

-- import Data.Set
import Data.Foldable as F
import Data.Typeable

import qualified Debug.Trace as DT

import System.IO.Unsafe

import Utilities.Format
import Text.Printf

-- trace_switch :: MVar (Set ThreadId)
-- trace_switch = unsafePerformIO (newMVar empty)

is_tracing_on :: IO Bool
is_tracing_on = return True
        -- sw  <- readMVar trace_switch
        -- tid <- myThreadId
        -- return $ tid `member` sw

turn_tracing_on :: IO ()
turn_tracing_on = return ()
    -- modifyMVar_ trace_switch $ \sw -> do
    --     tid <- myThreadId
    --     return $ insert tid sw

turn_tracing_off :: IO ()
turn_tracing_off = return ()
    -- modifyMVar_ trace_switch $ \sw -> do
    --     tid <- myThreadId
    --     return $ delete tid sw

trace :: String -> a -> a
trace xs x = unsafePerformIO $ do
        tid <- myThreadId
        -- b   <- is_tracing_on
        -- if b then
        return (DT.trace (format "({0}) {1}" tid xs) x)
        -- else
            -- return x

traceM :: Monad m => String -> m ()
traceM xs = trace xs (return ())

traceM' :: Monad m => String -> m a -> m a
traceM' xs cmd = do
    x <- cmd
    traceM xs
    return x

traceA :: ArrowApply arr => (a -> String) -> arr a ()
traceA f = arr (\x -> (trace (f x) returnA, ())) >>> app

traceIO :: MonadIO m => String -> m ()
traceIO xs = do
        tid <- liftIO $ myThreadId
        b <- liftIO $ is_tracing_on
        if b then
            liftIO $ DT.traceIO (format "({0}) {1}" tid xs)
        else
            return ()

traceBlock :: Monad m => String -> m a -> m a
traceBlock xs cmd = do
        traceM $ "begin " ++ xs
        r <- cmd
        traceM $ "end " ++ xs
        return r

traceBlockIO :: MonadIO m => String -> m a -> m a
traceBlockIO xs cmd = do
        traceIO $ "begin " ++ xs
        r <- cmd
        traceIO $ "end " ++ xs
        return r

with_tracing :: a -> a
with_tracing x = unsafePerformIO $ do
        b <- is_tracing_on
        if b 
            then return () 
            else turn_tracing_on
        let !r = x
        if b
            then return ()
            else turn_tracing_off
        return r

with_tracingM :: Monad m => m b -> m b
with_tracingM cmd = do
        b <- return $ unsafePerformIO is_tracing_on
        let !_x = if b 
            then () 
            else unsafePerformIO turn_tracing_on
        !r <- cmd
        let !_x = if b 
            then () 
            else unsafePerformIO turn_tracing_off
        return r

with_tracingIO :: MonadIO m => m a -> m a
with_tracingIO cmd = do
        b <- liftIO $ is_tracing_on
        if b 
            then return () 
            else liftIO $ turn_tracing_on
        r <- cmd
        if b
            then return ()
            else liftIO $ turn_tracing_off
        return r

newtype TracingError = TE String
    deriving (Typeable)

instance Show TracingError where
    show (TE xs) = xs

instance Exception TracingError where

beforeAfterIO' :: NFData a => String -> IO a -> IO a
beforeAfterIO' msg cmd = beforeAfterIO msg (force <$> cmd)

beforeAfterIO :: String -> IO a -> IO a
beforeAfterIO msg cmd = mapException f $ do
        traceM $ "before " ++ msg
        x <- catch (evaluate =<< cmd) (throw . f)
        traceM $ "after " ++ msg
        return x
    where
        f :: SomeException -> TracingError
        f e = TE $ format "Failed during {0}\n\n{1}" msg e

beforeAfter' :: NFData a => String -> a -> a
beforeAfter' msg = beforeAfter msg.force

beforeAfterT :: Foldable f => String -> f a -> f a
beforeAfterT msg t = beforeAfter msg $ F.foldl f (0 :: Int) t `seq` t
    where
        f n x = beforeAfter (printf "| %s, %d" msg n) x `seq` (n+1)

beforeAfter :: String -> a -> a
beforeAfter msg x = mapException f $ DT.trace ("before " ++ msg) x `seq` DT.trace ("after  " ++ msg) x
    where
        f :: SomeException -> TracingError
        f e = TE $ format "Failed during {0}\n\n{1}\nend" msg e
