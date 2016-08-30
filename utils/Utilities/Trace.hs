{-# LANGUAGE BangPatterns, TypeFamilies, TypeOperators #-}
module Utilities.Trace where

import Control.Arrow hiding (left,right)
import Control.Category
import Control.Concurrent
import Control.DeepSeq
import Control.Exception
import Control.Lens
import Control.Monad.IO.Class

import Data.Foldable as F
import Data.Typeable

import qualified Debug.Trace as DT

import GHC.Generics.Utils

import Prelude hiding ((.),id)

import System.IO.Unsafe

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
        return (DT.trace (printf "(%s) %s" (show tid) xs) x)
        -- else
            -- return x

traceM :: Monad m => String -> m ()
traceM xs = trace xs (return ())

traceM' :: Monad m => String -> m a -> m a
traceM' xs cmd = do
    x <- cmd
    traceM xs
    return x

traceA' :: Arrow arr 
        => (b -> String)
        -> arr a b 
        -> arr a a
traceA' f a = id &&& a >>> arr (\(x,y) -> trace (f y) () `seq` x)

traceA :: ArrowApply arr => (a -> String) -> arr a ()
traceA f = arr (\x -> (trace (f x) returnA, ())) >>> app

traceIO :: MonadIO m => String -> m ()
traceIO xs = do
        tid <- liftIO $ myThreadId
        b <- liftIO $ is_tracing_on
        if b then
            liftIO $ DT.traceIO (printf "(%s) %s" (show tid) xs)
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
        f e = TE $ printf "Failed during %s\n\n%s" msg (show e)

beforeAfter' :: NFData a => String -> a -> a
beforeAfter' msg = beforeAfter msg.force

beforeAfterT :: Foldable f => String -> f a -> f a
beforeAfterT msg t = beforeAfter msg $ F.foldl' f (0 :: Int) t `seq` t
    where
        f n x = beforeAfter (printf "| %s, %d" msg n) x `seq` (n+1)

beforeAfter :: String -> a -> a
beforeAfter msg x = insertMsg msg $ DT.trace ("before " ++ msg) x `seq` DT.trace ("after  " ++ msg) x

insertMsg :: String -> a -> a
insertMsg msg = mapException $ \e -> TE $ printf "Failed during %s\n\n%s\nend" msg (show (e :: SomeException))

class BeforeAfter' a where
    beforeAfterAllAux' :: String -> Int -> FunSig a -> a
class BeforeAfter a where
    beforeAfterAllAux :: String -> Int -> FunSig a -> a

type family FunSig a :: * where
    FunSig (Result a) = a
    FunSig (a -> b) = a -> FunSig b

instance NFData a => BeforeAfter (Result a) where
    beforeAfterAllAux tag _ = Result . insertMsg (tag ++ " (result)") . force

instance (NFData a, BeforeAfter b) => BeforeAfter (a -> b) where
    beforeAfterAllAux tag n f x = beforeAfterAllAux tag (n+1) (f $ insertMsg (printf "%s (arg %d)" tag n) $ force x)

instance BeforeAfter' (Result a) where
    beforeAfterAllAux' tag _ = Result . insertMsg (tag ++ " (result)")

instance (BeforeAfter' b) => BeforeAfter' (a -> b) where
    beforeAfterAllAux' tag n f x = beforeAfterAllAux' tag (n+1) (f $ insertMsg (printf "%s (arg %d)" tag n) x)

beforeAfterAll' :: BeforeAfter' a => String -> FunSig a -> a
beforeAfterAll' msg = beforeAfterAllAux' msg 0

beforeAfterAll :: BeforeAfter a => String -> FunSig a -> a
beforeAfterAll msg = beforeAfterAllAux msg 0

newtype Result a = Result { getres :: a }

class GOnFields a where
    gOnFields :: String
              -> a p -> a p

instance GOnFields c => GOnFields (C1 b c) where
    gOnFields str = _M1 %~ gOnFields str
instance GOnFields c => GOnFields (D1 b c) where
    gOnFields str = _M1 %~ gOnFields str
instance (GOnFields c,Selector s) => GOnFields (S1 s c) where
    gOnFields str x = x & _M1 %~ gOnFields (str ++ ": " ++ selName x)

instance (GOnFields a,GOnFields b) => GOnFields (a :*: b) where
    gOnFields str = (left %~ gOnFields str) . (right %~ gOnFields str)

instance (GOnFields a,GOnFields b) => GOnFields (a :+: b) where
    gOnFields str = (_L1 %~ gOnFields str) . (_R1 %~ gOnFields str)

instance NFData b => GOnFields (K1 a b) where
    gOnFields str (K1 x) = K1 $ beforeAfter' str x

onFields :: (Generic a, GOnFields (Rep a))
         => String
         -> a -> a  
onFields str = generic %~ gOnFields str 
