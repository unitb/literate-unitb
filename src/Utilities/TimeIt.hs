module Utilities.TimeIt where

import Control.Exception
import Control.Monad.State

import Data.Time
import Data.Tuple

import Text.Printf

formatDiff :: NominalDiffTime -> String 
formatDiff dt = printf "%s.%03d" (evalState formatDiffState s) (truncate $ fs * 1000 :: Int)
    where
        (s,fs) = properFraction dt

formatDiffState :: State Int String
formatDiffState = do
    s <- state $ swap . (`divMod` 60)
    m <- state $ swap . (`divMod` 60)
    h <- get
    return $ printf "%d:%02d:%02d" h m s 

timeIt :: IO a -> IO a
timeIt cmd = do
        (t,x) <- time cmd
        putStrLn $ formatDiff t
        return x

timeItT :: IO a -> IO (Double,a)
timeItT cmd = do
        (t,x) <- time cmd
        return (fromRational $ toRational t,x)

time :: IO t -> IO (NominalDiffTime, t)
time cmd = do 
        t0 <- getCurrentTime
        x <- evaluate =<< cmd
        t <- getCurrentTime
        return (diffUTCTime t t0, x)