{-# LANGUAGE BangPatterns #-}
module Utilities.Syntactic where

import Control.Monad.Trans.Either
import Control.Monad.IO.Class

import Utilities.Format

import System.IO.Unsafe

type Error = (String,Int,Int)

show_err :: [(String,Int,Int)] -> String
show_err xs = unlines $ map f xs
    where
        f (x,i,j) = format "error {0}: {1}" (i,j) (x :: String) :: String
            where 
--                !() = unsafePerformIO (print x)

class Syntactic a where
    line_info :: a -> (Int,Int)


with_li (i,j) = either (\x -> Left [(x,i,j)]) Right

with_li_t (i,j) x = EitherT $ do
    x <- runEitherT x
    either (\x -> Left [(x,i,j)]) Right x

makeReport :: MonadIO m => EitherT [Error] m String -> m String
makeReport m = eitherT f return m
    where    
--        f :: [Error] -> IO String
        f x = return $ ("Left " ++ show x)
