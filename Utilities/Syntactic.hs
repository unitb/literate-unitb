{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Utilities.Syntactic where

import Control.DeepSeq

import Control.Monad.Trans.Either
import Control.Monad.IO.Class

import Data.Typeable

import Utilities.Format

--type Error = (String,Int,Int)
data Error = Error String LineInfo | MLError String [(String,LineInfo)]
    deriving (Eq,Typeable,Show)
--        { message :: String
--        , line_info :: LineInfo }

data LineInfo = LI 
        { file_name :: FilePath
        , line :: Int
        , column :: Int }     
     deriving (Eq,Ord)   

instance Show LineInfo where
    show (LI _ i j) = show (i,j)

instance NFData LineInfo where
    rnf (LI fn i j) = rnf (fn,i,j)

show_err :: [Error] -> String
show_err xs = unlines $ map report xs

class Syntactic a where
    line_info :: a -> LineInfo

with_li :: LineInfo -> Either String b -> Either [Error] b
with_li li = either (\x -> Left [Error x li]) Right


report :: Error -> String
report (Error x (LI _ i j)) = format "error {0}: {1}" (i,j) (x :: String) :: String
report (MLError xs ys) = format "error: {1}\n{2}" xs 
                (unlines $ map (uncurry $ format "\t{1}: {2}") ys)

makeReport :: MonadIO m => EitherT [Error] m String -> m String
makeReport m = eitherT f return m
    where    
--        f :: [Error] -> IO String
        f x = return $ ("Left " ++ show_err x)

format_error :: Error -> String
format_error = report

message :: Error -> String
message (Error msg _) = msg
message (MLError msg _) = msg

