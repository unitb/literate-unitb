{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Utilities.Syntactic where

import Control.DeepSeq

import Control.Monad
import Control.Monad.Trans.Either
import Control.Monad.IO.Class

import Data.List
import Data.List.Ordered
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

instance NFData Error where
    rnf (Error msg li) = rnf (msg,li)
    rnf (MLError msg xs) = rnf (msg,xs)

show_err :: [Error] -> String
show_err xs = unlines $ map report $ sortOn line_info xs

class Syntactic a where
    line_info :: a -> LineInfo

with_li :: LineInfo -> Either [String] b -> Either [Error] b
with_li li = either (\x -> Left $ map (`Error` li) x) Right
instance Syntactic Error where
    line_info (Error _ li) = li
    line_info (MLError _ ls) = minimum $ map snd ls



report :: Error -> String
report (Error x (LI _ i j)) = format "error {0}: {1}" (i,j) (x :: String) :: String
report (MLError xs ys) = format "error: {0}\n{1}" xs 
                (unlines 
                    $ map (uncurry $ format "\t{0}: {1}") 
                    $ sortOn snd ys)

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

shrink_error_list :: [Error] -> [Error]
shrink_error_list es = do
        (xs,e,ys) <- zip3 (inits es) es (drop 1 $ tails es)
        guard $ not $ any (e `less_specific`) $ xs ++ ys
        return e
    where
        less_specific e0@(Error _ _) e1@(Error _ _) = e0 == e1
        less_specific (MLError m0 ls0) (MLError m1 ls1) = m0 == m1 && ls0' `subset` ls1'
            where
                ls0' = sortOn snd ls0
                ls1' = sortOn snd ls1
        less_specific _ _ = False
