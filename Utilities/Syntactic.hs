{-# LANGUAGE BangPatterns, TupleSections #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell      #-}
module Utilities.Syntactic where

import Control.DeepSeq
import Control.Lens

import Control.Monad
import Control.Monad.Trans.Either
import Control.Monad.IO.Class

import Data.DeriveTH
import Data.List
import Data.List.Ordered
import Data.Typeable

import Utilities.Format

data Error = Error String LineInfo | MLError String [(String,LineInfo)]
    deriving (Eq,Typeable,Show,Ord)

data LineInfo = LI 
        { _filename :: FilePath
        , _line :: Int
        , _column :: Int }     
     deriving (Eq,Ord)   

instance Show LineInfo where
    show (LI _ i j) = show (i,j)

makeLenses ''LineInfo

show_err :: [Error] -> String
show_err xs = unlines $ map report $ sortOn line_info xs

class Syntactic a where
    line_info :: a -> LineInfo

with_li :: LineInfo -> Either [String] b -> Either [Error] b
with_li li = either (\x -> Left $ map (`Error` li) x) Right
instance Syntactic Error where
    line_info (Error _ li) = li
    line_info (MLError _ ls) = minimum $ map snd ls

showLiLong :: LineInfo -> String
showLiLong (LI fn ln col) = format "{0}:{1}:{2}" fn ln col

report :: Error -> String
report (Error msg li) = format "{1}:\n    {0}" msg (showLiLong li)
report (MLError msg ys) = format "{0}\n{1}" msg
                (unlines 
                    $ map (\(msg,li) -> format "{1}:\n\t{0}\n" msg (showLiLong li)) 
                    $ sortOn snd ys)

makeReport :: MonadIO m => EitherT [Error] m String -> m String
makeReport = liftM fst . makeReport' () . liftM (,())

makeReport' :: MonadIO m => a -> EitherT [Error] m (String,a) -> m (String,a)
makeReport' def m = eitherT f return m
    where    
        f x = return ("Left " ++ show_err x,def)

format_error :: Error -> String
format_error = report

message :: Error -> String
message (Error msg _) = msg
message (MLError msg _) = msg

shrink_error_list :: [Error] -> [Error]
shrink_error_list es' = do
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
        es = nubSort es'

derive makeNFData ''Error
derive makeNFData ''LineInfo
