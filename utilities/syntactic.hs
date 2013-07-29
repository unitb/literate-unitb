module Utilities.Syntactic where

import Utilities.Format

type Error = (String,Int,Int)

show_err xs = unlines $ map f xs
    where
        f (x,i,j) = format "error {0}: {1}" (i,j) x :: String

class Syntactic a where
    line_info :: a -> (Int,Int)

with_li (i,j) = either (\x -> Left [(x,i,j)]) Right
