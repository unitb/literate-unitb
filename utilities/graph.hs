module Utilities.Graph where

import Data.Function
import Data.Graph
import Data.List

instance Show a => Show (SCC a) where
    show (AcyclicSCC x) = show x
    show (CyclicSCC xs) = show xs

cycles xs = cycles_with [] xs

cycles_with ys xs = stronglyConnComp $ collapse $ sort $ alist ++ vs
    where
        f xs  = (fst $ head xs, fst $ head xs, map snd xs)
        vs    = map (\x -> (x,x,[])) $ nub (map fst xs ++ map snd xs ++ ys)
        alist = map f $ groupBy ((==) `on` fst) $ sort xs
        collapse ( (x1,x2,xs) : zs@( (y1,_,ys):ws ) )
            | x1 == y1  = collapse $ (x1,x2,xs++ys):ws
            | x1 /= y1  = (x1,x2,xs) : collapse zs
        collapse xs = xs

--top_sort xs 
--    where
--        cycles xs
