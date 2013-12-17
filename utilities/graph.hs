{-# LANGUAGE FlexibleInstances #-}
module Utilities.Graph 
    ( Composition, cycles, cycles_with
    , Min(..), closure
    , m_closure, m_closure_with
    , as_matrix, as_matrix_with
    , matrix_of_with )
where

import Control.Monad

import Data.Array as A -- hiding ( (!) )
--import Data.Array.IArray hiding ( (!) )
import Data.Array.ST
import Data.Function
import Data.Graph
import Data.List as L hiding ( union, (\\) )
--import Data.Map  as M hiding ( union, (\\) )

import Prelude hiding ( seq )

instance Show a => Show (SCC a) where
    show (AcyclicSCC x) = show x
    show (CyclicSCC xs) = show xs

--type Array a b = 

cycles xs = cycles_with [] xs

cycles_with ys xs = stronglyConnComp $ collapse $ sort $ alist ++ vs
    where
        f xs  = (fst $ head xs, fst $ head xs, L.map snd xs)
        vs    = L.map (\x -> (x,x,[])) $ nub (L.map fst xs ++ L.map snd xs ++ ys)
        alist = L.map f $ groupBy ((==) `on` fst) $ sort xs
        collapse ( (x1,x2,xs) : zs@( (y1,_,ys):ws ) )
            | x1 == y1  = collapse $ (x1,x2,xs++ys):ws
            | x1 /= y1  = (x1,x2,xs) : collapse zs
        collapse xs = xs

class Composition a where
    union  :: a -> a -> a
    seq    :: a -> a -> a

instance Composition Bool where
    union x y = x || y
    seq x y   = x && y

data Min a = 
    Min { unMin :: a }
    | Infinite

instance (Ord a, Num a) => Composition (Min a) where
    union (Min x) (Min y) = Min $ x `min` y
    union Infinite y      = y
    union x Infinite      = x
    seq (Min x) (Min y)   = Min $  x  +  y
    seq Infinite _        = Infinite
    seq _ Infinite        = Infinite

closure :: (Ix a, Ord a) => [(a,a)] -> [(a,a)]
closure xs = ys
    where
        vs = sort $ nub (L.map fst xs ++ L.map snd xs)
        ar = (A.listArray ((1,1),(n,n)) $ repeat False) // es
        m0  = array (head vs,last vs) $ zip vs [1..n]
        m1  = array (1,n) $ zip [1..n] vs
        es = L.map f xs
        n  = length vs
        ys = concatMap g $ A.assocs $ closure_ ar
        f (u,v) = ((m0 ! u, m0 ! v),True)
        g ((i,j),b)
            | b         = [(m1 ! i, m1 ! j)]
            | otherwise = []

m_closure :: (Ix b, Ord b) => [(b,b)] -> Array (b,b) Bool
m_closure xs = ixmap (g m, g n) f $ closure_ ar
    where
        (m0,m1,ar) = matrix_of xs
        f (x,y)    = (m0 ! x, m0 ! y)
        g (i,j)    = (m1 ! i, m1 ! j) 
        (m,n)      = bounds ar

m_closure_with :: (Ix b, Ord b) => [b] -> [(b,b)] -> Array (b,b) Bool
m_closure_with rs xs = ixmap (g m, g n) f $ closure_ ar
    where
        (m0,m1,ar) = matrix_of_with rs xs
        f (x,y)    = (m0 ! x, m0 ! y)
        g (i,j)    = (m1 ! i, m1 ! j) 
        (m,n)      = bounds ar

as_matrix xs = as_matrix_with [] xs
    where
        (m0,m1,ar) = matrix_of xs
        f (x,y)    = (m0 ! x, m0 ! y)
        g (i,j)    = (m1 ! i, m1 ! j) 
        (m,n)      = bounds ar

as_matrix_with :: (Ix a, Ord a) => [a] -> [(a,a)] -> Array (a,a) Bool
as_matrix_with rs xs = ixmap (g m, g n) f ar
    where
        (m0,m1,ar) = matrix_of_with rs xs
        f (x,y)    = (m0 ! x, m0 ! y)
        g (i,j)    = (m1 ! i, m1 ! j) 
        (m,n)      = bounds ar

matrix_of :: (Ix a, Ord a) => [(a,a)] -> (Array a Int, Array Int a, Array (Int,Int) Bool)
matrix_of xs = matrix_of_with [] xs

    -- replace the maps with arrays
matrix_of_with :: (Ix a, Ord a) => [a] -> [(a,a)] -> (Array a Int, Array Int a, Array (Int,Int) Bool)
matrix_of_with rs xs = (m0,m1,ar)
    where
        vs = sort $ nub (L.map fst xs ++ L.map snd xs ++ rs)
        ar = (A.listArray ((1,1),(n,n)) $ repeat False) // es
        m0  = array (head vs, last vs) $ zip vs [1..n]
        m1  = array (1,n) $ zip [1..n] vs
        es = L.map f xs
        n  = length vs
        f (u,v) = ((m0 ! u, m0 ! v),True)

--edges_of 

closure_ :: Composition a => Array (Int,Int) a -> Array (Int,Int) a
closure_ ar = runSTArray $ do
        ar <- thaw ar 
        forM_ [m..n] $ \k -> do
          forM_ [m..n] $ \i -> do
            forM_ [m..n] $ \j -> do
              x <- readArray ar (i,k)
              y <- readArray ar (k,j)
              z <- readArray ar (i,j)
              writeArray ar (i,j) $ z `union` seq x y
        return ar
    where
        ((_,m),(_,n)) = bounds ar

--top_sort xs 
--    where
--        cycles xs
