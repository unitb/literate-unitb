{-# LANGUAGE FlexibleInstances #-}
module Utilities.Graph 
    ( Composition, cycles, cycles_with
    , Min(..), closure
    , m_closure, m_closure_with
--    , m_closure_with'
    , as_matrix, as_matrix_with
    , matrix_of_with, Matrix, map
    , (!), unionWith, transpose
    , mapKeys, empty, as_map, size )
where

import Control.Monad

import           Data.Array as A ( bounds, Array, (//), array, ixmap )
import qualified Data.Array as A -- hiding ( (!) )
import           Data.Array.ST
import           Data.Function
import           Data.Graph
import           Data.List as L hiding ( union, (\\), transpose, map )
import qualified Data.List as L
import           Data.Map  as M 
    ( Map, fromList, fromListWith
    , toList )
import qualified Data.Map  as M 
import           Data.Tuple

import Prelude hiding ( seq, map )

instance Show a => Show (SCC a) where
    show (AcyclicSCC x) = show x
    show (CyclicSCC xs) = show xs

--type Array a b = 

data Matrix a b = Matrix (Map a (Map a b)) [a] b
    deriving (Eq, Show)

empty x = Matrix M.empty [] x

(Matrix m _ x) ! (y,z) = maybe x (M.findWithDefault x z) (M.lookup y m)

unionWith g (Matrix m0 xs x) (Matrix m1 ys _) = Matrix (M.unionWith f m0 m1) (nub $ xs ++ ys) x
    where
        f m0 m1 = M.unionWith g m0 m1

transpose m = mapKeys swap m

mapKeys :: Ord b => ((a,a) -> (b,b)) -> Matrix a c -> Matrix b c 
mapKeys f (Matrix m xs x) = Matrix result (nub ys) x
    where
        result = M.map fromList 
            $ fromListWith (++) $ do
                (x,xs) <- toList $ M.map toList m
                (y,k)  <- xs
                let (x',y') = f (x,y)
                return (x',[(y',k)])
        ys = do
                x <- xs
                y <- xs
                let (x',y') = f (x,y)
                [x',y']

as_map g@(Matrix m _ x) = M.union result other
    where
        other = M.fromList $ zip (keys g) $ repeat x
        result = fromList $ do
            (x,xs) <- toList m
            (y,k)  <- toList xs
            return ((x,y),k)

map f (Matrix m xs x) = Matrix m' xs (f x)
    where
        m' = M.map (M.map f) m

keys (Matrix _ xs _) = [ (x,y) | x <- xs, y <- xs ]
    -- x <- M.keys m, y <- concat (M.elems $ M.map M.keys m) ]

size (Matrix m _ _)  = sum $ L.map M.size $ M.elems m

cycles :: Ord a => [(a,a)] -> [SCC a]
cycles xs = cycles_with [] xs

cycles_with :: Ord a => [a] -> [(a,a)] -> [SCC a]
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
    up  :: a -> a -> a
    seq    :: a -> a -> a

instance Composition Bool where
    up x y = x || y
    seq x y   = x && y

data Min a = 
    Min { unMin :: a }
    | Infinite

instance (Ord a, Num a) => Composition (Min a) where
    up (Min x) (Min y) = Min $ x `min` y
    up Infinite y      = y
    up x Infinite      = x
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
        f (u,v) = ((m0 A.! u, m0 A.! v),True)
        g ((i,j),b)
            | b         = [(m1 A.! i, m1 A.! j)]
            | otherwise = []

m_closure :: (Ix b, Ord b) => [(b,b)] -> Array (b,b) Bool
m_closure xs = ixmap (g m, g n) f $ closure_ ar
    where
        (m0,m1,ar) = matrix_of xs
        f (x,y)    = (m0 M.! x, m0 M.! y)
        g (i,j)    = (m1 A.! i, m1 A.! j) 
        (m,n)      = bounds ar

--m_closure_with :: (Ix b, Ord b) => [b] -> [(b,b)] -> Array (b,b) Bool
--m_closure_with rs xs = ixmap (g m, g n) f $ closure_ ar
--    where
--        (m0,m1,ar) = matrix_of_with rs xs
--        f (x,y)    = (m0 ! x, m0 ! y)
--        g (i,j)    = (m1 ! i, m1 ! j) 
--        (m,n)      = bounds ar

--m_closure_with' :: Ord b => [b] -> [(b,b)] -> Matrix b Bool
--m_closure_with' rs xs = mapKeys g $ fromList $ assocs $ closure_ ar
--    where
--        (_,m1,ar) = matrix_of_with rs xs
--        g (i,j)    = (m1 A.! i, m1 A.! j) 

m_closure_with :: (Ord b) => [b] -> [(b,b)] -> Matrix b Bool
m_closure_with vs es = Matrix (M.map (fromList . (`zip` repeat True)) result) vs False
--fromList $ do
--        (x,xs) <- toList result
--        y      <- vs
--        return ((x,y),y `elem` xs)
    where
        list        = fromListWith (++) $ L.map m_v vs ++ L.map m_e es
        m_v v       = (v,[])
        m_e (v0,v1) = (v0,[v1])
        order       = cycles_with vs es
        f m (AcyclicSCC v) = M.adjust (++ g m v) v m
        f m (CyclicSCC vs) = fromList (zip vs $ repeat $ h m vs) `M.union` m
        g m v  = list M.! v ++ concatMap (m M.!) (list M.! v)
        h m vs = vs ++ concatMap (g m) vs
        result      = foldl f list order

as_matrix :: Ord a => [(a, a)] -> Matrix a Bool
as_matrix xs = as_matrix_with [] xs

as_matrix_with :: Ord a => [a] -> [(a,a)] -> Matrix a Bool
as_matrix_with vs es = Matrix (M.map fromList $ fromListWith (++) zs) vs False
        -- zip cs (repeat False) ++ zip es (repeat True)
    where
--        cs = [ (x,y) | x <- rs, y <- rs ]
        zs = [ (x,[(y,True)]) | (x,y) <- es ]

--as_matrix_with :: (Ix a, Ord a) => [a] -> [(a,a)] -> Array (a,a) Bool
--as_matrix_with rs xs = ixmap (g m, g n) f ar
--    where
--        (m0,m1,ar) = matrix_of_with rs xs
--        f (x,y)    = (m0 ! x, m0 ! y)
--        g (i,j)    = (m1 ! i, m1 ! j) 
--        (m,n)      = bounds ar

matrix_of :: (Ord a) => [(a,a)] -> (Map a Int, Array Int a, Array (Int,Int) Bool)
matrix_of xs = matrix_of_with [] xs

    -- replace the maps with arrays
matrix_of_with :: (Ord a) => [a] -> [(a,a)] -> (Map a Int, Array Int a, Array (Int,Int) Bool)
matrix_of_with rs xs = (m0,m1,ar)
    where
        vs = sort $ nub (L.map fst xs ++ L.map snd xs ++ rs)
        ar = (A.listArray ((1,1),(n,n)) $ repeat False) // es
--        m0  = array (head vs, last vs) $ zip vs [1..n]
        m0  = fromList $ zip vs [1..n]
        m1  = array (1,n) $ zip [1..n] vs
        es = L.map f xs
        n  = length vs
        f (u,v) = ((m0 M.! u, m0 M.! v),True)

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
              writeArray ar (i,j) $ z `up` seq x y
        return ar
    where
        ((_,m),(_,n)) = bounds ar

--top_sort xs 
--    where
--        cycles xs
