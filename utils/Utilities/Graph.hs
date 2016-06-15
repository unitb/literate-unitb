{-# LANGUAGE ScopedTypeVariables,TypeFamilies #-}
module Utilities.Graph 
    ( Composition(..), cycles, cycles_with
    , Min(..), closure
    , SCC(..)
    , m_closure, m_closure_with
--    , m_closure_with'
    , as_matrix, as_matrix_with
    , matrix_of_with, Matrix, map
    , (!), unionWith, transpose
    , mapKeys, empty, as_map, size
    , unions, times, vertices 
    , uppest, run_tests, from_list )
where
-- 

import           Control.DeepSeq
import           Control.Monad
import qualified Control.Precondition as P

import           Data.Array as A ( bounds, Array, (//), array, ixmap )
import qualified Data.Array as A -- hiding ( (!) )
import           Data.Array.ST
import           Data.Function
import           Data.Graph hiding ( vertices )
import           Data.List as L hiding ( union, (\\), transpose, map )
import qualified Data.List as L
import qualified Data.List.Ordered as OL
import           Data.Map  as M 
    ( Map, fromList, fromListWith
    , toList )
import qualified Data.Map  as M 
import           Data.Maybe
import           Data.Tuple

import GHC.Generics

import Prelude hiding ( map )

import Test.QuickCheck
import Test.QuickCheck.Report

instance Show a => Show (SCC a) where
    show (AcyclicSCC x) = show x
    show (CyclicSCC xs) = show xs

--type Array a b = 

data Matrix a b = Matrix (Map a (Map a b)) [a] b
    deriving (Eq, Show, Generic)

empty :: b -> Matrix a b
empty x = Matrix M.empty [] x

(!) :: Ord k => Matrix k b -> (k,k) -> b
(!) (Matrix m _ x) (y,z) = maybe x (M.findWithDefault x z) (M.lookup y m)

unionWith :: Ord k => (a -> a -> a) 
          -> Matrix k a -> Matrix k a -> Matrix k a
unionWith g (Matrix m0 xs x) (Matrix m1 ys y) = Matrix (M.unionWith f m0 m1) (nub $ xs ++ ys) (g x y)
    where
        f m0 m1 = M.unionWith g m0 m1

transpose :: Ord a => Matrix a b -> Matrix a b
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

as_map :: Ord t => Matrix t a -> Map (t,t) a
as_map g@(Matrix m _ x) = M.union result other
    where
        other = M.fromList $ zip (keys g) $ repeat x
        result = fromList $ do
            (x,xs) <- toList m
            (y,k)  <- toList xs
            return ((x,y),k)

map :: (a -> b) -> Matrix k a -> Matrix k b
map f (Matrix m xs x) = Matrix m' xs (f x)
    where
        m' = M.map (M.map f) m

keys :: Matrix k a -> [(k,k)]
keys (Matrix _ xs _) = [ (x,y) | x <- xs, y <- xs ]
    -- x <- M.keys m, y <- concat (M.elems $ M.map M.keys m) ]

size :: Matrix k a -> Int
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

times :: (Ord a, Composition b)
      => Matrix a b -> Matrix a b 
      -> Matrix a b
times (Matrix m0 xs x) (Matrix m1 ys y) = Matrix m2 zs z
    where
        -- f :: a -> a -> b
        f x y = (m0 P.! x) P.! y
        -- g :: a -> a -> b
        g x y = m1 P.! x P.! y
        -- m2 :: Map a (Map a b)
        m2 = fromList $ do
                x <- xs
                let -- m :: Map a b
                    m = fromList $ do
                            y <- ys
                            let xs' = L.map (x `f`) zs
                                ys' = L.map (`g` y) zs
                                zs' = zipWith seqC xs' ys'
                            [(y,uppest zs')]
                [(x,m)]
        -- zs :: [a]
        zs = xs `L.union` ys
        -- z :: b
        z  = x `seqC` y

uppest :: Composition a => [a] -> a
uppest = foldl' up zero 

vertices :: Matrix a b -> [a]
vertices (Matrix _ vs _) = vs

class Eq a => Composition a where
    below :: a -> a -> Bool
    zero :: a
    up  :: a -> a -> a
    seqC   :: a -> a -> a
    below x y = x `up` y == y

data Type a = Type

axm_comp_zero_and_up :: Composition a => a -> Bool
axm_comp_zero_and_up x = zero `up` x == x

axm_comp_zero_and_seq :: Composition a => a -> Bool
axm_comp_zero_and_seq x = zero `seqC` x == zero

axm_comp_below_and_up :: Composition a => a -> a -> Bool
axm_comp_below_and_up x y = x `below` y  ==  (x `up` y == y)

axm_comp_below_refl :: Composition a => a -> Bool
axm_comp_below_refl x = x `below` x

axm_comp_below_trans :: Composition a => a -> a -> a -> Bool
axm_comp_below_trans x y z = (x `below` y && y `below` z) ==> (x `below` z)
    where
        (==>) x y = not x || y

axm_comp_below_antisym :: Composition a => a -> a -> Bool
axm_comp_below_antisym x y = (x `below` y && y `below` x) ==> (x == y)
    where
        (==>) x y = not x || y

properties :: forall a. (Arbitrary a, Composition a, Show a) 
           => Type a -> Property
properties Type = p0 .&&. p1 .&&. p2 .&&. p3 .&&. p4 .&&. p5
    where
        p0 :: a -> Bool
        p0 = axm_comp_zero_and_up
        p1 :: a -> Bool
        p1 = axm_comp_zero_and_seq
        p2 :: a -> a -> Bool
        p2 = axm_comp_below_and_up
        p3 :: a -> Bool
        p3 = axm_comp_below_refl
        p4 :: a -> a -> a -> Bool
        p4 = axm_comp_below_trans
        p5 :: a -> a -> Bool
        p5 = axm_comp_below_antisym

prop_all :: Property
prop_all = properties (Type :: Type (Min Int))
            .&&. properties (Type :: Type Bool)

instance Composition Bool where
    zero   = False
    up x y = x || y
    seqC x y   = x && y

data Min a = 
        Min { unMin :: a }
        | Infinite
    deriving Eq

instance (Ord a, Num a) => Composition (Min a) where
    zero = Infinite
    up (Min x) (Min y) = Min $ x `min` y
    up Infinite y      = y
    up x Infinite      = x
    seqC (Min x) (Min y)   = Min $  x  +  y
    seqC Infinite _        = Infinite
    seqC _ Infinite        = Infinite

instance Arbitrary a => Arbitrary (Min a) where
    arbitrary = sized $ \sz -> do
        frequency 
            [ (1, return Infinite)
            , (sz,liftM Min arbitrary)]

instance Show a => Show (Min a) where
    show (Min x)  = show x
    show Infinite = "<inf>"

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
        f (u,v) = ((m0 P.! u, m0 P.! v),True)
        g ((i,j),b)
            | b         = [(m1 P.! i, m1 P.! j)]
            | otherwise = []

m_closure :: (Ix b, Ord b) => [(b,b)] -> Array (b,b) Bool
m_closure xs = ixmap (g m, g n) f $ closure_ ar
    where
        (m0,m1,ar) = matrix_of xs
        f (x,y)    = (m0 P.! x, m0 P.! y)
        g (i,j)    = (m1 P.! i, m1 P.! j) 
        (m,n)      = bounds ar

m_closure_with :: (Ord b) => [b] -> [(b,b)] -> Matrix b Bool
m_closure_with vs es = Matrix (M.map (M.mapKeys convert . fromList . (`zip` repeat True)) result) new_vs False
    where
            -- adjacency list
        tr          = fromList $ zip [0..] $ nub new_vs
        tr'         = fromList $ zip new_vs ([0..] :: [Int])
        new_vs      = OL.nubSort $ vs ++ L.map fst es ++ L.map snd es
        vs'         = OL.nubSort $ L.map (tr' P.!) new_vs
        es'         = L.map (\(x,y) -> (tr' P.! x, tr' P.! y)) es
        al          = M.map sort $ fromListWith (++) $ L.map m_v vs' ++ L.map m_e es'
        m_v v       = (v,[])
        m_e (v0,v1) = (v0,[v1])
        order       = cycles_with vs' es'
        f m (AcyclicSCC v) = M.adjust (`OL.union` g m v) v m
        f m (CyclicSCC vs) = fromList (zip vs $ repeat $ h m vs) `M.union` m
        g m v  = unions $ (al P.! v) : L.map (m P.!) (al P.! v)
        h m vs = unions $ vs : L.map (g m) vs
        result      = M.mapKeys convert $ foldl' f al order
        convert x   = tr P.! x

as_matrix :: Ord a => [(a, a)] -> Matrix a Bool
as_matrix xs = as_matrix_with [] xs

from_list :: forall a b. (Eq b,Ord a) => [((a,a),b)] -> b -> Matrix a b
from_list es def = Matrix zs' vs def
    where 
        zs  = [ (x,[(y,b)]) | ((x,y),b) <- es, b /= def ]
        zs' = M.map fromList $ fromListWith (++) zs
        vs  = nub $ L.map (fst . fst) es ++ L.map (snd . fst) es :: [a]

as_matrix_with :: Ord a => [a] -> [(a,a)] -> Matrix a Bool
as_matrix_with vs es = Matrix (M.map fromList $ fromListWith (++) zs) vs False
        -- zip cs (repeat False) ++ zip es (repeat True)
    where
--        cs = [ (x,y) | x <- rs, y <- rs ]
        zs = [ (x,[(y,True)]) | (x,y) <- es ]

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
        f (u,v) = ((m0 P.! u, m0 P.! v),True)

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
              writeArray ar (i,j) $ z `up` seqC x y
        return ar
    where
        ((_,m),(_,n)) = bounds ar

unions :: Ord a => [[a]] -> [a]
unions xs = unions_aux $ sortBy (compare `on` listToMaybe) xs

unions_aux :: Ord a => [[a]] -> [a]
unions_aux [] = []
unions_aux ([]:xs) = unions xs
unions_aux ((x:xs):ys) = unions_aux' x $ insertBy (compare `on` listToMaybe) xs ys

unions_aux' :: Ord a => a -> [[a]] -> [a]
unions_aux' x [] = [x]
unions_aux' x ([]:ys) = unions_aux' x ys
unions_aux' x ws@((y:ys):zs)
    | x < y     = x : unions_aux ws
    | otherwise = unions_aux' x $ insertBy (compare `on` listToMaybe) ys zs

return []
run_tests :: (PropName -> Property -> IO (a, Result))
          -> IO ([a], Bool)
run_tests = $forAllProperties'

instance (NFData a,NFData b) => NFData (Matrix a b)

