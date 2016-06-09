{-# LANGUAGE TypeOperators,StandaloneDeriving #-}
module Test.QuickCheck.ZoomEq where

import Control.Invariant (Checked,content')
import Control.Lens hiding (from,to)

import Data.List.NonEmpty as NE (toList,NonEmpty)
import qualified Data.Map as M
import Data.Functor.Classes
import Data.Functor.Compose
import Data.Proxy
import Data.Word

import GHC.Generics

import Test.QuickCheck

infix 4 .==

newtype ShallowZoom a = ShallowZoom { unShallowZoom :: a } 
    deriving (Eq, Show)

class (Eq a,Show a) => ZoomEq a where
    (.==) :: a -> a -> Property
    default (.==) :: (GZoomEq (Rep a),Generic a,Eq a) 
                   => a -> a -> Property
    (.==) = genericZoomEq

genericZoomEq :: (GZoomEq (Rep a),Generic a,Eq a,Show a) 
              => a -> a -> Property
genericZoomEq x y | null xs   = x === y
                  | otherwise = x == y .||. conjoin xs
    where
        xs = gZoomEq (from x) (from y)

instance (Eq a,Show a) => ZoomEq (ShallowZoom a) where
    (.==) = (===)

instance ZoomEq (Proxy a) where
deriving instance ZoomEq a => ZoomEq (Identity a) 
instance ZoomEq Char where
    (.==) = (===)
instance ZoomEq Float where
    (.==) = (===)
instance ZoomEq Double where
    (.==) = (===)
instance ZoomEq Int where
    (.==) = (===)
instance ZoomEq Word16 where
    (.==) = (===)
instance ZoomEq Word32 where
    (.==) = (===)
instance ZoomEq Word64 where
    (.==) = (===)
instance (ZoomEq a,ZoomEq b) => ZoomEq (Either a b) where
deriving instance (ZoomEq (f (g a)),Eq a,Eq1 f,Eq1 g,Show a,Functor f,Show1 f,Show1 g) 
        => ZoomEq (Compose f g a) 
instance ZoomEq a => ZoomEq (Checked a) where
    x .== y = (x^.content') .== (y^.content')
instance ZoomEq a => ZoomEq (Maybe a) where
instance ZoomEq () where
    () .== () = property True
instance (ZoomEq a,ZoomEq b) => ZoomEq (a,b) where
instance (ZoomEq a,ZoomEq b,ZoomEq c) => ZoomEq (a,b,c) where
instance (ZoomEq a,ZoomEq b,ZoomEq c,ZoomEq d) => ZoomEq (a,b,c,d) where
instance (ZoomEq a,ZoomEq b,ZoomEq c,ZoomEq d,ZoomEq e) => ZoomEq (a,b,c,d,e) where

instance ZoomEq a => ZoomEq (NonEmpty a) where
    xs .== ys = NE.toList xs .== NE.toList ys

instance (Ord k,Show k,ZoomEq a) => ZoomEq (M.Map k a) where
    xs .== ys = conjoin [pXS,pYS,conjoin $ M.elems $ M.intersectionWithKey prop xs ys]
        where
            xs' = xs `M.difference` ys
            ys' = ys `M.difference` xs
            pXS = counterexample ("left keys:  " ++ show (M.keys xs')) $ M.null xs'
            pYS = counterexample ("right keys: " ++ show (M.keys ys')) $ M.null ys'
            prop k x y = counterexample ("key: " ++ show k) (x .== y)

instance ZoomEq a => ZoomEq [a] where
    xs .== ys = conjoin $
                    zipWith3 (\i x y -> counterexample (show i) $ x .== y) [0..] xs ys
                ++ [counterexample ("length") (length xs === length ys)]

class GZoomEq a where
    gZoomEq :: a p -> a p -> [Property]

instance GZoomEq a => GZoomEq (D1 z a) where
    gZoomEq (M1 x) (M1 y) = gZoomEq x y

instance (GZoomEq a,Constructor c) => GZoomEq (C1 c a) where
    gZoomEq c@(M1 x) (M1 y) = map (counterexample $ conName c) $ gZoomEq x y

instance (ZoomEq a,Show a) => GZoomEq (K1 k a) where
    gZoomEq (K1 x) (K1 y) = [x .== y]

conjProp :: (Property -> Property) 
         -> [Property] -> [Property]
conjProp _ [] = []
conjProp f xs = [conjoin $ map f xs]

instance (GZoomEq a,Selector s) => GZoomEq (S1 s a) where
    gZoomEq s@(M1 x) (M1 y) = 
            conjProp (counterexample (selName s ++ " = ")) 
                $ gZoomEq x y

instance (GZoomEq a,GZoomEq b) => GZoomEq (a :*: b) where
    gZoomEq (x0 :*: x1) (y0 :*: y1) = gZoomEq x0 y0 ++ gZoomEq x1 y1

instance (GZoomEq a,GZoomEq b) => GZoomEq (a :+: b) where
    gZoomEq (L1 x) (L1 y) = gZoomEq x y
    gZoomEq (R1 x) (R1 y) = gZoomEq x y
    gZoomEq _ _ = []

instance GZoomEq U1 where
    gZoomEq _ _ = [property True]
