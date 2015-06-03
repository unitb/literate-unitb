{-# LANGUAGE TypeOperators      #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE KindSignatures     #-}
module Utilities.Instances where

import Data.Default
import Data.Monoid

import GHC.Generics

class GMonoid a where
    gmempty :: a p
    gmappend :: a p -> a p -> a p
    gmconcat :: [a p] -> a p

instance GMonoid c => GMonoid (M1 a b c) where
    gmempty  = M1 gmempty
    gmappend (M1 x) (M1 y) = M1 $ gmappend x y
    gmconcat xs = M1 $ gmconcat $ map unM1 xs

instance Monoid b => GMonoid (K1 a b) where
    gmempty = K1 mempty
    gmappend (K1 x) (K1 y) = K1 $ mappend x y
    gmconcat xs = K1 $ mconcat $ map unK1 xs

instance (GMonoid a,GMonoid b) => GMonoid (a :*: b) where
    gmempty = gmempty :*: gmempty
    gmappend (x0 :*: x1) (y0 :*: y1) = gmappend x0 y0 :*: gmappend x1 y1
    gmconcat xs = gmconcat (map f xs) :*: gmconcat (map g xs)
        where
            f (x :*: _) = x
            g (_ :*: x) = x

genericMEmpty :: (Generic a, GMonoid (Rep a)) => a
genericMEmpty = to gmempty
genericMAppend :: (Generic a, GMonoid (Rep a)) => a -> a -> a
genericMAppend x y = to $ gmappend (from x) (from y)
genericMConcat :: (Generic a, GMonoid (Rep a)) => [a] -> a
genericMConcat xs = to $ gmconcat $ map from xs

class GDefault a where
    gDefault :: a p

instance GDefault c => GDefault (M1 a b c) where
    gDefault = M1 gDefault

instance Default b => GDefault (K1 a b) where
    gDefault = K1 def

instance (GDefault a,GDefault b) => GDefault (a:*:b) where
    gDefault = gDefault :*: gDefault

genericDefault :: (Generic a, GDefault (Rep a)) => a
genericDefault = to gDefault
