{-# LANGUAGE TypeOperators,KindSignatures #-}
module Utilities.Instances 
    ( Generic, defaultLift, genericMEmpty, genericMAppend, genericMConcat, genericDefault )
where

import Data.Default

import GHC.Generics

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

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

class GLifts a => GLift a where
    glift :: a p -> ExpQ

class GLifts a where
    glifts :: a p -> [ExpQ]
    default glifts :: GLift a => a p -> [ExpQ]
    glifts x = [glift x]

instance GLift b => GLifts (D1 a b) where
instance GLift b => GLift (D1 a b) where
    glift (M1 x) = glift x

instance Lift b => GLifts (K1 a b) where
instance Lift b => GLift (K1 a b) where
    glift (K1 x) = lift x

instance GLift b => GLifts (S1 s b) where
instance GLift b => GLift (S1 s b) where
    glift (M1 x) = glift x

instance (Constructor c,GLifts b) => GLifts (C1 c b) where
instance (Constructor c,GLifts b) => GLift (C1 c b) where
    glift c@(M1 x) = appsE $ conE (mkName $ conName c) : glifts x

instance (GLift a, GLift b) => GLifts (a :+: b) where
instance (GLift a, GLift b) => GLift (a :+: b) where
    glift (L1 x) = glift x
    glift (R1 x) = glift x

instance GLifts U1 where
    glifts U1 = []

instance (GLifts a, GLifts b) => GLifts (a :*: b) where
    glifts (x :*: y) = glifts x ++ glifts y

defaultLift :: (Generic a, GLift (Rep a)) => a -> ExpQ
defaultLift = glift . from
