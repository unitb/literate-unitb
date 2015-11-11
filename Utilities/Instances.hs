{-# LANGUAGE TypeOperators,KindSignatures, TypeFamilies,ScopedTypeVariables #-}
module Utilities.Instances 
    ( Generic, defaultLift, genericMEmpty, genericMAppend
    , genericMConcat, genericDefault, genericSemigroupMAppend
    , Intersection(..), genericSemigroupMAppendWith
    , genericArbitrary, inductive, listOf', arbitrary' )
where

import Control.Monad.Fix
import Control.Lens hiding (to,from)

import Data.Default
import Data.Functor.Compose
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as S
import Data.Semigroup

import GHC.Generics

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

import Test.QuickCheck

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

class GSemigroupWith a where
    gSemiMAppend :: a p -> a p -> a p

instance (GSemigroupWith c) => GSemigroupWith (M1 a b c) where
    gSemiMAppend x y = M1 (gSemiMAppend (unM1 x) (unM1 y))

instance Semigroup b => GSemigroupWith (K1 a b) where
    gSemiMAppend x y = K1 (unK1 x <> unK1 y)

instance (GSemigroupWith a,GSemigroupWith b) 
        => GSemigroupWith (a :*: b) where
    gSemiMAppend x y = gSemiMAppend (left x) (left y) :*:
                             gSemiMAppend (right x) (right y)

left :: (a :*: b) p -> a p
left (x :*: _) = x
right :: (a :*: b) p -> b p
right (_ :*: x) = x

class Applicative f => MapFields a (f :: * -> *) where
    type Mapped a f :: * -> *
    put :: f (a p) -> Mapped a f p
    get :: Mapped a f p -> f (a p)
    mapped :: Iso' (f (a p)) (Mapped a f p)
    mapped = iso put get

instance MapFields c f => MapFields (M1 a b c) f where
    type Mapped (M1 a b c) f = M1 a b (Mapped c f)
    put x = M1 $ put (unM1 <$> x)
    get x = M1 <$> get (unM1 x)

instance (Applicative f) => MapFields (K1 a b) f where
    type Mapped (K1 a b) f = K1 a (f b)
    put = K1 . fmap unK1
    get = fmap K1 . unK1

instance (MapFields a f,MapFields b f) => MapFields (a :*: b) f where
    type Mapped (a :*: b) f = Mapped a f :*: Mapped b f
    put x = put (left <$> x) :*: put (right <$> x)
    get x = (:*:) <$> get (left x) <*> get (right x)


genericMEmpty :: (Generic a, GMonoid (Rep a)) => a
genericMEmpty = to gmempty
genericMAppend :: (Generic a, GMonoid (Rep a)) => a -> a -> a
genericMAppend x y = to $ gmappend (from x) (from y)
genericMConcat :: (Generic a, GMonoid (Rep a)) => [a] -> a
genericMConcat xs = to $ gmconcat $ map from xs

genericSemigroupMAppend :: (Generic a, GSemigroupWith (Rep a)) => a -> a -> a
genericSemigroupMAppend x y = to $ gSemiMAppend (from x) (from y)

genericSemigroupMAppendWith :: forall a f. (Functor f,Generic a,MapFields (Rep a) f,GSemigroupWith (Mapped (Rep a) f)) => f a -> f a -> f a
genericSemigroupMAppendWith x y = to <$> get (gSemiMAppend (put $ from <$> x) (put $ from <$> y))

newtype Intersection a = Intersection { getIntersection :: a }
    deriving (Functor)

instance Applicative Intersection where
    pure = Intersection
    Intersection f <*> Intersection x = Intersection $ f x

instance Ord k => Semigroup (Intersection (Map k a)) where
    Intersection x <> Intersection y = Intersection $ x `M.intersection` y

instance Ord k => Semigroup (Intersection (Set k)) where
    Intersection x <> Intersection y = Intersection $ x `S.intersection` y

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

class GArbitrary a where
    gArbitrary :: [Gen (a p)]

instance GArbitrary c => GArbitrary (M1 a b c) where
    gArbitrary = fmap M1 <$> gArbitrary

instance Arbitrary b => GArbitrary (K1 a b) where
    gArbitrary = [K1 <$> arbitrary]

instance (GArbitrary a,GArbitrary b) => GArbitrary (a :*: b) where
    gArbitrary = getCompose $ (:*:) <$> Compose gArbitrary <*> Compose gArbitrary

instance (GArbitrary a,GArbitrary b) => GArbitrary (a :+: b) where
    gArbitrary = (fmap L1 <$> gArbitrary) ++ (fmap R1 <$> gArbitrary)

instance GArbitrary U1 where
    gArbitrary = [return U1]

genericArbitrary :: (Generic a, GArbitrary (Rep a)) => Gen a
genericArbitrary = to <$> oneof gArbitrary

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

inductive :: (Compose Maybe Gen a -> [Compose Maybe Gen a]) -> Gen a
inductive f = sized $ fix $ \ind n -> oneof =<< catMaybes . map getCompose . f <$> cmd ind n
    where
        cmd :: (Int -> Gen a) -> Int -> Gen (Compose Maybe Gen a)
        cmd r n =
                if n == 0 then return $ Compose Nothing
                          else return $ Compose $ Just $ r (n `div` 10)

listOf' :: Compose Maybe Gen a -> Compose Maybe Gen [a]
listOf' (Compose cmd) = Compose $ listOf <$> cmd

arbitrary' :: Arbitrary a => Compose Maybe Gen a
arbitrary' = Compose $ Just arbitrary
