{-# LANGUAGE TypeOperators
        , QuasiQuotes
        , StandaloneDeriving
        , ConstraintKinds
        , RankNTypes
        , TemplateHaskell
        , DeriveGeneric
        , DeriveTraversable
        , TypeFamilies
        , GeneralizedNewtypeDeriving
        , KindSignatures
        , TypeSynonymInstances
        , FlexibleInstances
        , FlexibleContexts
        , DeriveFunctor
        , ScopedTypeVariables
        , MultiParamTypeClasses
        , DefaultSignatures #-}
module GHC.Generics.Instances 
    ( Generic, genericLift, genericMEmpty, genericMAppend
    , genericMConcat, genericDefault, genericSemigroupMAppend
    , Intersection(..), genericSemigroupMAppendWith
    , genericSemigroupMConcat, genericSemigroupMConcatWith
    , show1, shows1, NFData1(..), deepseq1
    , Serialize1(..)
    , genericArbitrary, inductive, listOf', arbitrary' 
    , Lift1(..), Monoid1(..)
    , Default1(..)
    , OnFunctor(..) )
where

import Control.DeepSeq
import Control.Monad.Fix
import Control.Monad.Trans.Instances ()
import Control.Lens

import Data.Default
import Data.Either.Validation
import Data.Functor.Classes
import Data.Functor.Compose
import Data.Hashable
import Data.DList (DList)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import Data.List.NonEmpty (NonEmpty(..))
import Data.Proxy
import Data.Proxy.TH
import Data.Serialize (Serialize)
import qualified Data.Serialize as S
import Data.Set (Set)
import qualified Data.Set as S
import Data.Semigroup
import Data.Tuple.Generics
import Data.Typeable
import Data.Typeable.Internal

import GHC.Generics.Utils

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
    gSemiMConcat :: NonEmpty (a p) -> a p

instance (GSemigroupWith c) => GSemigroupWith (M1 a b c) where
    gSemiMAppend x y = M1 (gSemiMAppend (unM1 x) (unM1 y))
    gSemiMConcat xs  = M1 (gSemiMConcat $ unM1 <$> xs)

instance Semigroup b => GSemigroupWith (K1 a b) where
    gSemiMAppend x y = K1 (unK1 x <> unK1 y)
    gSemiMConcat xs  = K1 (sconcat $ unK1 <$> xs)

instance (GSemigroupWith a,GSemigroupWith b) 
        => GSemigroupWith (a :*: b) where
    gSemiMAppend x y = gSemiMAppend (x^.left) (y^.left) :*:
                             gSemiMAppend (x^.right) (y^.right)
    gSemiMConcat xs = gSemiMConcat (view left <$> xs) :*: gSemiMConcat (view right <$> xs)

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
    put x = put (view left <$> x) :*: put (view right <$> x)
    get x = (:*:) <$> get (x^.left) <*> get (x^.right)


genericMEmpty :: (Generic a, GMonoid (Rep a)) => a
genericMEmpty = gmempty^.from generic
genericMAppend :: (Generic a, GMonoid (Rep a)) => a -> a -> a
genericMAppend x y = gmappend (x^.generic) (y^.generic)^.from generic
genericMConcat :: (Generic a, GMonoid (Rep a)) => [a] -> a
genericMConcat xs = gmconcat (map (view generic) xs)^.from generic

class Monoid1 (f :: * -> *) where
    mempty1 :: f a
    default mempty1 :: Monoid (f a) => f a
    mempty1 = mempty
    mappend1 :: f a -> f a -> f a
    default mappend1 :: Monoid (f a) => f a -> f a -> f a
    mappend1 = mappend
    mconcat1 :: [f a] -> f a
    default mconcat1 :: Monoid (f a) => [f a] -> f a
    mconcat1 = mconcat

instance Monoid1 f => Monoid (OnFunctor f a) where
    mempty  = OnFunctor mempty1
    mappend (OnFunctor x) (OnFunctor y) = OnFunctor $ x `mappend1` y
    mconcat xs = OnFunctor $ mconcat1 $ map getFunctor xs

instance Monoid1 [] where
instance Monoid1 DList where
instance Ord k => Monoid1 (Map k) where

genericSemigroupMAppend :: (Generic a, GSemigroupWith (Rep a)) => a -> a -> a
genericSemigroupMAppend x y = gSemiMAppend (x^.generic) (y^.generic)^.from generic

genericSemigroupMConcat :: (Generic a, GSemigroupWith (Rep a)) => NonEmpty a -> a
genericSemigroupMConcat xs = gSemiMConcat (view generic <$> xs)^.from generic

genericSemigroupMAppendWith :: forall a f. (Functor f,Generic a,MapFields (Rep a) f,GSemigroupWith (Mapped (Rep a) f)) 
                            => f a -> f a -> f a
genericSemigroupMAppendWith x y = view (from generic) <$> get (gSemiMAppend (put $ view generic <$> x) (put $ view generic <$> y))

genericSemigroupMConcatWith :: forall a f. (Functor f,Generic a,MapFields (Rep a) f,GSemigroupWith (Mapped (Rep a) f)) 
                            => NonEmpty (f a) -> f a
genericSemigroupMConcatWith xs = view (from generic) <$> get (gSemiMConcat $ put.fmap (view generic) <$> xs)

newtype Intersection a = Intersection { getIntersection :: a }
    deriving (Functor)

instance Applicative Intersection where
    pure = Intersection
    Intersection f <*> Intersection x = Intersection $ f x

instance Ord k => Semigroup (Intersection (Map k a)) where
    Intersection x <> Intersection y = Intersection $ x `M.intersection` y

instance Ord k => Semigroup (Intersection (Set k)) where
    Intersection x <> Intersection y = Intersection $ x `S.intersection` y



class Default1 f where
    def1 :: Default a => f a

instance (Functor f,Default1 f,Default1 g,Default x) => Default (Compose f g x) where
    def = Compose $ getFunctor <$> def1



instance (Default x,Default1 f) => Default (OnFunctor f x) where
    def = OnFunctor def1


makeTuple'' :: (Generic a, GIsTuple constr (Rep a),Applicative f) 
            => Proxy constr 
            -> (forall b. constr b => Proxy b -> f b)
            -> Proxy a
            -> f a
makeTuple'' p f x = view (from generic) <$> gMakeTuple p f (view generic <$> x)

genericDefault :: (Generic a, GIsTuple Default (Rep a)) => a
genericDefault = runIdentity $ makeTuple'' [pr|Default|] (const $ Identity def) Proxy

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
genericArbitrary = view (from generic) <$> oneof gArbitrary

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

genericLift :: (Generic a, GLift (Rep a)) => a -> ExpQ
genericLift = glift . view generic

instance Lift a => Lift (NonEmpty a) where
    lift = genericLift

instance (Lift k,Lift a,Ord k) => Lift (Map k a) where
    lift m = [e| M.fromList $(listE $ lift <$> M.toList m) |]

instance (Lift a,Ord a) => Lift (Set a) where
    lift m = [e| S.fromList $(listE $ lift <$> S.toList m) |]

instance Lift Loc where
    lift = genericLift

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

instance Eq1 Proxy where
    eq1 = (==)
instance Eq1 NonEmpty where
    eq1 = (==)

instance Ord1 NonEmpty where
    compare1 = compare

instance Show1 Proxy where
    showsPrec1 = showsPrec

instance Show1 NonEmpty where
    showsPrec1 = showsPrec

instance (Show1 f,Show a) => Show (OnFunctor f a) where
    show = show1 . getFunctor

show1 :: (Show a, Show1 f) => f a -> String
show1 x = showsPrec1 0 x ""

shows1 :: (Show a, Show1 f) => f a -> ShowS
shows1 = showsPrec1 0

class NFData1 f where
    rnf1 :: NFData a => f a -> ()

deepseq1 :: (NFData a, NFData1 f) => f a -> b -> b
deepseq1 x y = rnf1 x `seq` y

instance NFData1 Proxy where
    rnf1 = rnf
instance NFData a => NFData1 (Const a) where
    rnf1 = rnf
instance NFData1 Identity where
    rnf1 = rnf
instance NFData1 [] where
    rnf1 = rnf
instance NFData1 NonEmpty where
    rnf1 = rnf
instance (Functor f,NFData1 f,NFData1 g) => NFData1 (Compose f g) where
    rnf1 = rnf . OnFunctor . fmap OnFunctor . getCompose
instance NFData a => NFData1 ((,) a) where
    rnf1 = rnf
instance NFData1 Maybe where
    rnf1 = rnf

newtype OnFunctor f a = OnFunctor { getFunctor :: (f a) }
    deriving (Functor,Applicative,Monad,Traversable,Foldable)

instance Rewrapped (OnFunctor f a) (OnFunctor g b) where

instance Wrapped (OnFunctor f a) where
    type Unwrapped (OnFunctor f a) = f a
    _Wrapped' = iso getFunctor OnFunctor

instance (NFData a,NFData1 f) => NFData (OnFunctor f a) where
    rnf = rnf1 . getFunctor

class Lift1 f where
    lift1 :: Lift a => f a -> ExpQ

instance Lift a => Lift (Const a b) where
    lift (Const x) = [e| Const $(lift x) |]
instance Lift a => Lift (Identity a) where
    lift (Identity x) = [e| Identity $(lift x) |]
instance Lift a => Lift1 (Const a) where
    lift1 = lift
instance Lift1 Identity where
    lift1 = lift
instance Lift1 [] where
    lift1 = lift
instance Lift1 NonEmpty where
    lift1 = lift
instance (Lift1 f,Lift1 g,Functor f) => Lift1 (Compose f g) where
    lift1 (Compose x) = lift1 $ OnFunctor <$> x
instance (Lift1 f,Lift a) => Lift (OnFunctor f a) where
    lift (OnFunctor x) = lift1 x
instance Lift a => Lift1 ((,) a) where
    lift1 = lift
instance Lift1 Maybe where
    lift1 = lift

instance Semigroup (DList a) where

deriving instance Generic (Validation a b)
deriving instance Generic Fingerprint
deriving instance Generic TypeRep
deriving instance Generic TyCon

instance (NFData a,NFData b) => NFData (Validation a b) where

class Serialize1 f where
    put1 :: Serialize a => S.Putter (f a)
    default put1 :: Serialize (f a) => S.Putter (f a)
    put1 = S.put
    get1 :: Serialize a => S.Get (f a)
    default get1 :: Serialize (f a) => S.Get (f a)
    get1 = S.get

instance Serialize1 Proxy where
instance Serialize1 NonEmpty where
instance Serialize1 Identity where
instance Serialize1 Maybe where

instance Serialize (Proxy a) where

instance Serialize (f (g a)) 
        => Serialize (Compose f g a) where
instance Serialize Fingerprint where
instance Serialize TyCon where
instance Serialize TypeRep where
instance Serialize a => Serialize (NonEmpty a) where
instance Serialize a => Serialize (Identity a) where

instance Arbitrary a => Arbitrary (Identity a) where
    arbitrary = Identity <$> arbitrary
instance Arbitrary (Proxy a) where
    arbitrary = return Proxy

instance (Serialize a,Serialize1 f) => Serialize (OnFunctor f a) where
    put = put1 . getFunctor
    get = OnFunctor <$> get1

instance (Hashable k,Hashable a) => Hashable (Map k a) where
    hashWithSalt salt = hashWithSalt salt . M.toList

instance Hashable a => Hashable (Set a) where
    hashWithSalt salt = hashWithSalt salt . S.toList
