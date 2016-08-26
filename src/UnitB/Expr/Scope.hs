{-# LANGUAGE LambdaCase,TypeOperators
        ,ExistentialQuantification
        ,UndecidableInstances
        ,ConstraintKinds
        ,StandaloneDeriving #-}
module UnitB.Expr.Scope where

import Bound
import Bound.Var

import Control.DeepSeq
import Control.Monad.State as St
import Control.Precondition

import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Constraint
import Data.Constraint.Forall
import Data.Constraint.Lifting
import Data.DList as D
import Data.Foldable as F
import Data.Map as M
import Data.Monoid
import Data.Proxy
import Data.Proxy.TH
import Data.Serialize as Ser
import Data.Type.Map

import GHC.Generics
import GHC.Generics.Instances hiding (arbitrary')

import Prelude.Extras

import Test.QuickCheck
import Test.QuickCheck.ZoomEq

import Text.Pretty

canBound :: (Traversable f,Ord b)
         => Scope b f a -> Scope Int f a
canBound (Scope e) = Scope $ evalState ((traverse._B) alloc e) M.empty
    where
        alloc v = do
            gets (M.lookup v) >>= \case
                Just i -> return i
                Nothing -> do
                    n <- gets M.size
                    modify $ M.insert v n
                    return n

eqScope :: (Traversable f,Monad f,Eq1 f,Ord b0,Ord b1,Eq a)
        => Scope b0 f a -> Scope b1 f a -> Bool
eqScope e0 e1 = canBound e0 == canBound e1

compareScope :: (Traversable f,Monad f,Ord1 f,Ord b0,Ord b1,Ord a)
             => Scope b0 f a -> Scope b1 f a -> Ordering
compareScope e0 e1 = canBound e0 `compare` canBound e1

myPut :: Serialize a
      => (Serialize a :- Serialize (f a))
      -> Putter (f a)
myPut (Sub Dict) = Ser.put

putTable :: (IsKey vs,Serialize a)
         => Table vs a 
         -> ((forall f v. (Monad f,Lifting Serialize f,Serialize v) => Putter (Scope vs f v)) -> Put)
         -> Put
putTable t f = Ser.put (F.toList t') >> f putter
    where
        putter e = myPut lifting $ instantiate (pure . Left . fst . at t') (Right <$> e)
        t' = toIntMap t

data Scoped f b a = forall lv. IsKey lv => Scoped (Table lv b) (f lv a)

fmapForall :: (ForallF cl f)
           => Proxy cl
           -> ForallF cl f :- cl (f k)
           -> (cl (f k) => (a -> r) -> f k a -> z )
           -> (a -> r)
           -> f k a -> z
fmapForall _ (Sub Dict) fun = fun

makeScoped :: (Ord b,Bifunctor f,Bifoldable f)
           => f b a -> Scoped f b a
makeScoped e = mkTable (toList' e) (\f t -> Scoped t ((fromJust' .f) `first` e))

fromScoped :: Bifunctor f => Scoped f b a -> f b a
fromScoped (Scoped t x) = at t `first` x

toList' :: Bifoldable f => f a b -> [a]
toList' = D.toList . bifoldMap pure (const mempty)

instance ForallF Functor f => Functor (Scoped f b) where
    fmap f (Scoped t x) = Scoped t (fmapForall [pr|Functor|] instF fmap f x)

instance ForallF Foldable f => Foldable (Scoped f b) where
    foldMap f (Scoped _ x) = fmapForall [pr|Foldable|] instF foldMap f x
instance (ForallF Functor f,ForallF Foldable f,ForallF Traversable f) => Traversable (Scoped f b) where
    traverse f (Scoped t x) = Scoped t <$> (fmapForall [pr|Traversable|] instF traverse f x)

instance (ForallF Functor f) => Bifunctor (Scoped f) where
    bimap f g (Scoped t x) = Scoped (fmap f t) (fmapForall [pr|Functor|] instF fmap g x)

instance ForallF Foldable f => Bifoldable (Scoped f) where
    bifoldMap f g (Scoped t x) = foldMap f t <> fmapForall [pr|Foldable|] instF foldMap g x

instance (ForallF Functor f,ForallF Foldable f,ForallF Traversable f) 
        => Bitraversable (Scoped f) where
    bitraverse f g (Scoped t x) = 
            Scoped <$> traverse f t 
                   <*> fmapForall [pr|Traversable|] instF traverse g x

instance (PrettyPrintable (f b a),Bifunctor f)
        => PrettyPrintable (Scoped f b a) where
    pretty = pretty . fromScoped

instance (Bifunctor f,Eq (f b a)) => Eq (Scoped f b a) where
    x0 == x1 = 
            fromScoped x0 == fromScoped x1

instance (Bifunctor f,Ord (f b a)) => Ord (Scoped f b a) where
    x0 `compare` x1 = 
            fromScoped x0 `compare` fromScoped x1

instance (ZoomEq (f b a),Bifunctor f) => ZoomEq (Scoped f b a) where
    Scoped t0 x0 .== Scoped t1 x1 = 
            first (at t0) x0 .== first (at t1) x1

instance (Ord b, Arbitrary (f b a), Bifunctor f, Bifoldable f) 
        => Arbitrary (Scoped f b a) where
    arbitrary = makeScoped <$> arbitrary

instance (Ord b,Bifunctor f,Bifoldable f,Serialize (f b a)) 
        => Serialize (Scoped f b a) where
    get = makeScoped <$> Ser.get
    put = Ser.put . fromScoped
instance (NFData a,NFData b,Bifoldable f) => NFData (Scoped f b a) where
    rnf (Scoped t x) = F.foldr deepseq (bifoldr seq deepseq () x) t

instance (Bifunctor f,Show (f b a)) => Show (Scoped f b a) where
    showsPrec n x = ("makeScoped (" ++) . showsPrec n (fromScoped x) . ( ")" ++)

deriving instance Generic (Scope lv expr v)

instance (Eq1 expr,Show1 expr,Monad expr,ZoomEq lv,ZoomEq v,ZoomEq (expr (Var lv v))) 
        => ZoomEq (Scope lv expr v) where
    x .== y = fromScope x .== fromScope y

arbitrary' :: Arbitrary a
           => Arbitrary a :- Arbitrary (expr a)
           -> Gen (expr a)
arbitrary' (Sub Dict) = arbitrary

instance (Arbitrary a, Arbitrary b) => Arbitrary (Var a b) where
    arbitrary = genericArbitrary

instance (Monad expr,Lifting Arbitrary expr,Arbitrary lv,Arbitrary v) => Arbitrary (Scope lv expr v) where
    arbitrary = toScope <$> arbitrary' lifting

