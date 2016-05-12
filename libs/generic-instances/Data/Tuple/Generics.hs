{-# LANGUAGE MultiParamTypeClasses
    , RankNTypes
    , FlexibleContexts
    , FlexibleInstances
    , DeriveGeneric
    , TypeOperators
    , ConstraintKinds
    , DefaultSignatures
    , ScopedTypeVariables
    , UndecidableInstances #-}
module Data.Tuple.Generics 
    ( IsTuple(..)
    , GIsTuple(..)
    , Generic, GZippableRecord
    , Rep
    , makeTuple'
    , foldMapTuple
    , foldMapTupleType
    , traverseTupleType
    , zipFields
    , zipFieldsM
    , len 
    , result0, case0 )
where

import Control.Applicative
import Control.Lens
import Control.Monad.Trans.Maybe
import Control.Monad.State
import Control.Monad.Writer

import Data.Functor.Compose
import Data.Proxy
import Data.Semigroup.Monad

import GHC.Generics hiding (from,to)
import GHC.Generics.Lens
import GHC.Generics.Utils

import Text.Read (readMaybe)

class IsTuple constr a where
    traverseTuple :: Applicative f => Proxy constr -> (forall b. constr b => b -> f b) -> a -> f a
    default traverseTuple :: (Generic a, GIsTuple constr (Rep a),Applicative f) 
                          => Proxy constr
                          -> (forall b. constr b => b -> f b) 
                          -> a -> f a
    traverseTuple p f x = (generic $ gTraverseTuple p f) x
    makeTuple :: Applicative f
              => Proxy constr
              -> (forall b. constr b => Proxy b -> f b)
              -> Proxy a -> f a
    default makeTuple :: (Generic a, GIsTuple constr (Rep a),Applicative f) 
                      => Proxy constr
                      -> (forall b. constr b => Proxy b -> f b) 
                      -> Proxy a -> f a
    makeTuple p f x = view (from generic) <$> gMakeTuple p f (view generic <$> x)
        -- <$> gMakeTuple p f

foldMapTuple :: (Monoid m,IsTuple constr a)
             => Proxy constr
             -> (forall b. constr b => b -> m)
             -> a -> m
foldMapTuple p f = execWriter . traverseTuple p (\x -> tell (f x) >> return x)

foldMapTupleType :: (Monoid m,IsTuple constr a)
                 => Proxy constr
                 -> (forall b. constr b => Proxy b -> m)
                 -> Proxy a -> m
foldMapTupleType p f x = r
    where
        g x = Compose $ tell (f x) >> return x
        (Proxy,r) = runWriter $ getCompose $ makeTuple p g x

traverseTupleType :: (Applicative f, IsTuple constr a)
                  => Proxy constr
                  -> (forall b. constr b => Proxy b -> f (Proxy b))
                  -> Proxy a -> f (Proxy a)
traverseTupleType p f = getCompose . makeTuple p (Compose . f)

len :: IsTuple constr a => Proxy constr -> Proxy a -> Int
len p = getSum . foldMapTupleType p (const 1) 

makeTuple' :: (IsTuple constr a, Applicative f) 
           => Proxy constr 
           -> (forall b. constr b => f b)
           -> f a
makeTuple' p f = makeTuple p (const f) Proxy

class GIsTuple constr a where
    gTraverseTuple :: Applicative f 
                   => Proxy constr
                   -> (forall b. constr b => b -> f b) 
                   -> a p -> f (a p)
    gMakeTuple :: Applicative f 
               => Proxy constr
               -> (forall b. constr b => Proxy b -> f b) 
               -> Proxy (a p) -> f (a p)

instance GIsTuple constr c => GIsTuple constr (M1 a b c) where
    gTraverseTuple p f (M1 x) = M1 <$> gTraverseTuple p f x
    gMakeTuple p f x = M1 <$> gMakeTuple p f (unM1 <$> x)

instance GIsTuple constr U1 where
    gTraverseTuple _ _ U1 = pure U1
    gMakeTuple _ _ _ = pure U1

instance constr b => GIsTuple constr (K1 a b) where
    gTraverseTuple _ f (K1 x) = K1 <$> f x
    gMakeTuple _ f x = K1 <$> f (unK1 <$> x)

instance (GIsTuple constr a,GIsTuple constr b) 
        => GIsTuple constr (a :*: b) where
    gTraverseTuple p f (x :*: y) = 
            (:*:) <$> gTraverseTuple p f x
                  <*> gTraverseTuple p f y
    gMakeTuple p f x =
            (:*:) <$> gMakeTuple p f (view left <$> x)
                  <*> gMakeTuple p f (view right <$> x)

class GZippableRecord constr a where
    gZipFields :: Applicative f
               => Proxy constr 
               -> (forall b. constr b => b -> b -> f b)
               -> a p -> a p -> f (a p)

instance GZippableRecord constr c 
      => GZippableRecord constr (M1 a b c) where
    gZipFields p f (M1 x) (M1 y) = M1 <$> gZipFields p f x y
instance constr b => GZippableRecord constr (K1 a b) where
    gZipFields Proxy f (K1 x) (K1 y) = K1 <$> f x y
instance (GZippableRecord constr a,GZippableRecord constr b)
      => GZippableRecord constr (a :*: b) where
    gZipFields p f (x0 :*: x1) (y0 :*: y1) = 
        liftA2 (:*:) (gZipFields p f x0 y0) (gZipFields p f x1 y1)
instance GZippableRecord constr U1 where
    gZipFields _ _ U1 U1 = pure U1

zipFields :: (Generic a,GZippableRecord constr (Rep a),Monoid c)
          => Proxy constr
          -> (forall b. constr b => b -> b -> c)
          -> a -> a -> c
zipFields p f x y = getConst $ zipFields' p (fmap Const . f) x y

zipFields' :: (Generic a,GZippableRecord constr (Rep a),Applicative f)
           => Proxy constr
           -> (forall b. constr b => b -> b -> f b)
           -> a -> a -> f a
zipFields' p f x y = view (from generic) <$> gZipFields p f (x^.generic) (y^.generic)

zipFieldsM :: (Generic a,GZippableRecord constr (Rep a),Monad m,Monoid c)
           => Proxy constr
           -> (forall b. constr b => b -> b -> m c)
           -> a -> a -> m c
zipFieldsM p f x y = getMon $ zipFields p (fmap Mon . f) x y

instance IsTuple constr () where
instance constr a => IsTuple constr (Identity a) where
instance (constr a0,constr a1) => IsTuple constr (a0,a1) where
instance (constr a0,constr a1,constr a2) 
    => IsTuple constr (a0,a1,a2) where
instance (constr a0,constr a1,constr a2,constr a3) 
    => IsTuple constr (a0,a1,a2,a3) where
instance (constr a0,constr a1,constr a2,constr a3,constr a4) 
    => IsTuple constr (a0,a1,a2,a3,a4) where
instance (constr a0,constr a1,constr a2,constr a3,constr a4,constr a5) 
    => IsTuple constr (a0,a1,a2,a3,a4,a5) where
instance (constr a0,constr a1,constr a2,constr a3,constr a4,constr a5,constr a6) 
    => IsTuple constr (a0,a1,a2,a3,a4,a5,a6) where

liftMaybe :: Monad m => Maybe a -> MaybeT m a
liftMaybe = MaybeT . return

parse :: IsTuple Read a => [String] -> Maybe a
parse = evalState cmd
    where
        readOne :: Read a => MaybeT (State [String]) a 
        readOne = do
            ys <- lift get
            (x,xs) <- liftMaybe $ uncons ys
            put xs
            liftMaybe $ readMaybe x
        p = Proxy :: Proxy Read
        cmd = runMaybeT $ do
            r  <- makeTuple' p readOne
            xs <- get
            guard (null xs)
            return r

result0 :: Maybe (Int,Float,[Int],Char)
result0 = Just (7,7.7,[7,6,5,4],'a')

case0 :: IO (Maybe (Int,Float,[Int],Char))
case0 = return $ parse ["7","7.7","[7,6,5,4]","'a'"]
