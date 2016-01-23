{-# LANGUAGE MultiParamTypeClasses
    , RankNTypes
    , TypeOperators
    , ConstraintKinds
    , DefaultSignatures
    , ScopedTypeVariables
    , UndecidableInstances #-}
module Utilities.Tuple.Generics 
    ( IsTuple(..)
    , test_case
    , makeTuple'
    , foldMapTuple
    , foldMapTupleType
    , traverseTupleType
    , len )
where

--import Control.Exception.Assert
import Control.Lens
import Control.Monad.Trans.Maybe
import Control.Monad.State
import Control.Monad.Writer

import Data.Functor.Compose
import Data.Proxy

import GHC.Generics hiding (from,to)
import GHC.Generics.Lens

import Tests.UnitTest

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
            (:*:) <$> gMakeTuple p f (left <$> x)
                  <*> gMakeTuple p f (right <$> x)

left :: (a :*: b) p -> a p
left (x :*: _) = x

right :: (a :*: b) p -> b p
right (_ :*: x) = x

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

test_case :: TestCase
test_case = test_cases "Generic tuple" 
    [ Case "test 0: parsing" case0 result0 ]

result0 :: Maybe (Int,Float,[Int],Char)
result0 = Just (7,7.7,[7,6,5,4],'a')

case0 :: IO (Maybe (Int,Float,[Int],Char))
case0 = return $ parse ["7","7.7","[7,6,5,4]","'a'"]
