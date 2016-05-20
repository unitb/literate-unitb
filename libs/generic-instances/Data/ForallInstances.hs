{-# LANGUAGE KindSignatures, PolyKinds, ConstraintKinds #-}
module Data.ForallInstances 
  ( module Data.ForallInstances 
  , module Data.Constraint )
where

import Data.Constraint
import Data.Proxy
import Data.Proxy.TH

class InstForall (c :: k -> Constraint) (f :: k -> k) where
    getInstance :: c a => Dict (c (f a))
    default getInstance :: (c a,c (f a)) => Dict (c (f a))
    getInstance = Dict

instance InstForall Show [] where

spec' :: (InstForall constr f,constr a) 
      => Proxy constr
      -> (Dict (constr (f a)) -> f a) -> f a
spec' Proxy f = f getInstance

specArg' :: (InstForall constr f,constr a) 
         => Proxy constr
         -> (Dict (constr (f a)) -> f a -> r) 
         -> f a -> r
specArg' Proxy f = f getInstance

specRes :: (InstForall constr f,constr a) 
        => Proxy constr
        -> (constr (f a) => f a) -> f a
specRes p f = spec' p (\Dict -> f)

specArg :: (InstForall constr f,constr a) 
        => Proxy constr
        -> (constr (f a) => f a -> r) -> f a -> r
specArg p f = specArg' p (\Dict -> f)

show1' :: (InstForall Show f,Show a)
       => f a -> String
show1' = specArg [pr|Show|] show

compare1' :: (InstForall Ord f,Ord a)
          => f a -> f a -> Ordering
compare1' = specArg [pr|Ord|] compare

sameTypeArg :: f a -> g a -> g a
sameTypeArg _ = id

useInst :: (constr a, InstForall constr f)
        => Proxy (constr (f a)) -> (constr (f a) => r) -> r
useInst p f = case sameTypeArg p getInstance of
                  Dict -> f
