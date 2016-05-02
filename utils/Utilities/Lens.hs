module Utilities.Lens where

import Control.Lens
import Control.Monad.State

import Data.Default
import Data.Either.Validation
import Data.Foldable as F
import Data.Map.Class as M
import Data.Semigroup
import Data.Tuple


{-# INLINE withKey #-}
withKey :: IsMap map => Iso (map a b) (map c d) (map a (a,b)) (map c d)
withKey = iso (M.mapWithKey (,)) id

{-# INLINE withKey' #-}
withKey' :: IsMap map => Getter (map a b) (map a (a,b))
withKey' = to (M.mapWithKey (,))

firstL :: LensLike f s t a b -> LensLike f (s,k) t (a,k) b
firstL ln f x = ln (\y -> f $ x & _1 .~ y) (fst x)

swapped :: Iso (a,b) (c,d) (b,a) (d,c)
swapped = iso swap swap

filterL :: (a -> Bool) -> Traversal' a a
filterL p f x
    | p x       = f x
    | otherwise = pure x

secondL :: LensLike f s t a b -> LensLike f (k,s) t (k,a) b
secondL ln f x = ln (\y -> f $ x & _2 .~ y) (snd x)

create :: Default a => State a b -> a
create cmd = execState cmd def

combine :: Lens' b a -> (a -> a -> a) -> b -> b -> b -> b
combine ln f x y z = z & ln .~ f (x^.ln) (y^.ln)

combine' :: Lens' b a -> (a -> a -> a) -> b -> b -> State b ()
combine' ln f x y = modify $ combine ln f x y

combineAll :: (Foldable f, Functor f, Default a) 
           => Lens' b a -> (a -> a -> a) -> f b -> b -> b
combineAll ln f xs = set ln $ F.foldl f def $ view ln <$> xs

combineAll' :: (Foldable f, Functor f, Default a) 
            => Lens' b a -> (a -> a -> a) -> f b -> State b ()
combineAll' ln f xs = modify $ combineAll ln f xs

onBoth :: Applicative f
       => (a0 -> f a1)
       -> (b0 -> f b1)
       -> (a0,b0)
       -> f (a1,b1)
onBoth f g (x,y) = (,) <$> f x <*> g y

traverseValidation :: (Traversable t,Semigroup e)
                   => (a -> Either e b) 
                   -> t a -> Either e (t b)
traverseValidation f = validationToEither . traverse (eitherToValidation . f)

unzipped :: Iso [(a,b)] [(c,d)] ([a],[b]) ([c],[d])
unzipped = iso unzip (uncurry zip)
