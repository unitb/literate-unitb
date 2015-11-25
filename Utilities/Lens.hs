module Utilities.Lens where

import Control.Lens
import Control.Monad.State

import Data.Default
import Data.Foldable as F
import Data.Map as M
import Data.Tuple

withKey :: Iso (Map a b) (Map c d) (Map a (a,b)) (Map c d)
withKey = iso (M.mapWithKey (,)) id

withKey' :: Getter (Map a b) (Map a (a,b))
withKey' = to (M.mapWithKey (,))

firstL :: LensLike f s t a b -> LensLike f (s,k) t (a,k) b
firstL ln f x = ln (\y -> f $ x & _1 .~ y) (fst x)

isoSwap :: Iso' (a,b) (b,a)
isoSwap = iso swap swap

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
