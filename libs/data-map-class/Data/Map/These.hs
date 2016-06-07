module Data.Map.These 
  ( module Data.Map.These 
  , module Data.These )
where

-- import Data.Map as M
import Data.Map.Class as M
import Data.These

mapOnUnion :: Ord k 
           => (These a b -> c)
           -> Map k a
           -> Map k b
           -> Map k c
mapOnUnion f = mapOnUnionWithKey (const f)

mapOnUnion' :: Ord k 
            => (Either a (Maybe a,b) -> c)
            -> Map k a
            -> Map k b
            -> Map k c
mapOnUnion' f = mapOnUnionWithKey' (const f)

mapOnUnionWithKey :: Ord k 
                  => (k -> These a b -> c)
                  -> Map k a
                  -> Map k b
                  -> Map k c
mapOnUnionWithKey f m0 m1 = M.unions [left,middle,right]
    where
        left   = M.mapWithKey (\k -> f k.This) (m0 `M.difference` m1)
        right  = M.mapWithKey (\k -> f k.That) (m1 `M.difference` m0)
        middle = M.intersectionWithKey (\k x y -> f k $ These x y) m0 m1

mapOnUnionWithKey' :: Ord k 
                   => (k -> Either a (Maybe a,b) -> c)
                   -> Map k a
                   -> Map k b
                   -> Map k c
mapOnUnionWithKey' f = mapOnUnionWithKey ((.onRight) . f)

onRight :: These a b -> Either a (Maybe a,b)
onRight (These x y) = Right (Just x,y)
onRight (That y)    = Right (Nothing,y)
onRight (This x)    = Left x
