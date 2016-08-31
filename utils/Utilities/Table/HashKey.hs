{-# LANGUAGE TypeFamilies #-}
module Utilities.Table.HashKey where

import Control.Arrow
import Control.DeepSeq
import Control.Lens
import Control.Monad
import Control.Precondition ((!))

import Data.Default
import Data.Function
import Data.Hashable

import qualified Data.Map as M
import qualified Data.List as L
import qualified Data.List.Ordered as Ord
import Data.Map.Class
import Data.Semigroup
import Data.Serialize
import qualified Data.Set as S

import GHC.Generics.Instances

import Prelude hiding (lookup,null,map,filter)

newtype MapWithHash k a = MapWithHash { _mapWithHash :: M.Map (HashKey k) a }
    deriving (Eq,Ord,Generic,Functor,Foldable,Traversable,Default,Monoid)

data HashKey k = HashKey !Int !k
    deriving (Eq,Ord,Generic)

type instance Index (MapWithHash a b) = a
type instance IxValue (MapWithHash a b) = b

makeLenses ''MapWithHash

key :: HashKey k -> k
key (HashKey _ k) = k

key' :: Hashable k1 => Iso (HashKey k0) (HashKey k1) k0 k1
key' = iso key (\k -> HashKey (hash k) k)

instance (Ord a,Hashable a) => At (MapWithHash a b) where
    at i = mapWithHash.at (i^.from key')

instance (Ord a,Hashable a) => Ixed (MapWithHash a b) where
    ix i = at i.traverse

instance (Show a,Show b,Ord a) => Show (MapWithHash a b) where
    show m = "fromList " ++ show (toList m)

instance (NFData a,NFData b) => NFData (MapWithHash a b) where
instance (NFData k) => NFData (HashKey k) where

{-# INLINE on2 #-}
on2 :: (forall a0 a1. Iso (m0 a0) (m0 a1) (m1 a0) (m1 a1))
    -> (m1 a0 -> m1 a1 -> m1 a2)
    -> (m0 a0 -> m0 a1 -> m0 a2)
on2 ln f x y = f (x^.ln) (y^.ln)^.from ln

{-# INLINE onList #-}
onList :: (forall a0 a1. Iso (m0 a0) (m0 a1) (m1 a0) (m1 a1))
       -> ([m1 a0] -> m1 a1)
       -> ([m0 a0] -> m0 a1)
onList ln f xs = f (xs & traverse %~ view ln)^.from ln

instance (Hashable k,Ord k) => Semigroup (Intersection (MapWithHash k a)) where
    Intersection x <> Intersection y = Intersection $ x `intersection` y

{-# INLINE onPair #-}
onPair :: (forall a . Iso' (map0 a) (map1 a))
       -> (map1 a -> (map1 b,map1 c))
       -> (map0 a -> (map0 b,map0 c))
onPair ln f = (view (from ln) *** view (from ln)) . f . view ln

instance IsMap MapWithHash where
    type IsKey MapWithHash k = (Ord k, Hashable k)
    {-# INLINE null #-}
    null  = null . view mapWithHash
    {-# INLINE empty #-}
    empty = MapWithHash empty
    {-# INLINE singleton #-}
    singleton k x = MapWithHash $ singleton (HashKey (hash k) k) x
    {-# INLINE size #-}
    size = size . view mapWithHash
    {-# INLINE isSubmapOf #-}
    isSubmapOf = isSubmapOfBy (==)
    {-# INLINE isSubmapOfBy #-}
    isSubmapOfBy f (MapWithHash x) (MapWithHash y) = isSubmapOfBy f x y
    {-# INLINE isProperSubmapOf #-}
    isProperSubmapOf (MapWithHash x) (MapWithHash y) = isProperSubmapOf x y
        -- Map
    {-# INLINE map #-}
    map f = mapWithHash %~ map f
    {-# INLINE mapMaybe #-}
    mapMaybe f = mapWithHash %~ mapMaybe f
    {-# INLINE mapMaybeWithKey #-}
    mapMaybeWithKey f = mapWithHash %~ mapMaybeWithKey (f . key)
    {-# INLINE mapEither #-}
    mapEither f = mapEitherWithKey (const f)
    {-# INLINE mapEitherWithKey #-}
    mapEitherWithKey f = (MapWithHash *** MapWithHash) . mapEitherWithKey (f . key) . view mapWithHash
    {-# INLINE mapWithKey #-}
    mapWithKey f = mapWithHash %~ mapWithKey (f . key)
    {-# INLINE traverseWithKey #-}
    traverseWithKey f = mapWithHash (traverseWithKey $ f . key)
    {-# INLINE foldMapWithKey #-}
    foldMapWithKey f = foldMapWithKey (f . key) . view mapWithHash
    {-# INLINE mapKeys #-}
    mapKeys f = mapWithHash %~ mapKeys (key' %~ f)
    {-# INLINE mapKeysWith #-}
    mapKeysWith f g = mapWithHash %~ mapKeysWith f (key' %~ g)
    {-# INLINE mapKeysMonotonic #-}
    mapKeysMonotonic f = mapWithHash %~ mapKeysMonotonic (key' %~ f)
        -- change by one
    {-# INLINE insert #-}
    insert k x = mapWithHash %~ insert (k^.from key') x
    {-# INLINE delete #-}
    delete k = mapWithHash %~ delete (k^.from key')
    {-# INLINE adjustWithKey #-}
    adjustWithKey f k = mapWithHash %~ adjustWithKey (f . key) (k^.from key')
        -- lookup
    {-# INLINE elemAt #-}
    elemAt i = (!i) . toAscList
    {-# INLINE lookup #-}
    lookup k = lookup (k^.from key') . view mapWithHash
    member k = member (k^.from key') . view mapWithHash
    {-# INLINE findWithDefault #-}
    findWithDefault x k = findWithDefault x (k^.from key') . view mapWithHash
        -- filtering
    {-# INLINE filter #-}
    filter f = mapWithHash %~ filter f
    {-# INLINE filterWithKey #-}
    filterWithKey f = mapWithHash %~ filterWithKey (f . key)
    partition = partitionWithKey . const
    {-# INLINE partitionWithKey #-}
    partitionWithKey f = onPair mapWithHash $
            partitionWithKey (f . key)
    {-# INLINE split #-}
    split k = partitionWithKey (\k' _ -> k' < k) . filterWithKey (const . (k /=))
        -- Combination
    {-# INLINE union #-}
    union = on2 mapWithHash union
    {-# INLINE unionWith #-}
    unionWith f = on2 mapWithHash $ unionWith f
    {-# INLINE unionWithKey #-}
    unionWithKey f = on2 mapWithHash $ unionWithKey (f . key)
    {-# INLINE unions #-}
    unions = onList mapWithHash unions
    {-# INLINE unionsWith #-}
    unionsWith f = onList mapWithHash $ unionsWith f
    {-# INLINE intersection #-}
    intersection = on2 mapWithHash intersection
    {-# INLINE intersectionWith #-}
    intersectionWith f = on2 mapWithHash $ intersectionWith f
    {-# INLINE intersectionWithKey #-}
    intersectionWithKey f = on2 mapWithHash $ intersectionWithKey (f . key)
    {-# INLINE difference #-}
    difference = on2 mapWithHash difference
    {-# INLINE differenceWith #-}
    differenceWith f = on2 mapWithHash $ differenceWith f
        -- lists
    --keys  = L.map key . keys . view mapWithHash
    keys  = L.map key . keys . view mapWithHash
    keysSet  = S.map key . keysSet . view mapWithHash
    elems = elems . view mapWithHash
    --elems = ascElems
    ascElems = L.map snd . toAscList
    toList = toAscList
    --toList = _
    toAscList = Ord.sortOn fst . (traverse._1 %~ key) . toList . view mapWithHash
    toListIntl = (Unordered,) . (traverse._1 %~ key) . M.toList . view mapWithHash
    fromSet f = MapWithHash . M.fromSet (f . key) . S.map (view $ from key')
    fromList = MapWithHash . fromList . convertKeys
    fromListIntl (_,xs) = fromList xs
    fromListWith f    = MapWithHash . fromListWith f . convertKeys
    fromListWithKey f = MapWithHash . fromListWithKey (f . key) . convertKeys
    tableToList = (traverse._1 %~ key) . M.toList . view mapWithHash
    tableElems = M.elems . view mapWithHash

convertKeys :: Hashable k => [(k,a)] -> [(HashKey k,a)]
convertKeys = traverse._1 %~ view (from key')

instance Serialize a => Serialize (HashKey a) where
instance (Ord a,Serialize a, Serialize b) => Serialize (MapWithHash a b) where

