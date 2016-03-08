{-# LANGUAGE KindSignatures,TypeFamilies #-}
module Data.Map.Class 
    ( M.Map
    , module Data.Map.Class 
    , (P.!) )
where

import Control.Lens
import Control.Precondition as P

import qualified Data.Map as M
import qualified Data.Set as S

import GHC.Exts (Constraint)

class IsMap (map :: * -> * -> *) where
    type IsKey map k :: Constraint
    empty :: map k a
    singleton :: IsKey map k => k -> a -> map k a
    null :: map k a -> Bool
    size :: map k a -> Int
    isSubmapOf :: (Eq k,IsKey map k,Eq a) => map k a -> map k a -> Bool
    isSubmapOfBy :: (Eq k,IsKey map k) 
                 => (a -> b -> Bool)
                 -> map k a -> map k b -> Bool
    isProperSubmapOf :: (Eq k,IsKey map k,Eq a) => map k a -> map k a -> Bool
        -- Map
    map :: (a -> b) -> map k a -> map k b
    mapMaybe :: (a -> Maybe b) -> map k a -> map k b
    mapMaybeWithKey :: (k -> a -> Maybe b) -> map k a -> map k b
    mapWithKey :: (k -> a -> b) -> map k a -> map k b
    mapEither :: (a -> Either b c) -> map k a -> (map k b, map k c)
    mapEitherWithKey :: (k -> a -> Either b c) -> map k a -> (map k b, map k c)
    traverseWithKey :: Applicative f => (k -> a -> f b) -> map k a -> f (map k b)
    foldMapWithKey :: Monoid map' => (k -> a -> map') -> map k a -> map'
    mapKeys :: IsKey map k1 => (k0 -> k1) -> map k0 a -> map k1 a
    mapKeysWith :: IsKey map k1 
                => (a -> a -> a)
                -> (k0 -> k1) 
                -> map k0 a -> map k1 a
    mapKeysMonotonic :: IsKey map k1 => (k0 -> k1) -> map k0 a -> map k1 a
        -- change by one
    delete :: IsKey map k => k -> map k a -> map k a
    insert :: IsKey map k => k -> a -> map k a -> map k a
    adjustWithKey :: IsKey map k => (k -> a -> a) -> k -> map k a -> map k a
        -- lookup
    member :: IsKey map k => k -> map k a -> Bool
    lookup :: IsKey map k => k -> map k a -> Maybe a
    findWithDefault :: IsKey map k => a -> k -> map k a -> a
    elemAt :: Ord k => Int -> map k a -> (k,a)
        -- filtering
    filter :: (a -> Bool) -> map k a -> map k a
    filterWithKey :: (k -> a -> Bool) -> map k a -> map k a
    partitionWithKey :: (k -> a -> Bool) -> map k a -> (map k a,map k a)
    split :: Ord k => k -> map k a -> (map k a, map k a)
        -- Combination
    union :: IsKey map k => map k a -> map k a -> map k a
    unions :: IsKey map k => [map k a] -> map k a
    unionsWith :: IsKey map k => (a -> a -> a) -> [map k a] -> map k a
    unionWith :: IsKey map k => (a -> a -> a) -> map k a -> map k a -> map k a
    unionWithKey :: IsKey map k => (k -> a -> a -> a) -> map k a -> map k a -> map k a
    intersection :: IsKey map k => map k a -> map k b -> map k a
    intersectionWith :: IsKey map k => (a -> b -> c) -> map k a -> map k b -> map k c
    intersectionWithKey :: IsKey map k => (k -> a -> b -> c) -> map k a -> map k b -> map k c
    difference :: IsKey map k => map k a -> map k b -> map k a
    differenceWith :: IsKey map k => (a -> b -> Maybe a) -> map k a -> map k b -> map k a
        -- lists
    keys :: map k a -> [k]
    keysSet :: Ord k => map k a -> S.Set k
    ascKeys :: Ord k => map k a -> [k]
    ascKeys = S.toAscList . keysSet
    elems :: Ord k => map k a -> [a]
    ascElems :: Ord k => map k a -> [a]
    toList :: Ord k => map k a -> [(k,a)]
    toAscList :: Ord k => map k a -> [(k,a)]
    toListIntl :: map k a -> (Order,[(k,a)])
    fromSet :: IsKey map k => (k -> a) -> S.Set k -> map k a
    fromList :: IsKey map k => [(k,a)] -> map k a
    fromListWith :: IsKey map k => (a -> a -> a) -> [(k,a)] -> map k a
    fromListWithKey :: IsKey map k => (k -> a -> a -> a) -> [(k,a)] -> map k a
    fromListIntl :: IsKey map k => (Order,[(k,a)]) -> map k a

data Order = Ordered | Unordered

{-# INLINE (\\) #-}
(\\) :: (IsMap map,IsKey map k) => map k a -> map k b -> map k a
(\\) = difference

{-# INLINE notMember #-}
notMember :: (IsMap map,IsKey map k) => k -> map k a -> Bool
notMember x m = not $ member x m

{-# INLINE convertMap #-}
convertMap :: (IsMap m0,IsMap m1,IsKey m1 k) => m0 k a -> m1 k a
convertMap = fromListIntl . toListIntl

instance IsMap M.Map where
    type IsKey M.Map k = Ord k
    {-# INLINE null #-}
    null = M.null
    {-# INLINE empty #-}
    empty = M.empty
    {-# INLINE singleton #-}
    singleton = M.singleton
    {-# INLINE size #-}
    size = M.size
    {-# INLINE isSubmapOf #-}
    isSubmapOf = M.isSubmapOf
    {-# INLINE isSubmapOfBy #-}
    isSubmapOfBy = M.isSubmapOfBy
    {-# INLINE isProperSubmapOf #-}
    isProperSubmapOf = M.isProperSubmapOf
        -- Map
    {-# INLINE map #-}
    map = M.map
    {-# INLINE mapMaybe #-}
    mapMaybe = M.mapMaybe
    mapMaybeWithKey = M.mapMaybeWithKey
    {-# INLINE mapEither #-}
    mapEither = M.mapEither
    {-# INLINE mapEitherWithKey #-}
    mapEitherWithKey = M.mapEitherWithKey
    {-# INLINE mapWithKey #-}
    mapWithKey = M.mapWithKey
    {-# INLINE traverseWithKey #-}
    traverseWithKey = M.traverseWithKey
    {-# INLINE foldMapWithKey #-}
    foldMapWithKey = M.foldMapWithKey
    {-# INLINE mapKeys #-}
    mapKeys = M.mapKeys
    {-# INLINE mapKeysWith #-}
    mapKeysWith = M.mapKeysWith
    {-# INLINE mapKeysMonotonic #-}
    mapKeysMonotonic = M.mapKeysMonotonic
        -- change by one
    {-# INLINE insert #-}
    insert = M.insert
    {-# INLINE delete #-}
    delete = M.delete
    {-# INLINE adjustWithKey #-}
    adjustWithKey = M.adjustWithKey
        -- lookup
    {-# INLINE elemAt #-}
    elemAt = M.elemAt
    {-# INLINE member #-}
    member = M.member
    {-# INLINE lookup #-}
    lookup = M.lookup
    {-# INLINE findWithDefault #-}
    findWithDefault = M.findWithDefault
        -- filtering
    {-# INLINE filter #-}
    filter = M.filter
    {-# INLINE filterWithKey #-}
    filterWithKey = M.filterWithKey
    {-# INLINE partitionWithKey #-}
    partitionWithKey = M.partitionWithKey
    {-# INLINE split #-}
    split = M.split
        -- Combination
    {-# INLINE union #-}
    union = M.union
    {-# INLINE unions #-}
    unions = M.unions
    {-# INLINE unionsWith #-}
    unionsWith = M.unionsWith
    {-# INLINE unionWith #-}
    unionWith = M.unionWith
    {-# INLINE unionWithKey #-}
    unionWithKey = M.unionWithKey
    {-# INLINE intersection #-}
    intersection x y = M.intersection x y
    {-# INLINE intersectionWith #-}
    intersectionWith = M.intersectionWith
    {-# INLINE intersectionWithKey #-}
    intersectionWithKey = M.intersectionWithKey
    {-# INLINE difference #-}
    difference = M.difference
    {-# INLINE differenceWith #-}
    differenceWith = M.differenceWith
        -- lists
    {-# INLINE elems #-}
    elems = M.elems
    {-# INLINE ascElems #-}
    ascElems = M.elems
    {-# INLINE keys #-}
    keys = M.keys
    {-# INLINE keysSet #-}
    keysSet = M.keysSet
    {-# INLINE toList #-}
    toList = M.toList
    {-# INLINE toAscList #-}
    toAscList = M.toAscList
    {-# INLINE toListIntl #-}
    toListIntl = (Ordered,) . M.toList
    {-# INLINE fromSet #-}
    fromSet = M.fromSet
    {-# INLINE fromList #-}
    fromList = M.fromList
    {-# INLINE fromListIntl #-}
    fromListIntl (Ordered,xs)   = M.fromAscList xs
    fromListIntl (Unordered,xs) = M.fromList xs
    {-# INLINE fromListWith #-}
    fromListWith = M.fromListWith
    {-# INLINE fromListWithKey #-}
    fromListWithKey = M.fromListWithKey

{-# INLINE asList #-}
asList :: (IsMap m,IsKey m k1) => Iso (m k0 a0) (m k1 a1) [(k0,a0)] [(k1,a1)]
asList = asListWith const

{-# INLINE asListWith #-}
asListWith :: (IsMap m,IsKey m k1) 
           => (a1 -> a1 -> a1)
           -> Iso (m k0 a0) (m k1 a1) [(k0,a0)] [(k1,a1)]
asListWith f = iso (snd . toListIntl) (fromListWith f)
