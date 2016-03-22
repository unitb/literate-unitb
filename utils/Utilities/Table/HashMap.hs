{-# LANGUAGE CPP, TypeFamilies #-}
module Utilities.Table.HashMap
    ( module Utilities.Table.HashMap 
    , M.HashMap ) 
where

import Control.Arrow
import Control.Lens

import Data.Default
import Data.Either.Combinators
import Data.Function
import Data.Hashable
import Data.List as L
import Data.Map.Class as Map
import Data.Maybe
--import Data.Monoid
import Data.Semigroup
import Data.Serialize
import qualified Data.Set as S

#ifdef __HASH_MAP_LAZY__
import qualified Data.HashMap.Lazy as M
#else
import qualified Data.HashMap.Strict as M
#endif

import GHC.Generics.Instances

instance IsMap M.HashMap where
    type IsKey M.HashMap k = (Ord k,Hashable k)
    {-# INLINE null #-}
    null = M.null
    {-# INLINE empty #-}
    empty = M.empty
    {-# INLINE singleton #-}
    singleton = M.singleton
    {-# INLINE size #-}
    size = M.size
    {-# INLINE isSubmapOf #-}
    isSubmapOf = isSubmapOfBy (==)
    isSubmapOfBy eq x y  = M.size (M.filter id $ M.intersectionWith eq x y) == M.size x
    isProperSubmapOf x y = M.size x < M.size y && isSubmapOf x y
        -- Map
    {-# INLINE map #-}
    map = M.map
    {-# INLINE mapMaybe #-}
    mapMaybe f = M.map fromJust . M.filter isJust . M.map f
    {-# INLINE mapMaybeWithKey #-}
    mapMaybeWithKey f = M.map fromJust . M.filter isJust . M.mapWithKey f
    {-# INLINE mapEither #-}
    mapEither f = mapEitherWithKey (const f)
    mapEitherWithKey f m = (Map.mapMaybe leftToMaybe m',Map.mapMaybe rightToMaybe m')
        where
            m' = M.mapWithKey f m
    {-# INLINE mapWithKey #-}
    mapWithKey = M.mapWithKey
    {-# INLINE traverseWithKey #-}
    traverseWithKey = M.traverseWithKey
    {-# INLINE foldMapWithKey #-}
    foldMapWithKey f = M.foldlWithKey' (\m k x -> m `mappend` f k x) mempty
    {-# INLINE mapKeys #-}
    mapKeys f = asList.traverse._1 %~ f
    {-# INLINE mapKeysWith #-}
    mapKeysWith f g = asListWith f.traverse._1 %~ g
    {-# INLINE mapKeysMonotonic #-}
    mapKeysMonotonic = mapKeys
        -- change by one
    {-# INLINE insert #-}
    insert = M.insert
    {-# INLINE delete #-}
    delete = M.delete
    {-# INLINE adjustWithKey #-}
    adjustWithKey f k = M.adjust (f k) k
        -- lookup
    {-# INLINE elemAt #-}
    elemAt i = (!!i) . toAscList
    {-# INLINE member #-}
    member = M.member
    {-# INLINE lookup #-}
    lookup = M.lookup
    {-# INLINE findWithDefault #-}
    findWithDefault = M.lookupDefault
        -- filtering
    {-# INLINE filter #-}
    filter = M.filter
    {-# INLINE filterWithKey #-}
    filterWithKey = M.filterWithKey
    partitionWithKey f = mapEitherWithKey f'
        where f' k x | f k x     = Left x
                     | otherwise = Right x
    {-# INLINE split #-}
    split k = partitionWithKey (\k' _ -> k' < k) . M.filterWithKey (const . (k /=))
        -- Combination
    {-# INLINE union #-}
    union = M.union
    {-# INLINE unions #-}
    unions = M.unions
    {-# INLINE unionsWith #-}
    unionsWith f = L.foldl' (M.unionWith f) M.empty
    {-# INLINE unionWith #-}
    unionWith = M.unionWith
    unionWithKey f x y = snd <$> unionWith (\(k,x) (_,y) -> (k,f k x y)) (M.mapWithKey (,) x) (M.mapWithKey (,) y)
    {-# INLINE intersection #-}
    intersection = M.intersection
    {-# INLINE intersectionWith #-}
    intersectionWith = M.intersectionWith
    {-# INLINE intersectionWithKey #-}
    intersectionWithKey f = M.intersectionWith (uncurry f) . M.mapWithKey (,)
    {-# INLINE difference #-}
    difference = M.difference
    {-# INLINE differenceWith #-}
    differenceWith f x y = M.difference x y `M.union` Map.mapMaybe id (M.intersectionWith f x y)
        -- lists
    {-# INLINE elems #-}
    elems = M.elems
    {-# INLINE ascElems #-}
    ascElems = M.elems
    {-# INLINE keys #-}
    keys = M.keys
    {-# INLINE keysSet #-}
    keysSet = S.fromList . M.keys
    {-# INLINE toList #-}
    toList = M.toList
    {-# INLINE toAscList #-}
    toAscList = sortOn fst . M.toList
    {-# INLINE toListIntl #-}
    toListIntl = (Ordered,) . M.toList
    {-# INLINE fromSet #-}
    fromSet f = M.fromList . L.map (id &&& f) . S.toList
    {-# INLINE fromList #-}
    fromList = M.fromList
    {-# INLINE fromListIntl #-}
    fromListIntl (_,xs) = M.fromList xs
    {-# INLINE fromListWith #-}
    fromListWith = M.fromListWith
    {-# INLINE fromListWithKey #-}
    fromListWithKey f = M.map snd . M.fromListWith (\(k,x) (_,y) -> (k,f k x y)) . L.map (fst &&& id)

tableToList :: M.HashMap k a -> [(k, a)]
tableToList = M.toList

tableElems :: M.HashMap k a -> [a]
tableElems = M.elems

instance Default (M.HashMap k a) where
    def = M.empty

instance (Ord k,Hashable k) => Semigroup (Intersection (M.HashMap k a)) where
    Intersection x <> Intersection y = Intersection $ x `intersection` y

instance (Ord k,Ord a) => Ord (M.HashMap k a) where
    compare = compare `on` toList

instance (Eq k,Hashable k,Serialize k,Serialize a) => Serialize (M.HashMap k a) where
    get = M.fromList <$> get
    put = put . M.toList
