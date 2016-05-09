{-# LANGUAGE TypeFamilies, ScopedTypeVariables #-}
module Utilities.Table.BucketTable where

import Control.Arrow
import Control.DeepSeq
import Control.Lens
import Control.Monad
import Control.Precondition ((!))

import Data.Default
import Data.Function
import Data.Hashable
import qualified Data.Map as IM
import qualified Data.Map as M
import qualified Data.Maybe as My
import qualified Data.List as L
import Data.Map.Class
import Data.Semigroup
import Data.Serialize
import qualified Data.Set as S

import GHC.Generics.Instances

import Prelude hiding (lookup,null,map,filter)


import Test.QuickCheck hiding (shrinkList)
import Test.QuickCheck.Function

--data Table a b = Table (UArray Int Int) (Array Int (Map a b))
--type Table = M.Map
    --Table { _table :: Map a b }
    --deriving (Eq,Ord,Generic,Functor,Foldable,Traversable,Default,Monoid)

--type Bucket = OrderedBucket
--type Bucket = UnorderedBucket
type Bucket = M.Map

newtype HashTable a b = HashTable { _hashTable :: M.Map Int (Bucket a b) }
    deriving (Eq,Ord,Generic,Functor,Foldable,Traversable,Default,Monoid)

newtype OrderedBucket a b = OrderedBucket { _orderedBucket :: [(a,b)] }
    deriving (Eq,Ord,Generic,Functor,Foldable,Traversable,Default,Monoid)

newtype UnorderedBucket a b = UnorderedBucket { _unorderedBucket :: [(a,b)] }
    deriving (Eq,Ord,Generic,Functor,Foldable,Traversable,Default,Monoid)

type instance Index (HashTable a b) = a
type instance IxValue (HashTable a b) = b
type instance Index (OrderedBucket a b) = a
type instance IxValue (OrderedBucket a b) = b
type instance Index (UnorderedBucket a b) = a
type instance IxValue (UnorderedBucket a b) = b

--makeLenses ''Table
makeLenses ''HashTable
makeLenses ''OrderedBucket
makeLenses ''UnorderedBucket

--{-# INLINE bucket #-}
--bucket :: Ord k1 => Iso (Bucket k0 a0) (Bucket k1 a1) [(k0,a0)] [(k1,a1)]
--bucket = iso M.toList M.fromList

--{-# INLINE unbucket #-}
--unbucket :: Ord k0 => Iso [(k0,a0)] [(k1,a1)] (Bucket k0 a0) (Bucket k1 a1)
--unbucket = from bucket

instance (Ord a,Hashable a) => At (HashTable a b) where
    at i = hashTable.at (hash i).notNull'.at i

instance (Ord a,Hashable a) => Ixed (HashTable a b) where
    ix i = at i.traverse

instance (Ord a) => At (OrderedBucket a b) where
    at i = orderedBucket.lens (L.lookup i) (\xs r -> insertMaybe i r $ L.filter ((i /=) . fst) xs)

insertMaybe :: Ord k => k -> Maybe a -> [(k,a)] -> [(k,a)]
insertMaybe k = maybe id (L.insertBy (compare `on` fst) . (k,))

instance (Ord a) => Ixed (OrderedBucket a b) where
    ix i = at i.traverse

instance (Ord a) => At (UnorderedBucket a b) where
    at i = unorderedBucket.lens (L.lookup i) (\xs r -> maybe id ((:) . (i,)) r $ L.filter ((i /=) . fst) xs)

instance (Ord a) => Ixed (UnorderedBucket a b) where
    ix i = at i.traverse

instance (Show a,Show b,Ord a) => Show (HashTable a b) where
    show m = "fromList " ++ show (toList m)

instance (NFData a,NFData b) => NFData (HashTable a b) where
instance (NFData a,NFData b) => NFData (OrderedBucket a b) where
instance (NFData a,NFData b) => NFData (UnorderedBucket a b) where

instance (Serialize a,Serialize b,Ord a) => Serialize (HashTable a b) where
instance (Serialize a,Serialize b,Ord a) => Serialize (OrderedBucket a b) where
instance (Serialize a,Serialize b,Ord a) => Serialize (UnorderedBucket a b) where


--instance IsMap Table where
--    type IsKey Table k = Ord k
--    null  = M.null . view table
--    empty = Table M.empty
--    singleton k x = Table $ M.singleton k x
--    size = M.size . view table
--    isSubmapOf x y = M.isSubmapOf (x^.table) (y^.table)
--    isSubmapOfBy f x y = M.isSubmapOfBy f (x^.table) (y^.table)
--    isProperSubmapOf x y = M.isProperSubmapOf (x^.table) (y^.table)
--        -- Map
--    map f = table %~ M.map f
--    mapMaybe f = table %~ M.mapMaybe f
--    mapEither f = mapEitherWithKey (const f)
--    mapEitherWithKey f = (Table *** Table) . M.mapEitherWithKey f . view table    
--    mapWithKey f = table %~ M.mapWithKey f
--    traverseWithKey f = table $ M.traverseWithKey f
--    foldMapWithKey f = M.foldMapWithKey f . view table
--    mapKeys f = table %~ M.mapKeys f
--    mapKeysWith f g = table %~ M.mapKeysWith f g
--    mapKeysMonotonic f = table %~ M.mapKeysMonotonic f
--        -- change by one
--    insert k x = table %~ M.insert k x
--    delete k = table %~ M.delete k
--    adjustWithKey f x = table %~ M.adjustWithKey f x
--        -- lookup
--    elemAt x = M.elemAt x . view table
--    lookup x = M.lookup x . view table
--    member x = M.member x . view table
--    findWithDefault x y = M.findWithDefault x y . view table
--        -- filtering
--    filter f = table %~ M.filter f
--    filterWithKey f = table %~ M.filterWithKey f
--    partitionWithKey f = (Table *** Table) . M.partitionWithKey f . view table
--    split k = (Table *** Table) . split k . view table
--        -- Combination
--    union = on2 table M.union
--    unionWith f = on2 table $ M.unionWith f
--    unionWithKey f = on2 table $ M.unionWithKey f
--    unions = onList table M.unions
--    unionsWith f = onList table $ M.unionsWith f
--    intersection = on2 table M.intersection
--    intersectionWith f = on2 table $ M.intersectionWith f
--    intersectionWithKey f = on2 table $ M.intersectionWithKey f
--    difference = on2 table M.difference
--    differenceWith f = on2 table $ M.differenceWith f
--        -- lists
--    keys  = M.keys . view table
--    keysSet  = M.keysSet . view table
--    elems = M.elems . view table
--    toList = M.toList . view table
--    toListIntl = (Ordered,) . M.toList . view table
--    fromSet f = Table . M.fromSet f
--    fromList = Table . M.fromList
--    fromListIntl (Ordered,xs)   = Table $ M.fromAscList xs
--    fromListIntl (Unordered,xs) = Table $ M.fromList xs
--    fromListWith f = Table . M.fromListWith f
--    fromListWithKey f = Table . M.fromListWithKey f

--instance Ord k => Semigroup (Intersection (Table k a)) where
--    Intersection x <> Intersection y = Intersection $ x `intersection` y

{-# SPECIALIZE notNull' :: Lens' (Maybe (Bucket k a)) (Bucket k a) #-}
{-# SPECIALIZE notNull' :: Lens' (Maybe (HashTable k a)) (HashTable k a) #-}
notNull' :: IsMap map => Lens' (Maybe (map k a)) (map k a)
notNull' = lens (My.fromMaybe empty) (const notNull)

{-# SPECIALIZE notNull :: Bucket a b -> Maybe (Bucket a b) #-}
{-# SPECIALIZE notNull :: HashTable a b -> Maybe (HashTable a b) #-}
notNull :: IsMap map => map a b -> Maybe (map a b)
notNull m | null m    = Nothing
          | otherwise = Just m

instance IsMap HashTable where
    type IsKey HashTable k = (Ord k,Hashable k)
    {-# INLINE null #-}
    null  = IM.null . view hashTable
    {-# INLINE empty #-}
    empty = HashTable IM.empty
    {-# INLINE singleton #-}
    singleton k x = HashTable $ IM.singleton (hash k) (singleton k x)
    -- {-# INLINE size #-}
    size = sum . IM.map size . view hashTable
    -- {-# INLINE isSubmapOf #-}
    isSubmapOf = isSubmapOfBy (==)
    -- {-# INLINE isSubmapOfBy #-}
    isSubmapOfBy f x y = IM.isSubmapOfBy (isSubmapOfBy f) (x^.hashTable) (y^.hashTable)
    -- {-# INLINE isProperSubmapOf #-}
    isProperSubmapOf x y = IM.isProperSubmapOfBy isProperSubmapOf (x^.hashTable) (y^.hashTable)
        -- Map
    -- {-# INLINE map #-}
    map f = hashTable %~ IM.map (map f)
    -- {-# INLINE mapMaybe #-}
    mapMaybe f = hashTable %~ IM.mapMaybe (notNull . mapMaybe f)
    mapMaybeWithKey f = hashTable %~ IM.mapMaybe (notNull . mapMaybeWithKey f)
    -- {-# INLINE mapEither #-}
    mapEither f = mapEitherWithKey (const f)
    -- {-# INLINE mapEitherWithKey #-}
    mapEitherWithKey f = (     HashTable . IM.mapMaybe (notNull . fst) 
                           &&& HashTable . IM.mapMaybe (notNull . snd)) 
                . IM.map (mapEitherWithKey f) . view hashTable
    -- {-# INLINE mapWithKey #-}
    mapWithKey f = hashTable %~ IM.map (mapWithKey f)
    -- {-# INLINE traverseWithKey #-}
    traverseWithKey f = hashTable $ traverse $ traverseWithKey f
    -- {-# INLINE foldMapWithKey #-}
    foldMapWithKey f = foldMap (foldMapWithKey f) . view hashTable
    -- {-# INLINE mapKeys #-}
    mapKeys f = asList.traverse._1 %~ f
    -- {-# INLINE mapKeysWith #-}
    mapKeysWith f g = asListWith f.traverse._1 %~ g
    -- {-# INLINE mapKeysMonotonic #-}
    mapKeysMonotonic = mapKeys
        -- change by one
    -- {-# INLINE insert #-}
    insert k x = hashTable %~ IM.insertWith union (hash k) (singleton k x)
    -- {-# INLINE delete #-}
    delete k = hashTable %~ IM.update (notNull . delete k) (hash k)
    -- {-# INLINE adjustWithKey #-}
    adjustWithKey f k = hashTable %~ IM.adjust (adjustWithKey f k) (hash k)
        -- lookup
    -- {-# INLINE elemAt #-}
    elemAt i = (!i) . toAscList
    -- {-# INLINE lookup #-}
    lookup k = lookup k <=< IM.lookup (hash k) . view hashTable
    member k = maybe False (member k) . IM.lookup (hash k) . view hashTable
    -- {-# INLINE findWithDefault #-}
    findWithDefault x k = My.fromMaybe x . lookup k
        -- filtering
    filter f = hashTable %~ IM.mapMaybe (notNull . filter f)
    filterWithKey f = hashTable %~ IM.mapMaybe (notNull . filterWithKey f)
    partitionWithKey f = mapEitherWithKey f'
        where f' k x | f k x     = Left x
                     | otherwise = Right x
    split k = partitionWithKey (\k' _ -> k' < k) . filterWithKey (const . (k /=))
        -- Combination
    union = unionWith const
    unionWith f = unionWithKey (const f)
    unionWithKey f (HashTable m0) (HashTable m1) = HashTable $ IM.unionWith (unionWithKey f) m0 m1
    unions = unionsWith const
    unionsWith f = HashTable . IM.unionsWith (unionWith f) . L.map (view hashTable)
    intersection = intersectionWith const
    intersectionWith f = intersectionWithKey (const f)
    intersectionWithKey f (HashTable m0) (HashTable m1) = HashTable $ IM.intersectionWith (intersectionWithKey f) m0 m1
    difference = differenceWith (\ _ _ -> Nothing)
    differenceWith f (HashTable m0) (HashTable m1) = 
            HashTable $ IM.differenceWith (fmap notNull <$> differenceWith f) m0 m1
        -- lists
    keys  = concat . IM.elems . IM.map keys . view hashTable
    keysSet  = S.unions . IM.elems . IM.map keysSet . view hashTable
    elems = ascElems
    ascElems = L.map snd . toAscList
    toList = toAscList
    --toList = concat . IM.elems . IM.map toList . view hashTable
    toAscList = toAscList . unions . IM.elems . view hashTable
    toListIntl = (Unordered,) . tableToList'
    fromSet f = fromList . L.map (id &&& f) . S.toList
    fromList = fromListWith const
    fromListIntl (_,xs) = fromList xs
    fromListWith f    = fromListWithKey (const f)
    fromListWithKey f xs = HashTable $ IM.map (fromListWithKey f) 
                                     $ IM.fromListWith (flip (++)) (L.map g xs)
                where g (k,x) = (hash k,[(k,x)])

prop_unionsWith_consistent :: forall k a. (Ord k,Eq a,Show k,Show a,Hashable k)
                           => Fun a (Fun a a) -> [[(k,a)]]
                           -> Property
prop_unionsWith_consistent f' xs = 
        M.toList (unionsWith f $ L.map fromList xs)
        === 
        toList (unionsWith f $ L.map fromList xs :: HashTable k a)
    where
        f = apply . apply f'

tableToList :: HashTable k a -> [(k,a)]
tableToList = tableToList'
--tableToList = (traverse._1 %~ key) . M.toList . view mapWithHash
--tableToList = M.toList

tableElems :: HashTable k a -> [a]
tableElems = tableElems'
--tableElems = M.elems . view mapWithHash
--tableElems = M.elems

tableToList' :: HashTable k a -> [(k,a)]
tableToList' = concat . IM.elems . IM.map M.toList . view hashTable

tableElems' :: HashTable k a -> [a]
tableElems' = concat . IM.elems . IM.map M.elems . view hashTable

_foo :: HashTable k a -> [a]
_foo = tableElems'

instance (Hashable k,Ord k) => Semigroup (Intersection (HashTable k a)) where
    Intersection x <> Intersection y = Intersection $ x `intersection` y

--shrinkList :: Traversal [a] [b] a (Maybe b)
--shrinkList f = fmap My.catMaybes . traverse f

--instance IsMap OrderedBucket where
--    type IsKey OrderedBucket k = Ord k
--    {-# INLINE null #-}
--    null  = L.null . view orderedBucket
--    {-# INLINE empty #-}
--    empty = OrderedBucket []
--    {-# INLINE singleton #-}
--    singleton k x = OrderedBucket [(k,x)]
--    -- {-# INLINE size #-}
--    size = L.length . view orderedBucket
--    -- {-# INLINE isSubmapOf #-}
--    isSubmapOf = isSubmapOfBy (==)
--    -- {-# INLINE isSubmapOfBy #-}
--    isSubmapOfBy f (OrderedBucket xs) (OrderedBucket ys) = subset f xs ys
--    -- {-# INLINE isProperSubmapOf #-}
--    isProperSubmapOf x y = isSubmapOf x y && nX < nY
--        where nX = size x ; nY = size y
--        -- Map
--    -- {-# INLINE map #-}
--    map f = orderedBucket.traverse._2 %~ f
--    -- {-# INLINE mapMaybe #-}
--    mapMaybe f = orderedBucket.shrinkList %~ _2 f
--    -- {-# INLINE mapEither #-}
--    mapEither f = _
--    -- {-# INLINE mapEitherWithKey #-}
--    mapEitherWithKey f = _
--    -- {-# INLINE mapWithKey #-}
--    mapWithKey f = _
--    -- {-# INLINE traverseWithKey #-}
--    traverseWithKey f = orderedBucket.traverse $ \(k,x) -> (k,) <$> f k x
--    -- {-# INLINE foldMapWithKey #-}
--    foldMapWithKey f = _
--    -- {-# INLINE mapKeys #-}
--    mapKeys f = asList.traverse._1 %~ f
--    -- {-# INLINE mapKeysWith #-}
--    mapKeysWith f g = asListWith f.traverse._1 %~ g
--    -- {-# INLINE mapKeysMonotonic #-}
--    mapKeysMonotonic f = orderedBucket.traverse._1 %~ f
--        -- change by one
--    -- {-# INLINE insert #-}
--    insert k x = _
--    -- {-# INLINE delete #-}
--    delete k = _
--    -- {-# INLINE adjustWithKey #-}
--    adjustWithKey f k = _
--        -- lookup
--    -- {-# INLINE elemAt #-}
--    elemAt i = _
--    -- {-# INLINE lookup #-}
--    lookup k = _
--    member k = _
--    -- {-# INLINE findWithDefault #-}
--    findWithDefault x k = _
--        -- filtering
--    filter f = _
--    filterWithKey f = _
--    partitionWithKey f = _
--    split k = _
--        -- Combination
--    union = _
--    unionWith f = _
--    unionWithKey f (HashTable m0) (HashTable m1) = _
--    unions = _
--    unionsWith f = _
--    intersection = _
--    intersectionWith f = _
--    intersectionWithKey f (HashTable m0) (HashTable m1) = _
--    difference = _
--    differenceWith f (HashTable m0) (HashTable m1) = _
--        -- lists
--    keys  = _
--    keysSet  = _
--    elems = _
--    ascElems = _
--    toList = _
--    --toList = _
--    toAscList = _
--    toListIntl = _
--    fromSet f = _
--    fromList = _
--    fromListIntl (_,xs) = _
--    fromListWith f    = _
--    fromListWithKey f xs = _

--subset :: (Ord k) 
--       => (a -> b -> Bool)
--       -> [(k,a)] -> [(k,b)] -> Bool
--subset _ [] _ = True
--subset _ _ [] = False
--subset eq xs'@((k0,x0):xs) ((k1,x1):ys) = 
--        case compare k0 k1 of
--            EQ -> x0 `eq` x1 && subset eq xs ys
--            LT -> False
--            GT -> subset eq xs' ys

--instance IsMap UnorderedBucket where
--    type IsKey UnorderedBucket k = Eq k
--    {-# INLINE null #-}
--    null  = _
--    {-# INLINE empty #-}
--    empty = _
--    {-# INLINE singleton #-}
--    singleton k x = _
--    -- {-# INLINE size #-}
--    size = _
--    -- {-# INLINE isSubmapOf #-}
--    isSubmapOf = _
--    -- {-# INLINE isSubmapOfBy #-}
--    isSubmapOfBy f x y = _
--    -- {-# INLINE isProperSubmapOf #-}
--    isProperSubmapOf x y = _
--        -- Map
--    -- {-# INLINE map #-}
--    map f = _
--    -- {-# INLINE mapMaybe #-}
--    mapMaybe f = _
--    -- {-# INLINE mapEither #-}
--    mapEither f = _
--    -- {-# INLINE mapEitherWithKey #-}
--    mapEitherWithKey f = _
--    -- {-# INLINE mapWithKey #-}
--    mapWithKey f = _
--    -- {-# INLINE traverseWithKey #-}
--    traverseWithKey f = _
--    -- {-# INLINE foldMapWithKey #-}
--    foldMapWithKey f = _
--    -- {-# INLINE mapKeys #-}
--    mapKeys f = _
--    -- {-# INLINE mapKeysWith #-}
--    mapKeysWith f g = _
--    -- {-# INLINE mapKeysMonotonic #-}
--    mapKeysMonotonic = _
--        -- change by one
--    -- {-# INLINE insert #-}
--    insert k x = _
--    -- {-# INLINE delete #-}
--    delete k = _
--    -- {-# INLINE adjustWithKey #-}
--    adjustWithKey f k = _
--        -- lookup
--    -- {-# INLINE elemAt #-}
--    elemAt i = _
--    -- {-# INLINE lookup #-}
--    lookup k = _
--    member k = _
--    -- {-# INLINE findWithDefault #-}
--    findWithDefault x k = _
--        -- filtering
--    filter f = _
--    filterWithKey f = _
--    partitionWithKey f = _
--        where f' k x | f k x     = _
--                     | otherwise = _
--    split k = _
--        -- Combination
--    union = _
--    unionWith f = _
--    unionWithKey f (HashTable m0) (HashTable m1) = _
--    unions = _
--    unionsWith f = _
--    intersection = _
--    intersectionWith f = _
--    intersectionWithKey f (HashTable m0) (HashTable m1) = _
--    difference = _
--    differenceWith f (HashTable m0) (HashTable m1) = _
--        -- lists
--    keys  = _
--    keysSet  = _
--    elems = _
--    ascElems = _
--    toList = _
--    --toList = _
--    toAscList = _
--    toListIntl = _
--    fromSet f = _
--    fromList = _
--    fromListIntl (_,xs) = _
--    fromListWith f    = _
--    fromListWithKey f xs = _
--                where g (k,x) = _

--hash# :: Hashable a => a -> Int#
--hash# x = h
--    where
--        !(I# h) = hash x

return []

run_spec :: IO Bool
run_spec = $quickCheckAll
