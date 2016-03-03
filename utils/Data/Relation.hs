{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE TypeOperators      #-}
module Data.Relation where

    -- Libraries
import Control.Arrow
import Control.DeepSeq
import Control.Monad

import Data.Default
import Data.List hiding (union,transpose,null)
import qualified Data.List.Ordered as LO
import Data.Monoid
import Data.Tuple
import Data.Maybe
import qualified Data.Set as S

import GHC.Generics

import Prelude hiding (null)

import Test.QuickCheck
import Test.QuickCheck.Function

import qualified Utilities.Map as M
import qualified Utilities.Permutation as Perm
import Utilities.Table

infixr 6 <|
infixr 6 <<|
infixl 7 |>
infixl 7 |>>
infix <->

newtype Relation a b = Rel (Table a (Table b ()))
    deriving (Eq,Default,Generic)

type (<->) a b = Relation a b

instance (Show a, Show b) => Show (Relation a b) where
    show r = "fromList " ++ show (toList r)

instance (Ord a,Hashable a,Ord b,Hashable b) 
        => Monoid (Relation a b) where
    mempty = empty
    mappend = union

toList :: Relation a b -> [(a,b)]
toList (Rel m) = [ (x,y) | (x,xs) <- snd $ M.toListIntl m, (y,()) <- snd $ M.toListIntl xs ]

fromList :: (M.IsKey Table a, M.IsKey Table b) => [(a,b)] -> Relation a b
fromList xs = Rel $ M.map M.fromList $ M.fromListWith (++) [ (x,[(y,())]) | (x,y) <- xs ]

fromListMap :: M.IsKey Table b => Table a [b] -> Relation a b
fromListMap m = Rel $ M.map (M.fromList . map pair) m
    where
        pair x = (x,())

empty :: Relation a b
empty = Rel M.empty

compose :: (M.IsKey Table a,M.IsKey Table b,M.IsKey Table c) 
        => Relation a b -> Relation b c -> Relation a c
compose (Rel r0) (Rel r1) = Rel $ cleanup $ M.map (M.unions . M.elems . (r1 `M.intersection`)) r0

cleanup :: Table k0 (Table k1 a) -> Table k0 (Table k1 a)
cleanup = M.filter (not . M.null)

union :: (M.IsKey Table a, M.IsKey Table b) => Relation a b -> Relation a b -> Relation a b
union (Rel r0) (Rel r1) = Rel $ M.unionWith M.union r0 r1

intersection :: (M.IsKey Table a, M.IsKey Table b) => Relation a b -> Relation a b -> Relation a b
intersection (Rel r0) (Rel r1) = Rel $ cleanup $ M.intersectionWith M.intersection r0 r1

difference :: (M.IsKey Table a, M.IsKey Table b) => Relation a b -> Relation a b -> Relation a b
difference (Rel r0) (Rel r1) = Rel $ M.differenceWith f r0 r1
    where
        f x y
                | M.null z  = Nothing
                | otherwise = Just z
            where
                z = x `M.difference` y

subset :: (M.IsKey Table a, M.IsKey Table b) => Relation a b -> Relation a b -> Bool
subset (Rel r0) (Rel r1) = M.isSubmapOfBy M.isSubmapOf r0 r1

irreflexive :: M.IsKey Table a => Relation a a -> Bool
irreflexive (Rel m) = M.null $ M.filterWithKey M.member m

transpose :: (M.IsKey Table a,M.IsKey Table b) => Relation a b -> Relation b a
transpose (Rel m) = Rel $ M.map M.fromList $ M.unionsWith (++) $ M.elems $ M.mapWithKey (\k x -> M.map (const [(k,())]) x) m

symmetric :: M.IsKey Table a => Relation a a -> Bool
symmetric r = r == transpose r

images :: (M.IsKey Table a,M.IsKey Table b) => Relation a b -> a -> S.Set b
images (Rel m) x = M.keysSet $ M.findWithDefault (M.empty) x m

transitive :: M.IsKey Table a => Relation a a -> Bool
transitive r = compose r r `subset` r

antisymmetric :: M.IsKey Table a => Relation a a -> Bool
antisymmetric r = null $ r `intersection` transpose r

null :: Relation a b -> Bool
null (Rel m) = M.null m

domain :: M.IsKey Table a => Relation a b -> S.Set a
domain (Rel m) = M.keysSet m

range :: M.IsKey Table b => Relation a b -> S.Set b
range (Rel m) = M.keysSet $ M.unions $ tableElems m

(!) :: (M.IsKey Table a, M.IsKey Table b) => Relation a b -> (a,b) -> Bool
(!) (Rel r) (x,y) = maybe False (y `M.member`) (x `M.lookup` r)

identity :: M.IsKey Table a => S.Set a -> Relation a a
identity s = Rel $ M.fromSet (`M.singleton` ()) s

(<|)  :: M.IsKey Table a 
      => S.Set a -> Relation a b -> Relation a b
(<<|) :: M.IsKey Table a 
      => S.Set a -> Relation a b -> Relation a b
(|>)  :: M.IsKey Table b 
      => Relation a b -> S.Set b -> Relation a b
(|>>) :: M.IsKey Table b 
      => Relation a b -> S.Set b -> Relation a b

(<|) = domRestr
(<<|) = domSubt
(|>) = ranRestr
(|>>) = ranSubt

domRestr :: M.IsKey Table a => S.Set a -> Relation a b -> Relation a b
domRestr s (Rel r) = Rel $ r `M.intersection` M.fromSet (const ()) s

domSubt :: M.IsKey Table a => S.Set a -> Relation a b -> Relation a b
domSubt s (Rel r) = Rel $ r `M.difference` M.fromSet (const ()) s

ranRestr :: M.IsKey Table b => Relation a b -> S.Set b -> Relation a b
ranRestr (Rel r) s = Rel $ M.mapMaybe f r
    where
        f m
                | M.null m' = Nothing
                | otherwise = Just m'
            where
                m' = m `M.intersection` M.fromSet (const ()) s

ranSubt :: M.IsKey Table b => Relation a b -> S.Set b -> Relation a b
ranSubt (Rel r) s = Rel $ M.mapMaybe f r
    where
        f m
                | M.null m' = Nothing
                | otherwise = Just m'
            where
                m' = m `M.difference` M.fromSet (const ()) s


mapDomain :: (M.IsKey Table c,M.IsKey Table b) => (a -> b) -> Relation a c -> Relation b c
mapDomain f (Rel m) = Rel $ M.mapKeysWith M.union f m

mapRange :: M.IsKey Table c => (b -> c) -> Relation a b -> Relation a c
mapRange f (Rel m) = Rel $ M.map (M.mapKeys f) m

bimap :: (M.IsKey Table c, M.IsKey Table d) => (a -> c) -> (b -> d) -> Relation a b -> Relation c d
bimap f g r = mapDomain f $ mapRange g r

filterDom :: (a -> Bool) -> Relation a b -> Relation a b
filterDom p (Rel m) = Rel $ M.filterWithKey (const . p) m

filterRan :: (b -> Bool) -> Relation a b -> Relation a b
filterRan p (Rel m) = Rel $ cleanup $ M.map (M.filterWithKey (const . p)) m

bimapMaybe :: (M.IsKey Table a1,M.IsKey Table b0,M.IsKey Table b1)
           => (a0 -> Maybe a1)
           -> (b0 -> Maybe b1)
           -> Relation a0 b0
           -> Relation a1 b1
bimapMaybe f g = mapMaybeRan g . mapMaybeDom f

mapMaybeDom :: (M.IsKey Table b,M.IsKey Table c) => (a -> Maybe c) -> Relation a b -> Relation c b
mapMaybeDom p (Rel m) = Rel $ M.fromListWith M.union $ mapMaybe p' $ tableToList m
    where
        p' (x,y) = p x >>= \x -> return (x,y)

mapMaybeRan :: M.IsKey Table c => (b -> Maybe c) -> Relation a b -> Relation a c
mapMaybeRan p (Rel m) = Rel $ cleanup $ M.map (M.fromList . mapMaybe p' . tableToList) m
    where
        p' (x,y) = p x >>= \x -> return (x,y)

instance (Ord a,Hashable a,Ord b,Hashable b,Arbitrary a,Arbitrary b) => Arbitrary (Relation a b) where
    arbitrary = fromList `liftM` arbitrary

instance (Ord a, Arbitrary a) => Arbitrary (S.Set a) where
    arbitrary = S.fromList `liftM` arbitrary

imp_invariant :: Relation a b -> Bool
imp_invariant (Rel r) = M.null (M.filter M.null r)

prop_toList_fromList :: (M.IsKey Table b, M.IsKey Table a) 
                     => [(a, b)] -> Bool
prop_toList_fromList xs = sort (toList $ fromList xs) == LO.nubSort xs

prop_fromList_toList :: (M.IsKey Table b, M.IsKey Table a) 
                     => Relation a b -> Bool
prop_fromList_toList r = fromList (toList r) == r

prop_domain_def :: M.IsKey Table a => Relation a b -> Bool
prop_domain_def r = domain r == S.fromList (map fst $ toList r)

prop_range_def :: M.IsKey Table b => Relation a b -> Bool
prop_range_def r = range r == S.fromList (map snd $ toList r)

prop_empty_def :: (Arbitrary b, Arbitrary a, Show b, Show a, M.IsKey Table b, M.IsKey Table a) 
               => a -> b -> Bool
prop_empty_def x y = not $ empty ! (x,y)

prop_apply_def :: (Arbitrary t1, Arbitrary t, Show t1, Show t, M.IsKey Table t1, M.IsKey Table t) 
               => Relation t t1 -> Property
prop_apply_def r = forAll arbitrary $ \x y -> r ! (x,y) == ((x,y) `elem` toList r)

prop_compose_def :: (M.IsKey Table a, M.IsKey Table b, M.IsKey Table c) 
                 => Relation a b -> Relation b c -> Bool
prop_compose_def r0 r1 =   toList (compose r0 r1) 
                        == LO.nubSort [ (x,z) | (x,y) <- toList r0
                                           , (w,z) <- toList r1
                                           , y == w ]

closure :: M.IsKey Table a => Relation a a -> Relation a a
closure r = Rel 
        $ cleanup $ M.convertMap
        $ M.map (M.fromSet (const ()) . S.fromList)
        $ Perm.closure' $ asGraph r

asGraph :: (M.IsKey Table a,Ord a) => Relation a a -> Perm.GraphImp a
asGraph r@(Rel m) = Perm.from_map (S.toList $ domain r `S.union` range r) 
        (M.convertMap $ M.map M.keys m)

cycles :: (M.IsKey Table a,Ord a) => Relation a a -> [[a]]
cycles r = Perm.cycles $ asGraph r

prop_all_valid :: M.IsKey Table b => S.Set b -> Fun b b -> Fun b Bool -> Relation b b -> Relation b b -> Bool
prop_all_valid s f p r0 r1 = all imp_invariant 
            [ r0,r1
            , compose r0 r1
            , empty
            , union r0 r1
            , intersection r0 r1
            , difference r0 r1
            , identity s
            , s `domSubt` r0
            , s `domRestr` r0
            , r0 `ranSubt` s
            , r0 `ranRestr` s
            , transpose r0
            , mapDomain (apply f) r0
            , mapRange (apply f) r0
            , closure r0
            , filterRan (apply p) r0
            , filterDom (apply p) r0 ]

prop_union_def :: (M.IsKey Table b, M.IsKey Table a, Ord a) => Relation a b -> Relation a b -> Bool
prop_union_def r0 r1 = LO.nubSort (toList r0 ++ toList r1) == toList (r0 `union` r1)

prop_intersection_def :: (M.IsKey Table b, M.IsKey Table a, Ord a) => Relation a b -> Relation a b -> Bool
prop_intersection_def r0 r1 = LO.nubSort (toList r0 `intersect` toList r1) == toList (r0 `intersection` r1)

prop_difference_def :: (M.IsKey Table b, M.IsKey Table a, Ord a) => Relation a b -> Relation a b -> Bool
prop_difference_def r0 r1 = LO.nubSort (toList r0 \\ toList r1) == toList (r0 `difference` r1)

prop_identity_def :: M.IsKey Table b => S.Set b -> Bool
prop_identity_def s = toList (identity s) == map (\x -> (x,x)) (S.toList s)

prop_ranSubt :: (M.IsKey Table b, Eq a, Ord b) => Relation a b -> S.Set b -> Bool
prop_ranSubt r s = toList (r `ranSubt` s) == filter (\(_,x) -> not $ x `S.member` s) (toList r)

prop_ranRestr :: (M.IsKey Table a, M.IsKey Table b, Ord b) => Relation a b -> S.Set b -> Bool
prop_ranRestr r s = toList (r `ranRestr` s) == filter (\(_,x) -> x `S.member` s) (toList r)

prop_domSubt :: (Eq b, M.IsKey Table a, Ord a) => Relation a b -> S.Set a -> Bool
prop_domSubt r s = toList (s `domSubt` r) == filter (\(x,_) -> not $ x `S.member` s) (toList r)

prop_domRestr :: (Eq b, M.IsKey Table a, Ord a) => Relation a b -> S.Set a -> Bool
prop_domRestr r s = toList (s `domRestr` r) == filter (\(x,_) -> x `S.member` s) (toList r)

prop_transpose_def :: (M.IsKey Table b, M.IsKey Table a, Ord b) => Relation b a -> Bool
prop_transpose_def r = toList (transpose r) == sort (map swap $ toList r)

prop_subset_def :: (M.IsKey Table b, M.IsKey Table a, Ord a) => Relation a b -> Relation a b -> Bool
prop_subset_def r0 r1 = r0 `subset` r1 == toList r0 `LO.subset` toList r1

prop_irreflexive_def :: (Arbitrary b, Show b, Ord b, M.IsKey Table b) => Relation b b -> Bool
prop_irreflexive_def r = (irreflexive r) == all (\x -> not $ r ! (x,x)) (S.toList $ domain r `S.union` range r)

prop_symmetric_def :: M.IsKey Table b => Relation b b -> Bool
prop_symmetric_def r = all (\x -> r ! swap x) (toList r) == symmetric r

prop_transitive_def :: M.IsKey Table b => Relation b b -> Bool
prop_transitive_def r = compose r r `subset` r == transitive r

prop_antisymmetric_def :: M.IsKey Table b => Relation b b -> Bool
prop_antisymmetric_def r = all (\x -> not $ r ! swap x) (toList r) == antisymmetric r

prop_null_def :: (Eq b, Eq a) => Relation a b -> Bool
prop_null_def r = null r == (r == empty)

prop_image_def :: (M.IsKey Table a, M.IsKey Table b) => Relation a b -> a -> Bool
prop_image_def r x = images r x == range (S.singleton x `domRestr` r)

prop_closure_is_transitive :: M.IsKey Table b => Relation b b -> Bool
prop_closure_is_transitive r = (cl_r `compose` r) `union` r == cl_r
    where
        cl_r = closure r

prop_mapDomain_def :: (M.IsKey Table b, Ord b, M.IsKey Table c) => Fun a b -> Relation a c -> Bool
prop_mapDomain_def (Fun _ f) r = toList (mapDomain f r) == LO.nubSort (map (first f) (toList r))

prop_mapRange_def :: (M.IsKey Table b, Ord b, M.IsKey Table a) => Fun c b -> Relation a c -> Bool
prop_mapRange_def (Fun _ f) r = toList (mapRange f r) == LO.nubSort (map (second f) (toList r))

prop_cycles_all_valid :: M.IsKey Table b => Relation b b -> Bool
prop_cycles_all_valid r = all (\c -> and [ cl ! (u,v) | u <- c, v <- c ] ) (cycles r)
    where
        cl = closure r

prop_cycles_maximal :: M.IsKey Table b => Relation b b -> Bool
prop_cycles_maximal r = and $ do
        let r_cycle = cycles r
        (c0,cs) <- zip r_cycle $ drop 1 $ tails r_cycle
        c1 <- cs
        u <- c0
        v <- c1
        return $ not (cl ! (u,v)) || not (cl ! (v,u))
    where
        cl = closure r

prop_filterDom_def :: (Eq a, Eq b) => Fun a Bool -> Relation a b -> Bool
prop_filterDom_def (Fun _ p) r = toList (filterDom p r) == filter (p . fst) (toList r)

prop_filterRan_def :: (Eq a, Eq b) => Fun b Bool -> Relation a b -> Bool
prop_filterRan_def (Fun _ p) r = toList (filterRan p r) == filter (p . snd) (toList r)

prop_mapMaybeDom_def :: (M.IsKey Table c, Ord c, M.IsKey Table b) => Fun b1 (Maybe c) -> Relation b1 b -> Bool
prop_mapMaybeDom_def (Fun _ f) r = toList (mapMaybeDom f r) == LO.nubSort (mapMaybe (first' f) (toList r))
    where
        first' = runKleisli . first . Kleisli

prop_mapMaybeRan_def :: (M.IsKey Table c, Ord c, M.IsKey Table a) => Fun b (Maybe c) -> Relation a b -> Bool
prop_mapMaybeRan_def (Fun _ f) r = toList (mapMaybeRan f r) == LO.nubSort (mapMaybe (second' f) (toList r))
    where
        second' = runKleisli . second . Kleisli

prop_bimapMaybe_def :: (M.IsKey Table a1,Ord a1, M.IsKey Table b0, M.IsKey Table b1) => Fun a0 (Maybe a1) -> Fun b0 (Maybe b1) -> Relation a0 b0 -> Bool
prop_bimapMaybe_def (Fun _ f) (Fun _ g) r = 
        toList (bimapMaybe f g r) == LO.nubSort (mapMaybe (runKleisli $ f' *** g') (toList r))
    where
        f' = Kleisli f
        g' = Kleisli g

return []

run_spec :: IO Bool
run_spec = $quickCheckAll

instance (NFData a,NFData b) => NFData (Relation a b)
