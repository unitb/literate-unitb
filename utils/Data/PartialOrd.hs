{-# LANGUAGE TypeFamilies #-}
module Data.PartialOrd where

import Control.Lens

import Data.Function
import Data.List 
import Data.List.Ordered
import Data.Proxy.TH
import Data.Tuple.Generics

import Test.QuickCheck

import qualified Utilities.Map as M
import Utilities.Table 

data PartOrdering = Comp Ordering | Uncomp
    deriving (Eq,Ord,Show)

newtype Quotient a = Quotient { _quotient :: a }
    deriving (Eq,Ord,Show,Arbitrary)

newtype Partial a = Partial { _partial :: a }
    deriving (Eq,Ord,Show,Arbitrary)

newtype Unordered a = Unordered { _unordered :: [a] }
    deriving (Eq,Ord,Show,Arbitrary)

makeLenses ''Partial
makePrisms ''PartOrdering
makeLenses ''Quotient
makeLenses ''Unordered

instance Monoid PartOrdering where
    mempty  = Comp EQ
    mappend (Comp EQ) x = x
    mappend Uncomp _ = Uncomp
    mappend x (Comp EQ) = x
    mappend _ Uncomp = Uncomp
    mappend (Comp LT) (Comp LT) = Comp LT
    mappend (Comp GT) (Comp GT) = Comp GT
    mappend (Comp GT) (Comp LT) = Uncomp
    mappend (Comp LT) (Comp GT) = Uncomp

instance Wrapped (Partial a) where
    type Unwrapped (Partial a) = a
    _Wrapped' = partial

opposite :: PartOrdering -> PartOrdering
opposite (Comp GT) = Comp LT
opposite (Comp LT) = Comp GT
opposite x = x

class PreOrd a where
    partCompare :: a -> a -> PartOrdering
    leq :: a -> a -> Bool
    leq x y = partCompare x y `elem` [Comp LT,Comp EQ]
    geq :: a -> a -> Bool
    geq x y = partCompare x y `elem` [Comp GT,Comp EQ]
    lt :: a -> a -> Bool
    lt x y = partCompare x y == Comp LT
    gt :: a -> a -> Bool
    gt x y = partCompare x y == Comp GT
    comparable :: a -> a -> Bool
    comparable x y = partCompare x y == Uncomp
    
    axiom_derived_def_geq :: a -> a -> Property
    axiom_derived_def_geq x y = leq x y === geq y x
    
    axiom_derived_def_gt :: a -> a -> Property
    axiom_derived_def_gt x y = lt x y === gt y x
    
    axiom_derived_def_lt :: a -> a -> Property
    axiom_derived_def_lt x y = lt x y === (leq x y && not (geq x y))
    
    axiom_derived_def_comparable :: a -> a -> Property
    axiom_derived_def_comparable x y = comparable x y === (partCompare x y == Uncomp)
    
    axiom_opposite_partCompare :: a -> a -> Property
    axiom_opposite_partCompare x y = partCompare x y === opposite (partCompare y x)
    
    axiom_derived_def_partCompare :: a -> a -> Bool
    axiom_derived_def_partCompare x y = case partCompare x y of
                                            Comp EQ -> leq x y && geq x y && not (gt x y) && not (lt x y)
                                            Comp LT -> leq x y && not (geq x y) && not (gt x y) && lt x y
                                            Comp GT -> not (leq x y) && geq x y && gt x y && not (lt x y)
                                            Uncomp  -> not (leq x y) && not (geq x y) && not (gt x y) && not (lt x y)
    axiom_transitity :: a -> a -> a -> Bool
    axiom_transitity x y z   = not (leq x y && leq y z) || leq x z
    
    axiom_reflexivity :: a -> Bool
    axiom_reflexivity x      = leq x x

class (Eq a,PreOrd a) => PartialOrd a where
    axiom_antisymmetry :: a -> a -> Bool
    axiom_antisymmetry x y = not (leq x y) || not (leq y x) || x == y

instance Ord a => PartialOrd (Partial a) where

instance Ord a => PreOrd (Partial a) where
    partCompare x y = Comp $ compare x y

instance Ord a => PreOrd (Unordered a) where
    partCompare (Unordered xs) (Unordered ys) = 
            case (null r,null l) of
                (True,True) -> Comp EQ
                (False,True) -> Comp GT
                (True,False) -> Comp LT
                (False,False) -> Uncomp
        where
            zs = xunionBy (compare `on` fst) ((,True) <$> sort xs) ((,False) <$> sort ys)
            (l,r) = partition snd zs

instance (Ord k,Eq a) => PreOrd (Table k a) where
    partCompare x y = case compare nX nY of
                        GT 
                            | M.isSubmapOf y x -> Comp GT
                            | otherwise        -> Uncomp
                        LT 
                            | M.isSubmapOf x y -> Comp LT
                            | otherwise        -> Uncomp
                        EQ  
                            | x == y    -> Comp EQ
                            | otherwise -> Uncomp
        where
            nX = M.size x
            nY = M.size y

instance (Ord k,Eq a) => PartialOrd (Table k a) where

instance Eq a => PreOrd (Quotient a) where
    partCompare x y
        | x == y    = Comp EQ
        | otherwise = Uncomp

instance Eq a => PartialOrd (Quotient a) where

genericPartialOrder :: (Generic a, GZippableRecord PartialOrd (Rep a))
                    => a -> a -> PartOrdering
genericPartialOrder = zipFields [pr|PartialOrd|] partCompare

genericPreorder :: (Generic a, GZippableRecord PreOrd (Rep a))
                => a -> a -> PartOrdering
genericPreorder = zipFields [pr|PreOrd|] partCompare

instance Arbitrary PartOrdering where
    arbitrary = oneof [Comp <$> arbitrary,return Uncomp]