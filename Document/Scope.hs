{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE ImplicitParams            #-}
module Document.Scope 
    ( Scope(..)
    , HasDeclSource (..)
    , HasLineInfo (..)
    , HasInhStatus (..)
    , make_table
    , make_all_tables 
    , make_all_tables'
    , all_errors
    , scopeUnion
    , merge_scopes
    , fromEither'
    , is_inherited, is_local
    , DeclSource(..)
    , InhStatus(..)
    , EventInhStatus
    , contents
    , WithDelete 
    , Redundant
    , RefScope(..)
    )
where

    -- Modules
import Document.Pipeline

import UnitB.Event

    -- Libraries
import Control.Applicative
import Control.Arrow (second,(***))
import Control.DeepSeq

import Control.Lens as L 
import Control.Monad.Identity
import Control.Monad.RWS (tell)
import Control.Parallel.Strategies

import Data.Either
import Data.Maybe 
import Data.List as L
import Data.List.NonEmpty as NE hiding (length,tail,head)
import Data.Map as M
import Data.Semigroup ((<>),First(..))
import qualified Data.Traversable as T

import GHC.Stack

import Test.QuickCheck as QC

import Utilities.Instances 
import Utilities.Invariant hiding ((===))
import Utilities.Permutation
import Utilities.Syntactic

    -- clashes is a symmetric, reflexive relation
class (Ord a,Show a) => Scope a where
    type Impl a :: *
    type Impl a = DefaultClashImpl a
    kind :: a -> String
    error_item :: a -> (String,LineInfo)
    default error_item :: (HasLineInfo a LineInfo) => a -> (String,LineInfo)
    error_item x = (kind x, view lineInfo x)

    keep_from :: DeclSource -> a -> Maybe a
    default keep_from :: (ClashImpl (Impl a), HasImplIso (Impl a) a) 
                      => DeclSource -> a -> Maybe a
    keep_from s x = (asImpl :: Iso' a (Impl a)) (keepFromImpl s) x

    make_inherited :: a -> Maybe a
    default make_inherited :: (ClashImpl (Impl a), HasImplIso (Impl a) a) 
                           => a -> Maybe a
    make_inherited x = (asImpl :: Iso' a (Impl a)) makeInheritedImpl x

    merge_scopes' :: a -> a -> Maybe a
    default merge_scopes' :: (ClashImpl (Impl a), HasImplIso (Impl a) a) => a -> a -> Maybe a
    merge_scopes' x y = view (L.from asImpl) <$> mergeScopesImpl (x^.asImpl :: Impl a) (y^.asImpl)

        -- | let x be a collection of event-related declaration in machine m0 and m1 be a 
        -- | refinement of m0. rename_events sub x translates the name in x from the m0 
        -- | namespace to the m1 namespace.
    rename_events :: Map EventId [EventId] -> a -> [a]

    axiom_Scope_clashesIsSymmetric :: a -> a -> Bool
    axiom_Scope_clashesIsSymmetric x y = (x `clash` y) == (y `clash` x)
    axiom_Scope_clashesOverMerge :: a -> a -> a -> Bool
    axiom_Scope_clashesOverMerge x y z = clash x y || ((x <+> y) `clash` z == (x `clash` z || y `clash` z))
    axiom_Scope_mergeCommutative :: a -> a -> Property
    axiom_Scope_mergeCommutative x y = clash x y .||. x <+> y === y <+> x
    axiom_Scope_mergeAssociative :: a -> a -> a -> Property
    axiom_Scope_mergeAssociative x y z = not (clashFree [x,y,z]) .||. x <+> (y <+> z) === (x <+> y) <+> z

clash :: Scope a => a -> a -> Bool
clash x y = isNothing $ merge_scopes' x y

merge_scopes :: (Scope a, ?loc :: CallStack) => a -> a -> a
merge_scopes x y = fromJust' $ merge_scopes' x y

scopeUnion :: Ord k
           => (a -> a -> Maybe a) 
           -> Map k a 
           -> Map k a 
           -> Maybe (Map k a)
scopeUnion f m0 m1 = sequence $ unionWith f' (Just <$> m0) (Just <$> m1)
    where
        f' x y = join $ f <$> x <*> y

(<+>) :: (Scope a, ?loc :: CallStack) => a -> a -> a
(<+>) x y = x `merge_scopes` y

clashFree :: Scope a => [a] -> Bool
clashFree [] = True
clashFree (x:xs) = all (not . clash x) xs && clashFree xs

newtype DefaultClashImpl a = DefaultClashImpl { getDefaultClashImpl :: a }

class HasImplIso a b where
    asImpl :: Iso' b a

class ClashImpl a where
    mergeScopesImpl :: a -> a -> Maybe a
    keepFromImpl :: DeclSource -> a -> Maybe a
    makeInheritedImpl :: a -> Maybe a

instance HasDeclSource a DeclSource 
        => ClashImpl (DefaultClashImpl a) where
    keepFromImpl s x'@(DefaultClashImpl x) = guard (x ^. declSource == s) >> return x'
    makeInheritedImpl (DefaultClashImpl x) = Just $ DefaultClashImpl $ x & declSource .~ Inherited
    mergeScopesImpl _ _ = Nothing

instance HasImplIso (DefaultClashImpl a) a where
    asImpl = iso DefaultClashImpl getDefaultClashImpl

class HasDeclSource a b | a -> b where
    declSource :: Lens' a b

class HasLineInfo a b | a -> b where
    lineInfo :: Lens' a b

class HasInhStatus a b | a -> b where
    inhStatus :: Lens' a b

is_inherited :: Scope s => s -> Maybe s
is_inherited = keep_from Inherited

is_local :: Scope s => s -> Maybe s
is_local = keep_from Local

data DeclSource = Inherited | Local
    deriving (Eq,Ord,Show,Generic)

data InhStatus a = InhAdd a | InhDelete (Maybe a)
    deriving (Eq,Ord,Show,Functor,Foldable,Traversable,Generic)

type EventInhStatus a = InhStatus (NonEmpty EventId,a)

data RefScope = Old | New

contents :: HasInhStatus a (InhStatus b) => a -> Maybe b
contents x = case x ^. inhStatus of
                InhAdd x -> Just x
                InhDelete x -> x

fromEither' :: Either [Error] a -> MM' c (Maybe a)
fromEither' (Left es) = tell es >> return Nothing
fromEither' (Right x) = return $ Just x

all_errors :: Traversable t 
           => t (Either [Error] a) 
           -> MM' c (Maybe (t a))
all_errors m = T.mapM fromEither' m >>= (return . T.sequence)

make_table :: (Ord a, Show a) 
           => (a -> String) 
           -> [(a,b,LineInfo)] 
           -> Either [Error] (Map a (b,LineInfo))
make_table f xs = returnOrFail $ fromListWith add $ L.map mkCell xs
    where
        mkCell (x,y,z) = (x,Right (y,z))
        sepError (x,y) = case y of
                 Left z -> Left (x,z)
                 Right (z,li) -> Right (x,(z,li))
        returnOrFail m = failIf $ L.map sepError $ M.toList m
        failIf xs 
            | L.null ys = return $ M.fromList $ rights xs
            | otherwise = Left $ L.map (uncurry err) ys
            where
                ys = lefts xs
        err x li = MLError (f x) (L.map (show x,) li)
        lis (Left xs)     = xs
        lis (Right (_,z)) = [z]
        add x y = Left $ lis x ++ lis y

make_all_tables' :: (Scope b, Show a, Ord a, Ord k) 
                 => (a -> String) 
                 -> Map k [(a,b)] 
                 -> MM (Maybe (Map k (Map a b)))
make_all_tables' f xs = T.sequence <$> T.sequence (M.map (make_table' f) xs `using` parTraversable rseq)

make_all_tables :: (Show a, Ord a, Ord k) 
                => (a -> String)
                -> Map k [(a, b, LineInfo)] 
                -> MM (Maybe (Map k (Map a (b,LineInfo))))
make_all_tables f xs = all_errors (M.map (make_table f) xs `using` parTraversable rseq)

make_table' :: forall a b.
               (Ord a, Show a, Scope b) 
            => (a -> String) 
            -> [(a,b)] 
            -> MM (Maybe (Map a b))
make_table' f items = all_errors $ M.mapWithKey g conflicts
        -- PROBLEM: given x,y,z, it's possible that none conflict with each other but
        -- x `merge` y conflicts with z
    where
        g k ws
                | all (\xs -> length xs <= 1) ws 
                            = Right $ L.foldl merge_scopes (head xs) (tail xs)
                | otherwise = Left $ L.map (\xs -> MLError (f k) $ L.map error_item xs) 
                                    $ L.filter (\xs -> length xs > 1) ws
            where
                xs = concat ws             
        items' = fromListWith (++) $ L.map (\(x,y) -> (x,[y])) items
        conflicts :: Map a [[b]]
        conflicts = M.map (flip u_scc clash) items' 

newtype WithDelete a = WithDelete { getDelete :: a }

instance Arbitrary DeclSource where
    arbitrary = genericArbitrary

instance Arbitrary e => Arbitrary (InhStatus e) where
    arbitrary = genericArbitrary

instance HasImplIso (WithDelete a) a where
    asImpl = iso WithDelete getDelete

newtype Redundant expr a = Redundant { getRedundant :: a }

instance HasImplIso a b => HasImplIso (Redundant expr a) b where
    asImpl = asImpl . iso Redundant getRedundant

instance HasInhStatus a b => HasInhStatus (WithDelete a) b where
    inhStatus = lens getDelete (const WithDelete) . inhStatus

instance HasDeclSource a b => HasDeclSource (WithDelete a) b where
    declSource = lens getDelete (const WithDelete) . declSource

instance ( HasInhStatus a (InhStatus expr)
         , Show expr
         , HasDeclSource a DeclSource )
        => ClashImpl (WithDelete a) where
    makeInheritedImpl (WithDelete x) = Just $ WithDelete $ x & declSource .~ Inherited
    keepFromImpl s (WithDelete x) = guard b >> return (WithDelete x)
        where
            b = case x ^. inhStatus of
                    InhAdd _ -> x ^. declSource == s
                    InhDelete _  -> s == Inherited

    mergeScopesImpl (WithDelete x) (WithDelete y) = WithDelete <$> z
        where
            z = case (x ^. inhStatus, y ^. inhStatus) of
                    (InhDelete Nothing, InhAdd e) -> Just $ x & inhStatus .~ InhDelete (Just e)
                    (InhAdd e, InhDelete Nothing) -> Just $ y & inhStatus .~ InhDelete (Just e)
                    _ -> Nothing

instance ( Eq expr, ClashImpl a
         , HasInhStatus a (EventInhStatus expr)
         , HasDeclSource a DeclSource)
        => ClashImpl (Redundant expr a) where
    makeInheritedImpl = fmap Redundant . makeInheritedImpl . getRedundant
    keepFromImpl s = fmap Redundant . keepFromImpl s . getRedundant
    mergeScopesImpl (Redundant x) (Redundant y) = Redundant <$> (mergeScopesImpl x y <|> g x y)
        where
            g :: a -> a -> Maybe a
            g x y = guard' x y >> Just (x & inhStatus %~ (flip f $ y^.inhStatus) 
                                          & declSource %~ (declUnion $ y^.declSource))
            guard' x y = guard =<< ((==) <$> (snd <$> contents x) <*> (snd <$> contents y))
            f (InhAdd x) (InhAdd y) = InhAdd $ x & _1 %~ NE.sort.(<> y^._1)
            f (InhAdd x) (InhDelete y) = InhDelete $ y & traverse._1 %~ NE.sort.(x^._1 <>)
            f (InhDelete x) (InhAdd y) = InhDelete $ x & traverse._1 %~ NE.sort.(<> y^._1)
            f (InhDelete x) (InhDelete y) = InhDelete $ (NE.sort *** getFirst) <$> (second First <$> x) <> (second First <$> y)
            declUnion Local Local = Local
            declUnion _ _         = Inherited

instance NFData DeclSource
