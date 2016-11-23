{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE ViewPatterns              #-}
module Document.Scope 
    ( Scope(..)
    , rename_events
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
    , NonEmptyListSet
    , nonEmptyListSet
    , setToList, setToNeList
    , setToList', setToNeList'
    , listSet
    , declUnion
    , RefScope(..)
    )
where

    -- Modules
import Document.Pipeline

import Logic.Expr.PrettyPrint

import UnitB.Event

    -- Libraries
import Control.Applicative
import Control.Arrow (second)
import Control.DeepSeq

import Control.Lens as L 
import Control.Lens.Extras
import Control.Lens.Misc
import Control.Monad.Identity
import Control.Monad.RWS (tell)
import Control.Parallel.Strategies
import Control.Precondition

import Data.DList as D
import Data.Either.Validation
import Data.Graph.Array
import Data.List as L
import qualified Data.List.Ordered as Ord
import           Data.List.NonEmpty as NE hiding (length,tail,head,map)
import qualified Data.List.NonEmpty as NE 
import           Data.Map as M
import           Data.Maybe as MM
import           Data.Semigroup (Semigroup(..),First(..))
import qualified Data.Traversable as T

import GHC.Generics.Instances 

import Test.QuickCheck as QC hiding (Failure,Success)
import Test.QuickCheck.ZoomEq

import Utilities.Syntactic

data DeclSource = Inherited | Local
    deriving (Eq,Ord,Show,Generic)

data InhStatus a = InhAdd a | InhDelete (Maybe a)
    deriving (Eq,Ord,Show,Functor,Foldable,Traversable,Generic)

makePrisms ''InhStatus

    -- clashes is a symmetric, reflexive relation
class (Ord a,Show a,ZoomEq a,PrettyPrintable a) => Scope a where
    type Impl a :: *
    type Impl a = DefaultClashImpl a
    kind :: a -> String
    error_item :: a -> NonEmpty (String,LineInfo)
    default error_item :: ( HasLineInfo a li, ErrorItem li
                          , ClashImpl (Impl a), HasImplIso (Impl a) a) 
                       => a -> NonEmpty (String,LineInfo)
    error_item x = errorItemImpl (kind x) (x^.lineInfo)

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
    rename_events' :: (EventId -> [EventId]) -> a -> [a]

    axiom_Scope_clashesIsSymmetric :: a -> a -> Bool
    axiom_Scope_clashesIsSymmetric x y = (x `clash` y) == (y `clash` x)
    axiom_Scope_clashesOverMerge :: PrettyPrintable a => a -> a -> a -> Property
    axiom_Scope_clashesOverMerge x y z = 
            counterexample ("x <+> y: " ++ pretty (x <+> y)) $
            counterexample ("x clash z: " ++ show (x `clash` z)) $
            counterexample ("y clash z: " ++ show (y `clash` z)) $
            clash x y .||. ((x <+> y) `clash` z === (x `clash` z || y `clash` z))
    axiom_Scope_mergeCommutative :: a -> a -> Property
    axiom_Scope_mergeCommutative x y = clash x y .||. x <+> y === y <+> x
    axiom_Scope_mergeAssociative :: a -> a -> a -> Property
    axiom_Scope_mergeAssociative x y z = not (clashFree [x,y,z]) .||. x <+> (y <+> z) .== (x <+> y) <+> z

rename_events :: (Scope a) 
              => M.Map EventId [EventId] 
              -> a -> [a]
rename_events m = rename_events' (\e -> findWithDefault [e] e m)

clash :: Scope a => a -> a -> Bool
clash x y = isNothing $ merge_scopes' x y

merge_scopes :: (Scope a, Pre) => a -> a -> a
merge_scopes x y = fromJust' $ merge_scopes' x y

scopeUnion :: Ord k
           => (a -> a -> Maybe a) 
           -> M.Map k a 
           -> M.Map k a 
           -> Maybe (M.Map k a)
scopeUnion f m0 m1 = sequence $ unionWith f' (Just <$> m0) (Just <$> m1)
    where
        f' x y = join $ f <$> x <*> y

(<+>) :: (Scope a, Pre) => a -> a -> a
(<+>) x y = x `merge_scopes` y

clashFree :: Scope a => [a] -> Bool
clashFree [] = True
clashFree (x:xs) = all (not . clash x) xs && clashFree xs

newtype DefaultClashImpl a = DefaultClashImpl { getDefaultClashImpl :: a }

defaultClashImpl :: Iso (DefaultClashImpl a) (DefaultClashImpl b) a b
defaultClashImpl = iso getDefaultClashImpl DefaultClashImpl

class HasImplIso a b where
    asImpl :: Iso' b a

class ClashImpl a where
    mergeScopesImpl :: a -> a -> Maybe a
    keepFromImpl :: DeclSource -> a -> Maybe a
    makeInheritedImpl :: a -> Maybe a

class ErrorItem err where
    errorItemImpl :: String 
                  -> err 
                  -> NonEmpty (String,LineInfo)

instance ErrorItem LineInfo where
    errorItemImpl kind x = pure (kind,x)

instance ErrorItem (NonEmpty LineInfo) where
    errorItemImpl kind xs = (kind,) <$> xs

instance ErrorItem (NonEmptyListSet LineInfo) where
    errorItemImpl kind xs = setToNeList' $ (kind,) <$> xs

instance (HasDeclSource a DeclSource)
        => ClashImpl (DefaultClashImpl a) where
    keepFromImpl s x'@(DefaultClashImpl x) = guard (x ^. declSource == s) >> return x'
    makeInheritedImpl (DefaultClashImpl x) = Just $ DefaultClashImpl $ x & declSource .~ Inherited
    mergeScopesImpl _ _  = Nothing

instance HasImplIso (DefaultClashImpl a) a where
    asImpl = from defaultClashImpl

instance HasLineInfo a b => HasLineInfo (DefaultClashImpl a) b where
    lineInfo = defaultClashImpl . lineInfo

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

newtype NonEmptyListSet a = NonEmptyListSet 
        { unNonEmptyListSet :: DList a } 
    deriving (Generic,Functor,Applicative,Semigroup)

_listSet' :: Ord a => DList a -> NonEmptyListSet a
_listSet' x = NonEmptyListSet x 

listSet :: (Ord a,Pre) => [a] -> NonEmptyListSet a
listSet x = nonEmptyListSet $ NE.fromList x

nonEmptyListSet :: Ord a => NonEmpty a -> NonEmptyListSet a
nonEmptyListSet x = NonEmptyListSet (D.fromList $ NE.toList x) 

setToList :: Ord a => NonEmptyListSet a -> [a]
setToList = Ord.nubSort . D.toList . unNonEmptyListSet

setToList' :: Ord a => NonEmptyListSet a -> [a]
setToList' = D.toList . unNonEmptyListSet

setToNeList' :: Ord a => NonEmptyListSet a -> NonEmpty a
setToNeList' = NE.fromList . setToList'

setToNeList :: Ord a => NonEmptyListSet a -> NonEmpty a
setToNeList = NE.fromList . setToList

instance Ord a => Eq (NonEmptyListSet a) where
    x == y = setToList x == setToList y
instance Ord a => Ord (NonEmptyListSet a) where
    compare x y = setToList x `compare` setToList y

instance (Show a,Ord a) => Show (NonEmptyListSet a) where
    show x = "listSet " ++ show (setToList x)
instance (PrettyPrintable a,Ord a) => PrettyPrintable (NonEmptyListSet a) where

instance (ZoomEq a,Ord a) => ZoomEq (NonEmptyListSet a) where
    x .== y = setToList x .== setToList y

newtype HeadOrd a = HeadOrd (NonEmpty a) deriving (Eq, Show)

instance Ord a => Ord (HeadOrd a) where
    compare (HeadOrd x) (HeadOrd y) = compare (NE.head x) (NE.head y)


instance (Arbitrary a,Ord a) => Arbitrary (NonEmptyListSet a) where
    arbitrary = nonEmptyListSet . NE.nub . NE.sort <$> arbitrary

instance Ord a => Wrapped (NonEmptyListSet a) where
    type Unwrapped (NonEmptyListSet a) = NonEmpty a
    _Wrapped' = iso setToNeList' nonEmptyListSet

type EventInhStatus a = InhStatus (NonEmptyListSet (EventId,LineInfo),a)

data RefScope = Old | New
    deriving (Eq,Ord,Show)

instance PrettyPrintable a => PrettyPrintable (InhStatus a) where

instance PrettyPrintable RefScope where
    pretty = show

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

make_table :: (Ord a, PrettyPrintable a) 
           => (a -> String) 
           -> [(a,b,LineInfo)] 
           -> Either [Error] (M.Map a (b,LineInfo))
make_table f xs = validationToEither $ M.traverseWithKey failIf' $ M.fromListWith (<>) $ L.map mkCell' xs 
    where
        mkCell' (x,y,z) = (x,(y,z) :| [])
        failIf' _ (x :| []) = pure x
        failIf' k xs = Failure $ err k (snd <$> xs)
        err x li = [MLError (f x) (fmap (pretty x,) li)]

make_all_tables' :: (Scope b, Show a, Ord a, Ord k) 
                 => (a -> String) 
                 -> M.Map k [(a,b)] 
                 -> MM (Maybe (M.Map k (M.Map a b)))
make_all_tables' f xs = T.sequence <$> T.sequence (M.map (make_table' f) xs `using` parTraversable rseq)

make_all_tables :: (PrettyPrintable a, Ord a, Ord k) 
                => (a -> String)
                -> M.Map k [(a, b, LineInfo)] 
                -> MM (Maybe (M.Map k (M.Map a (b,LineInfo))))
make_all_tables f xs = all_errors (M.map (make_table f) xs `using` parTraversable rseq)

make_table' :: forall a b.
               (Ord a, Show a, Scope b) 
            => (a -> String) 
            -> [(a,b)] 
            -> MM (Maybe (M.Map a b))
make_table' f items = all_errors $ M.mapWithKey g conflicts
        -- | PROBLEM: given x,y,z, it's possible that none conflict with each other but
        -- | x `merge` y conflicts with z
    where
        g k ws = case traverseValidation onlyOne ws of
                    Right xs -> Right $ L.foldl' merge_scopes (NE.head xs) (NE.tail xs)
                    Left xs  -> Left $ [ MLError (f k) $ sconcat $ fmap error_item err | err <- xs ]
            where
                onlyOne (x :| []) = Right x
                onlyOne xs = Left [xs]
        items' :: M.Map a [b]
        items' = M.map D.toList . fromListWith (<>) $ L.map (\(x,y) -> (x,pure y)) items
        conflicts :: M.Map a (NonEmpty (NonEmpty b))
        conflicts = M.mapMaybe (nonEm . flip u_scc clash) items' 
        nonEm :: [[d]] -> Maybe (NonEmpty (NonEmpty d))
        nonEm = nonEmpty . MM.mapMaybe nonEmpty

newtype WithDelete a = WithDelete { getDelete :: a }
    deriving Show

deleteIso :: Iso (WithDelete a) (WithDelete b) a b
deleteIso = iso getDelete WithDelete

instance PrettyPrintable DeclSource where
    pretty = show

instance ZoomEq DeclSource where
instance Arbitrary DeclSource where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance ZoomEq e => ZoomEq (InhStatus e) where

instance Arbitrary e => Arbitrary (InhStatus e) where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance HasImplIso (WithDelete a) a where
    asImpl = from deleteIso

newtype Redundant expr a = Redundant { getRedundant :: a }

redundant :: Iso (Redundant expr a) (Redundant expr b) a b
redundant = iso getRedundant Redundant

instance HasImplIso a b => HasImplIso (Redundant expr a) b where
    asImpl = asImpl . from redundant

instance HasInhStatus a b => HasInhStatus (WithDelete a) b where
    inhStatus = deleteIso . inhStatus

instance HasDeclSource a b => HasDeclSource (WithDelete a) b where
    declSource = deleteIso . declSource

instance HasLineInfo a b => HasLineInfo (WithDelete a) b where
    lineInfo = deleteIso . lineInfo

instance HasLineInfo a b => HasLineInfo (Redundant expr a) b where
    lineInfo = redundant . lineInfo

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
            z = case (x^.inhStatus, y^.inhStatus) of
                    (InhDelete Nothing, InhAdd e) 
                        | y^.declSource == Inherited -> Just $ x & inhStatus .~ InhDelete (Just e)
                                                                 & declSource %~ (declUnion $ y^.declSource)
                    (InhAdd e, InhDelete Nothing) 
                        | x^.declSource == Inherited -> Just $ y & inhStatus .~ InhDelete (Just e)
                                                                 & declSource %~ (declUnion $ x^.declSource)
                    _ -> Nothing

instance ( Eq expr, ClashImpl a, Show a
         , HasLineInfo a (NonEmptyListSet LineInfo)
         , HasInhStatus a (EventInhStatus expr)
         , HasDeclSource a DeclSource)
        => ClashImpl (Redundant expr a) where
    makeInheritedImpl = fmap Redundant . makeInheritedImpl . getRedundant
    keepFromImpl s = fmap Redundant . keepFromImpl s . getRedundant
    mergeScopesImpl (Redundant x) (Redundant y) = Redundant <$> ((reSort <$> mergeScopesImpl x y) <|> g x y)
        where
            reSort = lineInfo .~ (x^.lineInfo <> y^.lineInfo)
            g :: a -> a -> Maybe a
            g x y = guard' x y >> Just (x & inhStatus %~ (flip f $ y^.inhStatus) 
                                          & declSource %~ (declUnion $ y^.declSource)
                                          & lineInfo %~ (<> (y^.lineInfo)))
                                          -- & declSource %~ (declUnion $ y^.declSource)
                                          -- & lineInfo %~ (<> (y^.lineInfo)))
            guard' :: a -> a -> Maybe ()
            guard' x y = guard $ oneInherited x y && sameContents x y
            sameContents x y = fromMaybe True $ liftA2 (==) (snd <$> contents x) (snd <$> contents y)
            f :: EventInhStatus expr -> EventInhStatus expr -> EventInhStatus expr
            f (InhAdd x) (InhAdd y) = InhAdd $ x & _1 %~ (<> y^._1)
            f (InhAdd x) (InhDelete y) = InhDelete $ y & traverse._1 %~ (x^._1 <>)
            f (InhDelete x) (InhAdd y) = InhDelete $ x & traverse._1 %~ (<> y^._1)
            f (InhDelete x) (InhDelete y) = InhDelete $ second getFirst <$> (second First <$> x) <> (second First <$> y)

oneInherited :: ( HasDeclSource s DeclSource
                , HasInhStatus s (InhStatus a))
             => s -> s -> Bool
oneInherited x y = 
           (x^.declSource == Inherited && y^.declSource == Inherited)
        || (x^.declSource == Inherited && _InhAdd `is` (x^.inhStatus))
        || (y^.declSource == Inherited && _InhAdd `is` (y^.inhStatus))

declUnion :: DeclSource -> DeclSource -> DeclSource
declUnion Inherited Inherited = Inherited
declUnion _ _                 = Local

instance NFData DeclSource
