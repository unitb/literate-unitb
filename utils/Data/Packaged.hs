{-# LANGUAGE DeriveGeneric
    ,TypeFamilies
    ,StandaloneDeriving
    ,UndecidableInstances
    ,RankNTypes
    ,ExistentialQuantification
    ,FlexibleInstances
    ,MultiParamTypeClasses
    ,FunctionalDependencies #-}
module Data.Packaged where

import Control.DeepSeq
import Control.Lens
import Control.Monad
import Control.Monad.Loops

import Data.ByteString hiding (putStrLn)
import Data.Char
import Data.Data
import Data.Either.Combinators
import Data.Functor.Classes
import Data.Hashable
import Data.List.NonEmpty
import Data.Semigroup
import Data.Serialize as Ser
import Data.String

import Language.Haskell.TH.Syntax

import Utilities.Instances

newtype Packaged a = Package { getPackage :: ByteString }
    deriving (Eq,Ord,Data,Generic,Hashable)

packaged :: (Serialize a,Serialize b)
         => Iso a b (Packaged a) (Packaged b)
packaged = iso (Package . encode) (fromRight' . decode . getPackage)

unpackaged :: (Serialize a,Serialize b)
           => Iso (Packaged a) (Packaged b) a b
unpackaged = from packaged

instance Serialize a => Wrapped (Packaged a) where
    type Unwrapped (Packaged a) = a
    _Wrapped' = unpackaged

instance Serialize (Packaged a) where

class OnPackaged a where
    type UnpackedFun a :: *
    onPackaged :: UnpackedFun a -> a

instance (Serialize a,OnPackaged b) => OnPackaged (Packaged a -> b) where
    type UnpackedFun (Packaged a -> b) = a -> UnpackedFun b
    onPackaged f x = onPackaged $ f $ x^.unpackaged

instance Serialize a => OnPackaged (Packaged a) where
    type UnpackedFun (Packaged a) = a
    onPackaged = view packaged

instance (Serialize a,Show a) => Show (Packaged a) where
    show = show . view unpackaged

instance NFData (Packaged a) where

newtype NullTerminated f = NullTerm {getNullString :: f Char}
    deriving (Typeable,Generic)
type NullTerminatedString = NullTerminated []
type NullTerminatedNEString = NullTerminated NonEmpty

deriving instance (Typeable f,Data (f Char)) => Data (NullTerminated f)

instance Eq1 f => Eq (NullTerminated f) where
    NullTerm x == NullTerm y = eq1 x y
instance Ord1 f => Ord (NullTerminated f) where
    NullTerm x `compare` NullTerm y = compare1 x y

instance Show (NullTerminated []) where
    show = show . getNullString
instance Show (NullTerminated NonEmpty) where
    show = show . getNullString

instance IsString NullTerminatedString where
    fromString = NullTerm

instance NFData1 f => NFData (NullTerminated f) where
    rnf = rnf1 . getNullString

instance Wrapped (NullTerminated f) where
    type Unwrapped (NullTerminated f) = f Char
    _Wrapped' = iso getNullString NullTerm

instance Serialize (NullTerminated []) where
    put (NullTerm xs) = mapM_ put xs >> put (chr 0)
    {-# INLINE get #-}
    get = NullTerm <$> 
            whileJust (do x <- get ; return (if x == chr 0 then Nothing else Just x)) return

putNullTerminated :: Foldable t => Putter (t Char)
putNullTerminated xs = mapM_ put xs >> put (chr 0)

getNullTerminatedList :: Get String
getNullTerminatedList = do
        x <- get
        if x == chr 0 
            then return []
            else (x:) <$> getNullTerminatedList

getNullTerminatedNEList :: Get (NonEmpty Char)
getNullTerminatedNEList = maybe mzero return . nonEmpty =<< getNullTerminatedList

instance Serialize (NullTerminated NonEmpty) where
    put (NullTerm xs) = mapM_ put xs >> put (chr 0)
    {-# INLINE get #-}
    get = maybe mzero (return . NullTerm) . nonEmpty =<<
             whileJust (do x <- get ; return (if x == chr 0 then Nothing else Just x)) return

instance Hashable NullTerminatedNEString where
instance Hashable NullTerminatedString where

instance Semigroup NullTerminatedNEString where
    (<>) = genericSemigroupMAppend
instance Semigroup NullTerminatedString where
instance Monoid NullTerminatedString where
    mappend = genericMAppend
    mempty = genericMEmpty
    mconcat = genericMConcat

instance Lift1 f => Lift (NullTerminated f) where
    lift x = [e| NullTerm $(lift1 $ getNullString x) |]
