{-# LANGUAGE TypeFamilies #-}
module Logic.Names.Packaged
    ( Name, InternalName
    , IsName(..)
    , IsBaseName(..) 
    , asInternal
    , asName
    , isZ3Name
    , makeName
    , Intl.make
    , Intl.make'
    , Intl.Translatable  (..)
    , addSuffix
    , addBackslash
    , reserved
    , setSuffix
    , dropSuffix
    , isName
    , isName'
    , Intl.fresh
    , smt, tex
    , NonEmpty((:|))
    , Intl.Encoding(Z3Encoding)
    )
where

    -- Modules
import Logic.Names.Internals (IsBaseName(..))
import qualified Logic.Names.Internals as Intl

    -- Libraries
import Control.DeepSeq
import Control.Lens
import Control.Precondition

import Data.Data
import Data.Hashable
import Data.List.NonEmpty
import Data.Packaged
import Data.Serialize

import GHC.Generics (Generic)

import Language.Haskell.TH hiding (Name)
import Language.Haskell.TH.Syntax hiding (Name)
import Language.Haskell.TH.Quote

import Test.QuickCheck

newtype Name = Name { getName :: Packaged Intl.Name }
    deriving (Eq,Ord,Data,Generic,Hashable)
newtype InternalName = InternalName { getInternalName :: Packaged Intl.InternalName }
    deriving (Eq,Ord,Data,Generic,Hashable)

name :: Iso' Name Intl.Name
name = iso getName Name . unpackaged
internal :: Iso' InternalName Intl.InternalName
internal = iso getInternalName InternalName . unpackaged

class (IsBaseName n,Hashable n) => IsName n where
    fromInternal :: InternalName -> n
    fromName :: Name -> n

asInternal :: IsName n => n -> InternalName
--asInternal = asInternal'
asInternal = view (from internal) . asInternal'

asName :: IsName n => n -> Name    
--asName = asName'
asName = view (from name) . asName'

addBackslash :: Name -> Name
addBackslash = name %~ Intl.addBackslash

instance IsBaseName Name where
    render = render . view name
    generateNames = fmap (view $ from name) . generateNames . view name
    fromString''  = view (from name) . fromString''
    addPrime = name %~ addPrime
    language = fmap (view $ from name) . language . fmap (view name)
    z3Name = view (from name) . z3Name
    texName = view (from name) . texName
    asName' = asName' . view name
    asInternal' = asInternal' . view name
instance IsBaseName InternalName where
    render = render . view internal
    generateNames = fmap (view $ from internal) . generateNames . view internal
    fromString''  = view (from internal) . fromString''
    addPrime = internal %~ addPrime
    language = fmap (view $ from internal) . language . fmap (view internal)
    z3Name = view (from internal) . z3Name
    texName = view (from internal) . texName
    asName' = asName' . view internal
    asInternal' = asInternal' . view internal


instance Show Name where
    show = show . view unpackaged . getName

instance Show InternalName where
    show = show . view unpackaged . getInternalName


makeName :: Pre => String -> Name
makeName = view (from name) . Intl.makeName

addSuffix :: String -> InternalName -> InternalName
addSuffix suf = internal %~ Intl.addSuffix suf

setSuffix :: Pre => String -> Name -> Name
setSuffix suf = name %~ Intl.setSuffix suf

dropSuffix :: InternalName -> InternalName
dropSuffix = internal %~ Intl.dropSuffix

reserved :: String -> Int -> InternalName
reserved = fmap (view $ from internal) . Intl.reserved

isName :: String -> Either [String] Name
isName = fmap (view $ from name) . Intl.isName

isName' :: String -> Maybe Name
isName' = fmap (view $ from name) . Intl.isName'

instance NFData Name where
instance NFData InternalName where
instance Serialize Name where
instance Serialize InternalName where

instance Arbitrary Name where
    arbitrary = view (from name) <$> arbitrary
instance Arbitrary InternalName where
    arbitrary = view (from internal) <$> arbitrary

instance Lift Name where
    lift n = [e| $(lift $ n^.name) ^. from name |]

instance Lift InternalName where
    lift n = [e| $(lift $ n^.internal) ^. from internal |]

instance IsName Name where
    fromInternal = asName
    fromName = id
instance IsName InternalName where
    fromInternal = id
    fromName = asInternal

smt :: QuasiQuoter
smt = QuasiQuoter
    { quoteExp  = \str -> [e| fromName . view (from name) $ $(parseZ3Name str) |]
    , quotePat  = undefined
    , quoteDec  = undefined
    , quoteType = undefined }

tex :: QuasiQuoter
tex = QuasiQuoter
    { quoteExp  = \str -> [e| view (from name) $ $(parseTexName str) |]
    , quotePat  = undefined
    , quoteDec  = undefined
    , quoteType = undefined }

parseZ3Name :: String -> ExpQ
parseZ3Name str = either (fail . unlines) lift $ Intl.isZ3Name str

parseTexName :: String -> ExpQ
parseTexName str = either (fail . unlines) lift $ Intl.isName str

isZ3Name :: String -> Either [String] Name
isZ3Name = fmap (view $ from name) . Intl.isZ3Name
