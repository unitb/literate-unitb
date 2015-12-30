{-# LANGUAGE TypeFamilies #-}
module Logic.Names 
    ( Name, InternalName
    , IsName
    , IsBaseName(..) 
    , HasNames(..) 
    , asInternal
    , asName
    , makeName
    , Intl.make
    , Intl.make'
    , Intl.Translatable  (..)
    , addSuffix
    , addBackslash
    , reserved
    , setSuffix
    , dropSuffix
    , assert
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

import Utilities.Packaged
import Utilities.Partial

    -- Libraries
import Control.DeepSeq
import Control.Lens

import Data.Data
import Data.Serialize
import Data.List.NonEmpty

import GHC.Generics (Generic)

import Language.Haskell.TH hiding (Name)
import Language.Haskell.TH.Syntax hiding (Name)
import Language.Haskell.TH.Quote

import Test.QuickCheck

newtype Name = Name { getName :: Packaged Intl.Name }
    deriving (Eq,Ord,Data,Generic)
newtype InternalName = InternalName { getInternalName :: Packaged Intl.InternalName }
    deriving (Eq,Ord,Data,Generic)

name :: Iso' Name Intl.Name
name = iso getName Name . unpackaged
internal :: Iso' InternalName Intl.InternalName
internal = iso getInternalName InternalName . unpackaged

class IsBaseName n => IsName n where
    fromInternal :: InternalName -> n
    fromName :: Name -> n

asInternal :: IsName n => n -> InternalName
asInternal = view (from internal) . asInternal'

asName :: IsName n => n -> Name    
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

instance IsName Name where
    fromInternal = asName
    fromName = id
instance IsName InternalName where
    fromInternal = id
    fromName = asInternal

instance Show Name where
    show = show . view unpackaged . getName

instance Show InternalName where
    show = show . view unpackaged . getInternalName

class IsName n => HasNames a n | a -> n where
    type SetNameT n' a :: *
    namesOf :: IsName n' 
            => Traversal a (SetNameT n' a)
                         n n'

makeName :: Assert -> String -> Name
makeName arse = view (from name) . Intl.makeName arse

addSuffix :: String -> InternalName -> InternalName
addSuffix suf = internal %~ Intl.addSuffix suf

setSuffix :: Assert -> String -> Name -> Name
setSuffix arse suf = name %~ Intl.setSuffix arse suf

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
