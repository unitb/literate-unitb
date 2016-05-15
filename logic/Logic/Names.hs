{-# LANGUAGE TypeFamilies, CPP #-}
module Logic.Names 
    ( IsBaseName(..) 
    , HasNames(..) 
    , NonEmpty((:|))
    , nameType
    , Name(..), InternalName(..)
    , isZ3Name, isZ3Name'
    , Translatable(..)
    , IsName(..)
    , asInternal, asName
    , makeName
    , makeZ3Name
    , make, make'
    , isName, isName'
    , fromString'
    , fresh
    , reserved
    , z3Render
    , dropSuffix 
    , addSuffix
    , addBackslash
    , setSuffix
    , smt, tex
    , Encoding(..)
    , run_props     
    )
where

    -- Modules
#ifdef __PACKAGED_NAMES__
import Logic.Names.Packaged as Names
#else
import Logic.Names.Internals as Names
#endif

import Control.Lens
import Data.Typeable

class IsName n => HasNames a n | a -> n where
    type SetNameT n' a :: *
    namesOf :: IsName n' 
            => Traversal a (SetNameT n' a)
                         n n'

nameType :: String
nameType = tyConModule $ fst $ splitTyConApp $ typeRep (Proxy :: Proxy Name)
