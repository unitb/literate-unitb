{-# LANGUAGE TypeFamilies, ScopedTypeVariables
    , BangPatterns, CPP #-}
module Utilities.Table 
    ( Table
    , Hashable
    , tableToList
    , tableElems
    , tableType
    )
where

--import Control.Arrow
--import Control.DeepSeq
--import Control.Lens
--import Control.Monad

--import Data.Array
--import Data.Default
--import Data.Function
import Data.Hashable
import Data.Typeable
--import qualified Data.IntMap as IM
--import qualified Data.Map as IM
--import qualified Data.Map as M
--import qualified Data.Maybe as My
--import qualified Data.List as L
--import qualified Data.List.Ordered as Ord
--import Data.List.NonEmpty as NE (NonEmpty(..)) 
--import qualified Data.List.NonEmpty as NE
--import Data.Semigroup
--import Data.Serialize
--import qualified Data.Set as S
--import Data.Array.Unboxed

--import GHC.Exts (Int(..))
--import GHC.Prim

import Prelude hiding (lookup,null,map,filter)

--import Utilities.Instances
--import Utilities.Map

--import Test.QuickCheck hiding (shrinkList)
--import Test.QuickCheck.Function

#ifdef __HASHED_KEYS__

import Utilities.Table.HashKey as Table

type Table = MapWithHash
#else
#ifdef __BUCKET_TABLE__ 

import Utilities.Table.BucketTable as Table

type Table = HashTable
#else
#ifdef __HASH_MAP__ 

import Utilities.Table.HashMap as Table

type Table = HashMap
#else
import Data.Map as M
type Table = Map

tableToList :: Table k a -> [(k, a)]
tableToList = M.toList

tableElems :: Table k a -> [a]
tableElems = M.elems

#endif
#endif
#endif

tableType :: String
tableType = tyConModule $ fst $ splitTyConApp $ typeRep (Proxy :: Proxy (Table Int Int))
