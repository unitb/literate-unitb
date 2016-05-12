{-# LANGUAGE TypeFamilies, ScopedTypeVariables
    , BangPatterns, CPP #-}
module Utilities.Table 
    ( Table
    , Hashable
    , tableToList
    , tableElems
    , tableType
    , curryMap, uncurryMap
    , curriedMap
    )
where

--import Control.Arrow
--import Control.DeepSeq
import Control.Lens
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

import Data.Map.Class

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

type Table = HashMap
#else
import qualified Data.Map as M
type Table = M.Map

#endif
#endif
#endif

tableType :: String
tableType = tyConModule $ fst $ splitTyConApp $ typeRep (Proxy :: Proxy (Table Int Int))

uncurryMap :: (IsKey Table a,IsKey Table b)
           => Table a (Table b c)
           -> Table (a,b) c
uncurryMap m = fromList [ ((x,y),k) | (x,xs) <- toList m, (y,k) <- toList xs ]

curryMap :: (IsKey Table a,IsKey Table b)
         => Table (a,b) c
         -> Table a (Table b c)
curryMap m = fromList <$> fromListWith (++) [ (x,[(y,k)]) | ((x,y),k) <- toList m ]

curriedMap :: (IsKey Table a,IsKey Table b,IsKey Table x,IsKey Table y)
           => Iso (Table (a,b) c) (Table (x,y) z) 
                  (Table a (Table b c)) (Table x (Table y z))
curriedMap = iso curryMap uncurryMap
