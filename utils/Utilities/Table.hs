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

import Control.Lens

import Data.Hashable
import Data.Typeable

import Prelude hiding (lookup,null,map,filter)

import Data.Map.Class


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
