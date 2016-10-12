{-# LANGUAGE TypeFamilies, ScopedTypeVariables
    , BangPatterns, CPP #-}
module Utilities.Map 
    ( Map
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

import Utilities.Map.HashKey as Map

type Map = MapWithHash
#else
#ifdef __BUCKET_TABLE__ 

import Utilities.Map.BucketMap as Map

type Map = HashMap
#else
#ifdef __HASH_MAP__ 

type Map = HashMap
#else
import qualified Data.Map as M
type Map = M.Map

#endif
#endif
#endif

tableType :: String
tableType = tyConModule $ fst $ splitTyConApp $ typeRep (Proxy :: Proxy (Map Int Int))

uncurryMap :: (IsKey Map a,IsKey Map b)
           => Map a (Map b c)
           -> Map (a,b) c
uncurryMap m = fromList [ ((x,y),k) | (x,xs) <- toList m, (y,k) <- toList xs ]

curryMap :: (IsKey Map a,IsKey Map b)
         => Map (a,b) c
         -> Map a (Map b c)
curryMap m = fromList <$> fromListWith (++) [ (x,[(y,k)]) | ((x,y),k) <- toList m ]

curriedMap :: (IsKey Map a,IsKey Map b,IsKey Map x,IsKey Map y)
           => Iso (Map (a,b) c) (Map (x,y) z) 
                  (Map a (Map b c)) (Map x (Map y z))
curriedMap = iso curryMap uncurryMap
