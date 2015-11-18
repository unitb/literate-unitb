{-# LANGUAGE ImplicitParams #-}
module Utilities.Partial 
    ( module Utilities.Partial 
    , module Data.Maybe 
    , module Data.Either.Combinators )
where

import Data.Either.Combinators hiding 
        ( fromRight',fromLeft'
        , mapLeft,mapRight
        , mapBoth )
import Data.Maybe hiding (fromJust)

import Utilities.CallStack
import Utilities.Invariant

fromJust' :: (?loc :: CallStack) => Maybe a -> a
fromJust' (Just x)   = x
fromJust' Nothing = assertFalse' "Nothing"

fromRight' :: (?loc :: CallStack) => Either a b -> b
fromRight' (Right x) = x
fromRight' (Left _)  = assertFalse' "Left"

fromLeft' :: (?loc :: CallStack) => Either a b -> a
fromLeft' (Left x) = x
fromLeft' (Right _)  = assertFalse' "Right"

fromJust'' :: Assert -> Maybe a -> a
fromJust'' _ (Just x) = x
fromJust'' arse Nothing = assertFalse arse "Nothing"

