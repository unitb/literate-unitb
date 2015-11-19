{-# LANGUAGE ImplicitParams, RankNTypes, TemplateHaskell #-}
module Utilities.Partial 
    ( module Utilities.Partial 
    , module Data.Maybe 
    , module Data.Either.Combinators
    , assert )
where

import Control.Exception.Assert
import Control.Lens

import Data.Either.Combinators hiding 
        ( fromRight',fromLeft'
        , mapLeft,mapRight
        , mapBoth )
import Data.Maybe hiding (fromJust)

import PseudoMacros

import Utilities.CallStack

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

(!) :: (?loc :: CallStack, Ixed m) 
    => m -> Index m -> IxValue m
(!) m x = fromJust' $ m^?ix x

type Assert = forall a. Bool -> a -> a

assertFalse :: Assert -> String -> a
assertFalse arse msg = assertMessage "False" msg (arse False) (error "false assertion (1)")

assertFalse' :: (?loc :: CallStack) => a
assertFalse' = provided False (error "false assertion (2)")

provided :: (?loc :: CallStack) => Bool -> a -> a
provided = provided' ?loc

assertWithCallStack :: CallStack -> String -> (a -> a) -> a -> a
assertWithCallStack cs tag = assertMessage tag
        (fromMaybe "" $ stackTrace [] cs)

provided' :: CallStack -> Bool -> a -> a
provided' cs b = assertMessage "Precondition" 
        (fromMaybe "" $ stackTrace [$__FILE__] cs) (assert b)

providedM :: (?loc :: CallStack) => Bool -> m a -> m a
providedM b cmd = do
        provided b () `seq` cmd
