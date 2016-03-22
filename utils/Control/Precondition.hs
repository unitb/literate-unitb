{-# LANGUAGE RankNTypes, TemplateHaskell, ImplicitParams #-}
module Control.Precondition 
    ( module Control.Precondition 
    , module Control.Exception.Assert
    , module Data.Maybe 
    , module Data.Either.Combinators
    , Loc(..)
    , CallStack )
where

import Control.Exception.Assert
import Control.Lens

import Data.Either.Combinators hiding 
        ( fromRight',fromLeft'
        , mapLeft,mapRight
        , mapBoth )
import Data.List.NonEmpty
import Data.Maybe hiding (fromJust)

import GHC.Stack.Utils

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

import PseudoMacros

import Text.Printf

import GHC.Generics.Instances ()

fromJust' :: (?loc :: CallStack) => Maybe a -> a
fromJust' (Just x)   = x
fromJust' Nothing = assertFalse' "Nothing"

fromRight' :: (?loc :: CallStack) => Either a b -> b
fromRight' (Right x) = x
fromRight' (Left _)  = assertFalse' "Left"

fromRight'' :: Assert -> Either a b -> b
fromRight'' _ (Right x) = x
fromRight'' arse (Left _)  = assertFalse arse "Left"

fromLeft' :: (?loc :: CallStack) => Either a b -> a
fromLeft' (Left x) = x
fromLeft' (Right _)  = assertFalse' "Right"

fromJust'' :: Assert -> Maybe a -> a
fromJust'' _ (Just x) = x
fromJust'' arse Nothing = assertFalse arse "Nothing"

nonEmpty' :: Assert -> [a] -> NonEmpty a
nonEmpty' _ (x : xs) = x :| xs
nonEmpty' arse []    = assertFalse arse "empty list cast as non empty"

(!) :: (?loc :: CallStack, Ixed m) 
    => m -> Index m -> IxValue m
(!) m x = fromJust' $ m^?ix x

type Assert = forall a. Bool -> a -> a

assertFalse :: Assert -> String -> a
assertFalse arse msg = assertMessage "False" msg (arse False) (error "false assertion (1)")

assertFalse' :: (?loc :: CallStack) => a
assertFalse' = provided False (error "false assertion (2)")

assertFalseMessage :: (?loc :: CallStack) => String -> a
assertFalseMessage msg = providedMessage' ?loc msg False (error "false assertion (2)")

provided :: (?loc :: CallStack) => Bool -> a -> a
provided = provided' ?loc

withCallStack :: (?loc :: CallStack) => Assert -> Assert
withCallStack arse b = assertWithCallStack ?loc "" (arse b)

withMessage :: (?loc :: CallStack) => String -> String -> Assert -> Assert
withMessage tag msg arse b = assertWithCallStack ?loc (tag ++ " " ++ msg) $ arse b

assertWithCallStack :: CallStack -> String -> (a -> a) -> a -> a
assertWithCallStack cs tag = assertMessage tag
        (fromMaybe "" $ stackTrace [$__FILE__] cs)

provided' :: CallStack -> Bool -> a -> a
provided' cs b = assertMessage "Precondition" 
        (fromMaybe "" $ stackTrace [$__FILE__] cs) (assert b)

providedMessage' :: CallStack -> String -> Bool -> a -> a
providedMessage' cs msg b = assertMessage "Precondition" 
        (fromMaybe "" (stackTrace [$__FILE__] cs) ++ "\n" ++ msg) (assert b)

providedM :: (?loc :: CallStack) => Bool -> m a -> m a
providedM b cmd = do
        provided b () `seq` cmd

locMsg :: Loc -> String
locMsg loc = printf "%s:%d:%d" (loc_filename loc) (fst $ loc_start loc) (snd $ loc_end loc)

withLoc :: Name -> ExpQ
withLoc fun = do
    loc <- location
    [e| $(varE fun) $(lift loc) |]
