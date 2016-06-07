{-# LANGUAGE RankNTypes
        , TemplateHaskell
        , ImplicitParams
        , ConstraintKinds #-}
module Control.Precondition 
    ( module Control.Precondition 
    , module Data.Maybe 
    , module Data.Either.Combinators
    , Loc(..) )
where

import Control.Exception
import Control.Exception.Assert (assertMessage)
import Control.Lens

import Data.Either.Combinators hiding 
        ( fromRight',fromLeft'
        , mapLeft,mapRight
        , mapBoth, isRight, isLeft )
import Data.List.NonEmpty
import Data.Maybe hiding (fromJust)

import GHC.Stack.Utils

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

import PseudoMacros

import Text.Printf

import GHC.Generics.Instances ()

fromJust' :: Pre => Maybe a -> a
fromJust' (Just x)   = x
fromJust' Nothing = assertFalse' "Nothing"

fromRight' :: Pre => Either a b -> b
fromRight' (Right x) = x
fromRight' (Left _)  = assertFalse' "Left"


fromLeft' :: Pre => Either a b -> a
fromLeft' (Left x) = x
fromLeft' (Right _)  = assertFalse' "Right"


nonEmpty' :: Pre => [a] -> NonEmpty a
nonEmpty' (x : xs) = x :| xs
nonEmpty' []    = assertFalse' "empty list cast as non empty"

(!) :: (Pre, Ixed m) 
    => m -> Index m -> IxValue m
(!) m x = fromJust' $ m^?ix x

byPred :: (Show x,Pre) 
       => String -> (x -> Bool) -> x -> a -> a
byPred msg p x = providedMessage' ?loc "byPred" (msg ++ "\n" ++ show x) (p x)

byEq :: (Eq x, Show x,Pre) => String -> x -> x -> a -> a
byEq msg = byRel' msg (==) "≠"

byOrd :: (Ord x, Show x,Pre) => String -> Ordering -> x -> x -> a -> a
byOrd msg ord = byRel' msg (\x y -> ord == compare x y) symb
    where
        symb = case ord of
                    LT -> "≮"
                    GT -> "≯"
                    EQ -> "≠"

byRel :: (Show a,Pre) => String -> (a -> a -> Bool) -> a -> a -> x -> x
byRel msg rel = byRel' msg rel "/rel/"

byRel' :: (Show a,Pre) => String -> (a -> a -> Bool) -> String -> a -> a -> x -> x
byRel' tag rel symb x0 x1 r = providedMessage' ?loc tag
    (show x0 ++ " " ++ symb ++ " " ++ show x1) (x0 `rel` x1) r

type Pre = (?loc :: CallStack)


assertFalse' :: Pre => String -> a
assertFalse' msg = providedMessage' (?loc) "assertion" msg False (error "false assertion: ")

undefined' :: Pre => a
undefined' = provided False (error "undefined")

assertFalseMessage :: Pre => String -> a
assertFalseMessage msg = providedMessage' ?loc "False assert" msg False (error "false assertion (2)")

provided :: Pre => Bool -> a -> a
provided = provided' ?loc




provided' :: CallStack -> Bool -> a -> a
provided' cs b = assertMessage "Precondition" 
        (fromMaybe "" $ stackTrace [$__FILE__] cs) (assert b)

providedMessage' :: CallStack -> String -> String -> Bool -> a -> a
providedMessage' cs tag msg b = assertMessage tag
        (fromMaybe "" (stackTrace [$__FILE__] cs) ++ "\n" ++ msg) (assert b)

providedM :: Pre => Bool -> m a -> m a
providedM b cmd = do
        provided b () `seq` cmd

locMsg :: Loc -> String
locMsg loc = printf "%s:%d:%d" (loc_filename loc) (fst $ loc_start loc) (snd $ loc_end loc)

withLoc :: Name -> ExpQ
withLoc fun = do
    loc <- location
    [e| $(varE fun) $(lift loc) |]
