{-# LANGUAGE StandaloneDeriving, ImplicitParams #-}
module Utilities.Invariant 
    ( HasInvariant(..), Checked, IsChecked(..)
    , Assert, fromJust', mutate, create'
    , module Control.Exception.Assert
    , Controls(..), view',(!.) 
    , HasPrefix(..)
    , (===), isSubsetOf', isProperSubsetOf'
    , isSubmapOf',isProperSubmapOf'
    , relation, provided
    , fromJust''
    , assertFalse, assertFalse'
    , Invariant, (##) )
where

import Control.DeepSeq
import Control.Exception
import Control.Exception.Assert
import Control.Lens
import Control.Monad.State
import Control.Monad.RWS

import Data.Default
import Data.Functor.Compose
import Data.Functor.Classes
import Data.List
import Data.Map (isSubmapOf,isProperSubmapOf,Map)
import Data.Maybe
import Data.Set (isSubsetOf,isProperSubsetOf,Set)
import Data.Typeable

import GHC.Stack

import PseudoMacros

import Text.Printf

import Utilities.CallStack
import Utilities.Lens

newtype Checked a = Checked { getChecked :: a }
    deriving (Eq,Ord,NFData,Functor,Foldable,Traversable,Typeable)

instance Show a => Show (Checked a) where
    show (Checked x) = show x

instance Eq1 Checked where
    eq1 (Checked a) (Checked b) = a == b

instance Show1 Checked where
    showsPrec1 = showsPrec

deriving instance Typeable Compose

newtype Invariant a = Invariant { runInvariant :: RWS [String] [(String,Bool)] () a }
    deriving (Functor,Applicative,Monad)

class Show a => HasInvariant a where
    invariant :: a -> Invariant ()

class HasInvariant b => IsChecked a b | a -> b where
    check :: (Bool -> b -> b)
          -> b -> a
    content :: (Bool -> b -> b)
            -> Iso' a b

class IsAssertion a where
    toInvariant :: a -> Invariant ()

instance IsAssertion Bool where
    toInvariant b = Invariant $ do
        p <- ask
        tell [(intercalate " - " $ reverse p, b)]

instance IsAssertion (Invariant a) where
    toInvariant b = b >> return ()

class Controls a b | a -> b where
    content' :: Getter a b
    default content' :: Getter a a
    content' = id

infixl 8 !.

(!.) :: Controls a b => a -> Getting c b c -> c
(!.) = flip view'

view' :: (Controls a b,MonadReader a m) => Getting c b c -> m c
view' ln = view $ content'.ln

instance Controls (Checked a) a where
    content' = to getChecked

instance HasInvariant a => IsChecked (Checked a) a where
    check arse x = Checked $ byPred arse (printf "invariant failure: \n%s" $ intercalate "\n" p) (const $ null p) x x 
        where
            p = map fst $ filter (not.snd) $ snd $ execRWS (runInvariant $ invariant x) [] ()
    content arse = iso getChecked (check arse)

instance Controls (Compose Checked f a) (f a) where
    content' = to getCompose . content'

instance HasInvariant (f a) => IsChecked (Compose Checked f a) (f a) where
    check arse = Compose . check arse
    content arse = iso getCompose Compose . content arse

instance NFData (f (g x)) => NFData (Compose f g x) where
    rnf = rnf . getCompose

infixr 0 ##

(##) :: (IsAssertion b, ?loc :: CallStack) => String -> b -> Invariant ()
(##) tag b = withStack ?loc $ withPrefix tag $ toInvariant b

infix 4 ===

(===) :: (Eq a, Show a) => a -> a -> Invariant ()
(===) = relation "/=" (==)

isSubsetOf' :: (Ord a,Show a) => Set a -> Set a -> Invariant ()
isSubsetOf' = relation "/⊆" isSubsetOf

isProperSubsetOf' :: (Ord a,Show a) => Set a -> Set a -> Invariant ()
isProperSubsetOf' = relation "/⊂" isProperSubsetOf

isSubmapOf' :: (Ord k,Eq a,Show k,Show a) => Map k a -> Map k a -> Invariant ()
isSubmapOf' = relation "/⊆" isSubmapOf

isProperSubmapOf' :: (Ord k,Eq a,Show k,Show a) => Map k a -> Map k a -> Invariant ()
isProperSubmapOf' = relation "/⊂" isProperSubmapOf

relation :: Show a => String -> (a -> a -> Bool) -> a -> a -> Invariant ()
relation symb rel x y = printf "%s %s %s" (show x) symb (show y) ## (x `rel` y)

class HasPrefix m where
    withPrefix :: String -> m a -> m a
    
instance HasPrefix Invariant where
    withPrefix pre (Invariant cmd) = Invariant $ local (pre:) cmd

mutate :: IsChecked c a => Assert -> c -> State a k -> c
mutate arse x cmd = x & content arse %~ execState cmd 

withStack :: CallStack -> Invariant a -> Invariant a
withStack cs = maybe id withPrefix $ stackTrace [$__FILE__] cs

provided :: (?loc :: CallStack) => Bool -> a -> a
provided b = assertMessage "Precondition" 
        (fromMaybe "" $ stackTrace [$__FILE__] ?loc) (assert b)

create' :: (IsChecked c a,Default a) => Assert -> State a k -> c
create' arse = check arse . create 

type Assert = forall a. Bool -> a -> a

fromJust' :: (?loc :: CallStack) => Maybe a -> a
fromJust' (Just x)   = x
fromJust' Nothing = assertFalse' "Nothing"

fromJust'' :: Assert -> Maybe a -> a
fromJust'' _ (Just x) = x
fromJust'' arse Nothing = assertFalse arse "Nothing"

assertFalse :: Assert -> String -> a
assertFalse arse msg = assertMessage "False" msg (arse False) (error "false assertion (1)")

assertFalse' :: (?loc :: CallStack) => a
assertFalse' = provided False (error "false assertion (2)")
