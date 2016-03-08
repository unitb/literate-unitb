{-# LANGUAGE StandaloneDeriving, TypeFamilies #-}
module Control.Invariant 
    ( HasInvariant(..), Checked, IsChecked(..)
    , Assert
    , mutate, mutate', create'
    , module Control.Exception.Assert
    , Controls(..)
    , view',(!.), views'
    , use', uses'
    , HasPrefix(..)
    , (===), isSubsetOf', isProperSubsetOf'
    , isSubmapOf',isProperSubmapOf'
    , member'
    , relation
    , trading
    , provided, providedM
    , assertFalse, assertFalse'
    , Invariant, (##) )
where

import Control.DeepSeq
import Control.Exception
import Control.Exception.Assert
import Control.Lens
import Control.Monad.State
import Control.Monad.RWS
import Control.Precondition

import Data.Default
import Data.Functor.Compose
import Data.Functor.Classes
import Data.List
import Data.Set (isSubsetOf,isProperSubsetOf,Set)
import Data.Typeable

import GHC.Stack.Utils

import PseudoMacros

import Text.Printf

import Data.Map.Class (isSubmapOf,isProperSubmapOf,member,IsMap,IsKey)

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
    updateCache :: a -> a
    updateCache = id

class HasInvariant b => IsChecked a b | a -> b where
    check :: Assert
          -> b -> a
    check' :: Assert
           -> b -> a
    content :: Assert
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
    default content' :: a ~ b => Getter a b
    content' = id

infixl 8 !.

(!.) :: Controls a b => a -> Getting c b c -> c
(!.) = flip view'

view' :: (Controls a b,MonadReader a m) => Getting c b c -> m c
view' ln = view $ content'.ln

views' :: (Controls a b,MonadReader a m) 
       => Getting d b c
       -> (c -> d)
       -> m d
views' ln f = views (content'.ln) f

use' :: (Controls a b,MonadState a m) => Getting c b c -> m c
use' ln = use $ content'.ln

uses' :: (Controls a b,MonadState a m) 
      => Getting d b c 
      -> (c -> d) 
      -> m d
uses' ln f = uses (content'.ln) f

instance Controls (Checked a) a where
    content' = to getChecked

instance (Functor f, Show a, Show1 f, Show1 g, HasInvariant (f (g a))) 
        => HasInvariant (Compose f g a) where
    invariant = invariant . getCompose
    updateCache = _Wrapped' %~ updateCache

instance HasInvariant a => IsChecked (Checked a) a where
    check arse = check' arse . updateCache
    check' arse x = Checked $ byPred arse msg (const $ null p) x x
        where
            msg = printf "invariant failure: \n%s" $ intercalate "\n" p
            p = map fst $ filter (not.snd) $ snd $ execRWS (runInvariant $ invariant x) [] ()
    content arse = iso getChecked (check arse)

trading :: (Functor f,Functor f')
        => Iso (Compose f (Compose g h) x) (Compose f' (Compose g' h') x')
               (Compose f g (h x)) (Compose f' g' (h' x'))
trading = iso (_Wrapped %~ fmap getCompose) (_Wrapped %~ fmap Compose)

instance Controls (Compose Checked f a) (f a) where
    content' = to getCompose . content'

instance HasInvariant (f a) => IsChecked (Compose Checked f a) (f a) where
    check arse = Compose . check arse
    check' arse  = Compose . check' arse
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

{-# INLINE isSubmapOf' #-}
isSubmapOf' :: (IsMap map,IsKey map k,Eq k,Eq a,Show (map k a)) => map k a -> map k a -> Invariant ()
isSubmapOf' = relation "/⊆" isSubmapOf

{-# INLINE isProperSubmapOf' #-}
isProperSubmapOf' :: (IsMap map,Eq k, Eq a,Show (map k a),IsKey map k) => map k a -> map k a -> Invariant ()
isProperSubmapOf' = relation "/⊂" isProperSubmapOf

{-# INLINE member' #-}
member' :: (Show k,Show (map k a),IsMap map,IsKey map k) => k -> map k a -> Invariant ()
member' = relation "/∈" member

relation :: (Show a,Show b) => String -> (a -> b -> Bool) -> a -> b -> Invariant ()
relation symb rel x y = printf "%s %s %s" (show x) symb (show y) ## (x `rel` y)

class HasPrefix m where
    withPrefix :: String -> m a -> m a
    
instance HasPrefix Invariant where
    withPrefix pre (Invariant cmd) = Invariant $ local (pre:) cmd

mutate :: IsChecked c a => Assert -> c -> State a k -> c
mutate arse x cmd = x & content arse %~ execState cmd 

mutate' :: (IsChecked c a,Monad m) => Assert -> StateT a m k -> StateT c m k
mutate' arse cmd = zoom (content arse) cmd

create' :: (IsChecked c a,Default a) => Assert -> State a k -> c
create' arse = check arse . flip execState def 

withStack :: CallStack -> Invariant a -> Invariant a
withStack cs = maybe id withPrefix $ stackTrace [$__FILE__] cs
