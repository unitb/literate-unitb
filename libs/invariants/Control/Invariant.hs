{-# LANGUAGE StandaloneDeriving, TypeFamilies #-}
module Control.Invariant 
    ( HasInvariant(..), Checked, IsChecked(..)
    , mutate, mutate', create'
    , Controls(..)
    , view',(!.), views'
    , use', uses'
    , HasPrefix(..)
    , (===), isSubsetOf', isProperSubsetOf'
    , relation
    , trading, holds
    , invariantMessage
    , provided, providedM
    , assertFalse'
    , Pre
    , IsAssertion(..)
    , checkAssert
    , checkAssertM
    , Invariant, (##) )
where

import Control.DeepSeq
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

import Test.QuickCheck hiding ((===))

import Text.Printf.TH

newtype Checked a = Checked { getChecked :: a }
    deriving (Eq,Ord,NFData,Functor,Foldable,Traversable,Typeable)

instance Show a => Show (Checked a) where
    show (Checked x) = show x

instance Eq1 Checked where
    eq1 (Checked a) (Checked b) = a == b

instance Show1 Checked where
    showsPrec1 = showsPrec

deriving instance Typeable Compose

newtype InvariantM a = Invariant { runInvariant :: RWS [String] [String] () a }
    deriving (Functor,Applicative,Monad)

type Invariant = InvariantM ()

class Show a => HasInvariant a where
    invariant :: a -> Invariant
    updateCache :: a -> a
    updateCache = id

class HasInvariant b => IsChecked a b | a -> b where
    check :: Pre
          => b -> a
    check' :: Pre
           => b -> a
    content :: Pre
            => Iso' a b

class IsAssertion a where
    toInvariant :: a -> Invariant
    fromBool :: Bool -> a

instance (a ~ ()) => Testable (InvariantM a) where
    property p = conjoin (map (`counterexample` property False) xs)
        where
            xs = invariantResults p

instance IsAssertion Bool where
    toInvariant b = Invariant $ do
        p <- ask
        unless b $ tell [intercalate " - " $ reverse p]
    fromBool = id

instance (a ~ ()) => IsAssertion (InvariantM a) where
    toInvariant b = b >> return ()
    fromBool = toInvariant

instance Monoid a => Monoid (InvariantM a) where
    mempty = return mempty
    mappend = liftM2 mappend
    mconcat = fmap mconcat . sequence

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
    check    = check' . updateCache
    check' x = Checked $ checkAssert (invariant x) (show x) x
        where
            -- msg = [printf|invariant failure: \n%s|] $ intercalate "\n" p
            -- p = map fst $ filter (not.snd) $ snd $ execRWS (runInvariant $ invariant x) [] ()
    content = iso getChecked check

holds :: IsAssertion prop => prop -> Bool
holds prop = null $ snd $ execRWS (runInvariant $ toInvariant prop) [] ()

checkAssertM :: (IsAssertion a,Monad m,Pre) => a -> String -> m ()
checkAssertM p msg = checkAssert p msg (return ())

checkAssert :: (IsAssertion a,Pre) => a -> String -> b -> b
checkAssert prop detail x = providedMessage' ?loc "Invariants" msg (null p) x
        where
            msg = [printf|assertion failure: \n%s\n%s|] (intercalate "\n" p) (take 1000 detail)
            p = invariantResults prop

invariantResults :: IsAssertion a => a -> [String]
invariantResults prop = 
        map (take 1000) . snd $ execRWS (runInvariant $ toInvariant prop) [] ()

invariantMessage :: IsAssertion a => a -> String
invariantMessage prop 
        | null p    = "pass"
        | otherwise = intercalate "\n" $ "failed" : p
    where
        p = invariantResults prop

trading :: (Functor f,Functor f')
        => Iso (Compose f (Compose g h) x) (Compose f' (Compose g' h') x')
               (Compose f g (h x)) (Compose f' g' (h' x'))
trading = iso (_Wrapped %~ fmap getCompose) (_Wrapped %~ fmap Compose)

instance Controls (Compose Checked f a) (f a) where
    content' = to getCompose . content'

instance HasInvariant (f a) => IsChecked (Compose Checked f a) (f a) where
    check   = Compose . check
    check'  = Compose . check'
    content = iso getCompose Compose . content

instance NFData (f (g x)) => NFData (Compose f g x) where
    rnf = rnf . getCompose

infixr 0 ##

(##) :: (IsAssertion b, Pre) => String -> b -> Invariant
(##) tag b = withStack ?loc $ withPrefix tag $ toInvariant b

infix 4 ===

(===) :: (Eq a, Show a) => a -> a -> Invariant
(===) = relation "/=" (==)

isSubsetOf' :: (Ord a,Show a) => Set a -> Set a -> Invariant
isSubsetOf' = relation "/⊆" isSubsetOf

isProperSubsetOf' :: (Ord a,Show a) => Set a -> Set a -> Invariant
isProperSubsetOf' = relation "/⊂" isProperSubsetOf

relation :: (Show a,Show b) 
         => String 
         -> (a -> b -> Bool) 
         -> a -> b -> Invariant
relation symb rel x y = [printf|%s %s %s|] (show x) symb (show y) ## (x `rel` y)

class HasPrefix m where
    withPrefix :: String -> m a -> m a
    
instance HasPrefix InvariantM where
    withPrefix pre (Invariant cmd) = Invariant $ local (pre:) cmd

instance (HasInvariant a,Arbitrary a) => Arbitrary (Checked a) where
    arbitrary = check' <$> arbitrary
    shrink = fmap check' . shrink . getChecked

mutate :: (IsChecked c a,Pre)
       => c -> State a k -> c
mutate x cmd = x & content %~ execState cmd 

mutate' :: (IsChecked c a,Monad m,Pre) => StateT a m k -> StateT c m k
mutate' = zoom content

create' :: (IsChecked c a,Default a,Pre) => State a k -> c
create' = check . flip execState def 

withStack :: CallStack -> InvariantM a -> InvariantM a
withStack cs = maybe id withPrefix $ stackTrace [$__FILE__] cs
