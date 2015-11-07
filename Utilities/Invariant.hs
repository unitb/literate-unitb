
{-# LANGUAGE StandaloneDeriving #-}
module Utilities.Invariant 
    ( HasInvariant(..), Checked, IsChecked(..)
    , Assert, fromJust', mutate
    , module Control.Exception.Assert
    , Controls(..), view',(!.) )
where

import Control.DeepSeq
import Control.Exception
import Control.Exception.Assert
import Control.Lens
import Control.Monad.State

import Data.Functor.Compose
import Data.Functor.Classes
import Data.List
import Data.Typeable

import Text.Printf

--import Utilities.Trace

newtype Checked a = Checked { getChecked :: a }
    deriving (Eq,Ord,NFData,Functor,Foldable,Traversable,Typeable)

instance Show a => Show (Checked a) where
    show (Checked x) = show x

instance Eq1 Checked where
    eq1 (Checked a) (Checked b) = a == b

instance Show1 Checked where
    showsPrec1 = showsPrec

deriving instance Typeable Compose

class Show a => HasInvariant a where
    invariant :: a -> [(String,Bool)]

class HasInvariant b => IsChecked a b | a -> b where
    check :: (Bool -> b -> b)
          -> b -> a
    content :: (Bool -> b -> b)
            -> Iso' a b

class Controls a b | a -> b where
    content' :: Getter a b

infixl 8 !.

(!.) :: Controls a b => a -> Getting c b c -> c
(!.) = flip view'

view' :: Controls a b => Getting c b c -> a -> c
view' ln = view $ content'.ln

instance Controls (Checked a) a where
    content' = to getChecked

instance HasInvariant a => IsChecked (Checked a) a where
    check arse x = Checked $ byPred arse (printf "invariant failure: \n%s" $ intercalate "\n" p) (const $ null p) x x 
        where
            p = map fst $ filter (not.snd) $ invariant x
    content arse = iso getChecked (check arse)

instance Controls (Compose Checked f a) (f a) where
    content' = to getCompose . content'

instance HasInvariant (f a) => IsChecked (Compose Checked f a) (f a) where
    check arse = Compose . check arse
    content arse = iso getCompose Compose . content arse

instance NFData (f (g x)) => NFData (Compose f g x) where
    rnf = rnf . getCompose

mutate :: IsChecked c a => Assert -> c -> State a k -> c
mutate arse x cmd = x & content arse %~ execState cmd 

type Assert = forall a. Bool -> a -> a

fromJust' :: Assert -> String -> Maybe a -> a
fromJust' _ _ (Just x)   = x
fromJust' arse tag Nothing = assertFalse arse tag

assertFalse :: Assert -> String -> a
assertFalse arse msg = assertMessage "False" msg (arse False) (error "false assertion")
