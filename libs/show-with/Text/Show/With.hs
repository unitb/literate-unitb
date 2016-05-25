module Text.Show.With where

import Data.Functor.Classes

import GHC.Generics.Instances

newtype ShowString' a = ShowString a
type ShowString = ShowString' String
type ShowSString = ShowString' (String -> String)

instance Show ShowString where
    showsPrec _ (ShowString x) = (x ++)

instance Show ShowSString where
    showsPrec _ (ShowString f) = f

showWith' :: (Functor f, Show1 f)
          => (a -> ShowS)
          -> f a -> String
showWith' f = ($ "") . showsWith f

showWith :: (Functor f, Show1 f)
         => (a -> String)
         -> f a -> String
showWith f = showWith' ((++) . f)

showsWith :: (Functor f, Show1 f)
          => (a -> ShowS)
          -> f a -> ShowS
showsWith f = shows1 . fmap (ShowString . f)
