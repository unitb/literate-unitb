{-# LANGUAGE TypeOperators #-}
module GHC.Generics.Utils
    ( left,right
    , module GHC.Generics
    , module GHC.Generics.Lens )
where

import Control.Lens

import GHC.Generics hiding (from,to)
import GHC.Generics.Lens

left :: Lens ((a0 :*: b) p) ((a1 :*: b) p) (a0 p) (a1 p)
left f (x :*: y) = (:*: y) <$> f x

right :: Lens ((a :*: b0) p) ((a :*: b1) p) (b0 p) (b1 p)
right f (x :*: y) = (x :*:) <$> f y
