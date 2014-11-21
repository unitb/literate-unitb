module Document.Pipeline where

import Control.Arrow
import qualified Control.Category as C

import Data.Set

data Pipeline m a b = Pipeline (Set String) (a -> m b)

instance Monad m => C.Category (Pipeline m) where
    id = Pipeline empty return
    Pipeline xs f . Pipeline ys g = Pipeline (xs `union` ys) $ (>>= f) . g

instance Monad m => Arrow (Pipeline m) where
    arr f = Pipeline empty $ return . f
    first (Pipeline xs f) = Pipeline xs $ \(x,y) -> f x >>= \z -> return (z,y)
