module Utilities.HeterogenousEquality where

import Data.Typeable 

h_equal :: (Typeable a, Typeable b, Eq a) => a -> b -> Bool
h_equal x y = Just x == cast y