module Utilities.HeterogenousEquality where

import Data.Typeable 

h_equal :: (Typeable a, Typeable b, Eq a) => a -> b -> Bool
h_equal x y = Just x == cast y

h_compare :: (Typeable a, Typeable b, Ord a) => a -> b -> Ordering
h_compare x y = case cast y of
                    Just y -> compare x y
                    Nothing -> compare (typeOf x) (typeOf y)
