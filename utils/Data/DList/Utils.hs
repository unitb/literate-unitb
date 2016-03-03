module Data.DList.Utils where

import Control.Lens

import Data.DList as D
import Data.List  as L

intercalate :: String -> [DList Char] -> DList Char
intercalate xs xss = D.concat (intersperse (D.fromList xs) xss)

concatMap :: (a -> DList b) 
          -> [a]
          -> DList b
concatMap f = D.concat . L.map f

asList :: Iso (DList a) (DList b) [a] [b]
asList = iso D.toList D.fromList
