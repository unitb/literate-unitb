{-# LANGUAGE DeriveGeneric, DeriveDataTypeable #-}

module UnitB.Label where

import GHC.Generics 
import Data.Map hiding ( map )
import Data.Typeable

data Label = Lbl String
    deriving (Ord, Eq, Typeable, Generic)

instance Show Label where
    show (Lbl s) = s

label s = Lbl s

symbol_table :: Named a => [a] -> Map String a
symbol_table xs = fromList $ map as_pair xs

class Named n where
    name    :: n -> String
    as_pair :: n -> (String, n)
    as_pair n = (name n, n)
