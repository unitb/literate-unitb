{-# LANGUAGE DeriveGeneric, DeriveDataTypeable #-}
module Logic.Label where

    -- Module
import Logic.Classes

    -- Libraries
import GHC.Generics 
import Data.Map hiding ( map )
import Data.Typeable

data Label = Lbl String
    deriving (Ord, Eq, Typeable, Generic)

instance Show Label where
    show (Lbl s) = s

label :: String -> Label
label s = Lbl s

symbol_table :: Named a => [a] -> Map String a
symbol_table xs = fromList $ map as_pair xs
