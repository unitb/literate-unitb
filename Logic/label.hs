{-# LANGUAGE DeriveGeneric, DeriveDataTypeable #-}
module Logic.Label where

    -- Module
import Logic.Classes

    -- Libraries
import GHC.Generics 

import Data.List
import Data.Map hiding ( map, split )
import Data.String.Utils ( split )
import Data.Typeable

data Label = Lbl String
    deriving (Ord, Eq, Typeable, Generic)

instance Show Label where
    show (Lbl s) = s

label :: String -> Label
label s = Lbl s

symbol_table :: Named a => [a] -> Map String a
symbol_table xs = fromList $ map as_pair xs

composite_label :: [Label] -> Label
composite_label xs = Lbl $ intercalate "/" $ map str xs
    where
        str (Lbl s) = s

to_list :: Label -> [Label]
to_list (Lbl xs) = map Lbl $ split "/" xs
