{-# LANGUAGE DeriveGeneric, DeriveDataTypeable #-}
{-# LANGUAGE OverloadedStrings #-}
module Logic.Expr.Label where

    -- Module
import Logic.Expr.Classes

    -- Libraries
import GHC.Generics 

import Data.List as L
import Data.Map hiding ( map, split )
import Data.String
import Data.String.Utils ( split )
import Data.Typeable

data Label = Lbl String
    deriving (Ord, Eq, Typeable, Generic)

instance Show Label where
    show (Lbl s) = s

instance IsString Label where
    fromString x = label x

label :: String -> Label
label s = Lbl s

symbol_table :: Named a => [a] -> Map String a
symbol_table xs = fromList $ map as_pair xs

decorated_table :: Named a => [a] -> Map String a
decorated_table xs = fromList $ map (\x -> (decorated_name x, x)) xs

composite_label :: [Label] -> Label
composite_label xs = Lbl $ intercalate "/" $ L.filter (not . L.null) $ map str xs
    where
        str (Lbl s) = s

to_list :: Label -> [Label]
to_list (Lbl xs) = map Lbl $ split "/" xs
