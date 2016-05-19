{-# LANGUAGE OverloadedStrings #-}
module Logic.Expr.Label where

    -- Module
import Logic.Names

    -- Libraries
import Control.DeepSeq

import Data.Hashable
import Data.List as L
import Data.Serialize hiding (label)
import Data.String
import Data.String.Utils ( split )
import Data.Typeable

import GHC.Generics 

import Test.QuickCheck hiding (label)

import Text.Pretty

data Label = Lbl String
    deriving (Ord, Eq, Show, Typeable, Generic)

class IsLabel a where
    as_label :: a -> Label

instance PrettyPrintable Label where
    pretty (Lbl s) = s

instance IsString Label where
    fromString x = label x

instance IsLabel Label where
    as_label = id

instance IsLabel Name where
    as_label = label . render . asInternal

instance (IsLabel l,IsLabel r) => IsLabel (Either l r) where
    as_label = either as_label as_label

instance Arbitrary Label where
    arbitrary = Lbl <$> elements [ [x,y] | x <- ['a'..'z'], y <- ['0'..'9'] ]

instance Hashable Label where

label :: String -> Label
label s = Lbl s

(</>) :: Label -> Label -> Label
(</>) (Lbl x) (Lbl y) = Lbl $ x ++ "/" ++ y

composite_label :: [Label] -> Label
composite_label xs = Lbl $ intercalate "/" $ L.filter (not . L.null) $ map str xs
    where
        str (Lbl s) = s

to_list :: Label -> [Label]
to_list (Lbl xs) = map Lbl $ split "/" xs

instance NFData Label

instance Serialize Label where
