module Utilities.String where

newtype ShowString = ShowString String

instance Show ShowString where
    show (ShowString x) = x
