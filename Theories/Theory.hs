module Theories.Theory where

import Logic.Expr
import Logic.Label

    -- Libraries
import Data.Map hiding ( map )

data Theory = Theory {
        extends :: [Theory],
        types   :: Map String Sort,
        funs    :: Map String Fun,
        consts  :: Map String Var,
        fact    :: Map Label Expr,
        dummies :: Map String Var }
    deriving (Eq, Show)
