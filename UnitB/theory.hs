module UnitB.Theory where

import UnitB.Label

import Z3.Def

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

instance Named Fun where
    name (Fun _ x _ _) = x

instance Named Var where
    name (Var x _) = x

instance Named Sort where
    name (Sort x _ _) = x
    name (DefSort x _ _ _) = x
    name BoolSort   = "\\Bool"
    name IntSort    = "\\Int"
    name RealSort   = "\\Real"
