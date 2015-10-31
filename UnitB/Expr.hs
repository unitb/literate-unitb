module UnitB.Expr 
    ( module Logic.Expr
    , module Logic.Expr.Printable 
    , Expr, RawExpr, ExprP
    , raw )
where

import Logic.Expr hiding (Expr,ExprP)
import qualified Logic.Expr
import Logic.Expr.Printable

type Expr = DispExpr
type RawExpr = Logic.Expr.Expr
type ExprP = Either [String] Expr

raw :: (Functor m, IsExpr expr) => m expr -> m RawExpr
raw = fmap getExpr
