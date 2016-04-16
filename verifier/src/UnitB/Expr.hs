module UnitB.Expr 
    ( module Logic.Expr
    , module Logic.Expr.Printable 
    , Expr, ExprP, RawExpr
    , raw )
where

import Logic.Expr hiding (Expr,ExprP,RawExpr)
import qualified Logic.Expr
import Logic.Expr.Printable

type Expr = DispExpr
type RawExpr = Logic.Expr.Expr
type ExprP = Either [String] Expr

raw :: (Functor m, HasExpr expr) => m expr -> m RawExpr
raw = fmap getExpr

