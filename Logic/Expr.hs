module Logic.Expr 
    ( module Logic.Expr.Classes 
    , module Logic.Expr.Const
    , module Logic.Expr.Expr
    , module Logic.Expr.Genericity
    , module Logic.Expr.Label
    , module Logic.Expr.PrettyPrint
    , module Logic.Expr.Type
    )
where

import Logic.Expr.Classes 
import Logic.Expr.Const hiding (toList)
import Logic.Expr.Expr  -- hiding (Expr)  
import Logic.Expr.Genericity hiding ( Generic, variables )
import Logic.Expr.Label
import Logic.Expr.PrettyPrint
import Logic.Expr.Type
