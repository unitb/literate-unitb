module UnitB.Expr 
    ( module Logic.Expr
    , module Logic.Expr.Printable 
    , Expr(..), ExprP, RawExpr(..)
    , raw )
where

    -- Modules
import Logic.Expr hiding (Expr,ExprP,RawExpr)
import qualified Logic.Expr
import Logic.Expr.Printable

    -- Libraries
import Control.DeepSeq
import Data.Serialize
import GHC.Generics
import Test.QuickCheck.ZoomEq

newtype Expr v = Expr (DispExpr)
    deriving (Eq,Ord,Show,Generic)

newtype RawExpr v = RawExpr (Logic.Expr.Expr)
    deriving (Eq,Ord,Show,Generic)

type ExprP v = Either [String] (Expr v)

raw :: (Functor m, HasExpr expr) => m expr -> m (RawExpr v)
raw = fmap (RawExpr . getExpr)

instance Serialize (RawExpr v)
instance NFData (RawExpr v)
instance ZoomEq (RawExpr v)
