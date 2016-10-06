{-# LANGUAGE CPP #-}
module Logic.Theory.Internals where

    -- Modules
import Logic.Expr
import Logic.Operator
import Logic.Proof hiding (preserve) 

    -- Libraries
import Control.DeepSeq
import Control.Lens hiding (Context,(.=),from,to,rewriteM)
import Control.Lens.HierarchyTH
import Control.Precondition

#if MIN_VERSION_transformers(0,5,0)
import           Prelude.Extras hiding (Lift1)
-- #else
-- import           Data.Functor.Classes
#endif
import           Data.Serialize
import           Data.Typeable

import GHC.Generics hiding ((:+:),prec)

import Test.QuickCheck.ZoomEq

import Utilities.Table

type Theory = Theory' Expr
data Theory' expr = Theory 
        { _theory'Name :: Name
        , _extends    :: Table Name Theory
        , _types      :: Table Name Sort
        , _funs       :: Table Name Fun
        , _theory'Defs :: Table Name Def
        , _consts     :: Table Name Var
        , _theory'Dummies :: Table Name Var 
        , _theory'SyntacticThm :: SyntacticProp
        , _fact       :: Table Label expr
        , _theorems   :: Table Label (Maybe Proof)
        , _thm_depend :: [ (Label,Label) ]
        , _notation   :: Notation }
    deriving ( Eq, Show, Typeable, Generic, Functor
             , Foldable, Traversable)

makeLenses ''Theory'
makeFields ''Theory'
mkCons ''Theory'

-- #if MIN_VERSION_transformers(0,5,0)
-- instance Ord k => F.Eq1 (Table k) where
--     liftEq eq m0 m1 = F.liftEq eq' (toList m0) (toList m1)
--         where
--             eq' (x0,x1) (y0,y1) = x0 == y0 && eq x1 y1

-- instance F.Eq1 Theory' where
--     liftEq eq  
--             (Theory x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
--             (Theory y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11)
--         =  x0 == y0
--         && x1 == y1
--         && x2 == y2
--         && x3 == y3
--         && x4 == y4
--         && x5 == y5
--         && x6 == y6
--         && x7 == y7
--         && F.liftEq eq x8 y8
--         && x9 == y9
--         && x10 == y10
--         && x11 == y11
-- #endif

empty_theory :: Name -> Theory' expr
empty_theory n = (makeTheory' n)
    { _notation = empty_notation }

empty_theory' :: Pre => String -> Theory' expr
empty_theory' = empty_theory . fromString''

instance ZoomEq expr => ZoomEq (Theory' expr) where

instance NFData expr => NFData (Theory' expr) where

instance Serialize expr => Serialize (Theory' expr) where
