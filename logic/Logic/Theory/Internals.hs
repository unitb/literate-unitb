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

empty_theory :: Name -> Theory' expr
empty_theory n = (makeTheory' n)
    { _notation = empty_notation }

empty_theory' :: Pre => String -> Theory' expr
empty_theory' = empty_theory . fromString''

instance ZoomEq expr => ZoomEq (Theory' expr) where

instance NFData expr => NFData (Theory' expr) where

instance Serialize expr => Serialize (Theory' expr) where
