module Logic.Theory.Internals where

    -- Modules
import Logic.Expr
import Logic.Operator
import Logic.Proof hiding (preserve) 

    -- Libraries
import Control.Lens hiding (Context,(.=),from,to,rewriteM)
import Control.Lens.HierarchyTH
import Control.Precondition

import           Data.Typeable

import GHC.Generics hiding ((:+:),prec)

import Test.QuickCheck.ZoomEq

import Utilities.Table

data Theory = Theory 
        { _theoryName :: Name
        , _extends    :: Table Name Theory
        , _types      :: Table Name Sort
        , _funs       :: Table Name Fun
        , _theoryDefs :: Table Name Def
        , _consts     :: Table Name Var
        , _theoryDummies :: Table Name Var 
        , _theorySyntacticThm :: SyntacticProp
        , _fact       :: Table Label Expr
        , _theorems   :: Table Label (Maybe Proof)
        , _thm_depend :: [ (Label,Label) ]
        , _notation   :: Notation }
    deriving (Eq, Show, Typeable, Generic)

makeLenses ''Theory
makeFields ''Theory
mkCons ''Theory

empty_theory :: Name -> Theory
empty_theory n = (makeTheory n)
    { _notation = empty_notation }

empty_theory' :: Pre => String -> Theory
empty_theory' = empty_theory . fromString''

instance ZoomEq Theory where
