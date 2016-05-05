module Logic.Theory.Internals where

    -- Modules
import Logic.Expr
import Logic.Expr.Scope
import Logic.Operator
import Logic.Proof hiding (preserve) 

    -- Libraries
import Control.DeepSeq
import Control.Lens hiding (Context,(.=),from,to,rewriteM)
import Control.Precondition

import           Data.Map.Class as M 
import           Data.List as L
import           Data.Serialize
import           Data.Typeable

import GHC.Generics hiding ((:+:),prec)

import Utilities.Table as M
import Utilities.TH

data Theory = Theory 
        { _theoryName :: Name
        , _extends    :: Table Name Theory
        , _types      :: Table Name Sort
        , _funs       :: Table Name Fun
        , _defs       :: Table Name Def
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

instance NFData Theory where

instance HasScope Theory where
    scopeCorrect' t = mconcat
            [ withVars (symbols t)
                $ foldMapWithKey scopeCorrect'' $ t^.fact
            , withVars (symbols $ t & defs .~ M.empty)
                $ foldMapWithKey scopeCorrect'' $ t^.defs
            , foldMapWithKey scopeCorrect'' (t^.extends) ]

instance Serialize Theory where

instance HasSymbols Theory Var Name where
    symbols t = symbol_table $ defsAsVars (theory_ctx t)^.constants

theory_ctx :: Theory -> Context
theory_ctx th = 
        merge_all_ctx $
            (Context ts c new_fun (_defs th) dums) : L.map theory_ctx (M.ascElems d)
    where
        d      = _extends th
        ts     = _types th
        fun    = _funs th
        c      = _consts th
        dums   = th^.dummies
        new_fun = fun
