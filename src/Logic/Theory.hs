module Logic.Theory 
    ( Theory(..)
    , fact
    , make_theory
    , make_theory'
    , all_theories
    , syntacticThm
    , th_notation
    , th_notation'
    , theory_ctx
    , theory_facts
    , empty_theory
    , empty_theory'
    , basic_theory
    , symbols
    , types, defs, funs, consts, theorems
    , thm_depend, notation, extends )
where

    -- Modules
import Logic.Expr
import Logic.Expr.Const
import Logic.Expr.Scope
import Logic.Operator as OP
import Logic.Proof hiding (preserve) 
import qualified Logic.Proof as P
import Logic.Theory.Internals
import Logic.Theory.Monad

    -- Libraries
import Control.DeepSeq
import Control.Lens hiding (Context,from,to,rewriteM)

import           Data.Foldable as F
import           Data.List as L
import           Data.Map.Class as M 
import           Data.Serialize hiding (label)

import Utilities.Table

all_theories :: Theory -> [Theory]
all_theories th = th : M.ascElems (all_theories' th)
    where
        _ = set theorySyntacticThm

all_theories' :: Theory -> Table Name Theory
all_theories' th = M.unions $ view extends th : M.ascElems (M.map all_theories' $ view extends th)

basic_theory :: Theory
basic_theory = make_theory' "basic" $ do 
        types .= symbol_table [BoolSort, pair_sort, set_sort]
        funs  .= symbol_table [const_fun,ident_fun]
        fact  .= fromList 
           [ (label "@basic@@_0", axm0) 
           , (label "@basic@@_1", axm1) ]
        syntacticThm .= empty_monotonicity
            { _associative = fromList 
                    [(nAnd,   mztrue)
                    ,(nOr,    mzfalse)
                    ,(nEqual, mztrue)]
            , _monotonicity = fromList $
                P.preserve implies_fun [nAnd,nOr] 
             ++ [ ((nImp,nNeg),Independent zfollows')
                , ((nImp,nImp), Side (Just zfollows')
                                     (Just zimplies')) ] }
        notation .= functional_notation
   where
        nImp = z3Name "=>"
        nNeg = z3Name "not"
        nAnd = z3Name "and"
        nOr  = z3Name "or"
        nEqual = z3Name "="
        zimplies' = Rel implies_fun Direct
        zfollows' = Rel implies_fun Flipped
        _ = theoryDummies Identity
--        t  = VARIABLE "t"
        t0 = VARIABLE $ z3Name "t0"
        t1 = VARIABLE $ z3Name "t1"
        (x,x_decl) = var "x" t0
        (y,y_decl) = var "y" t1
--        axm0 = fromJust $ mzforall [x_decl,y_decl] mztrue $
--                mzeq x y `mzeq` mzeq_symb x y
        axm0 = $typeCheck $ mzforall [x_decl,y_decl] mztrue $ 
            zselect (zconst x) y .=. x
        axm1 = $typeCheck $ mzforall [x_decl] mztrue $
            zselect zident x .=. x



th_notation :: Theory -> Notation
th_notation th = th_notation' ths
    where ths = th : ascElems (_extends th)

th_notation' :: Foldable f => f Theory -> Notation
th_notation' ths = res
    where
        res = flip precede logical_notation res'
        res' = F.foldr (OP.combine . _notation) empty_notation ths

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

    -- todo: prefix name of theorems of a z3_decoration
theory_facts :: Theory -> Table Label Expr
theory_facts th = 
        merge_all (new_fact : L.map theory_facts (M.ascElems d))
    where
        d      = _extends th
        facts  = _fact th
        new_fact = facts

instance HasSymbols Theory Var Name where
    symbols t = symbol_table $ defsAsVars (theory_ctx t)^.constants


instance NFData Theory where

instance HasScope Theory where
    scopeCorrect' t = mconcat
            [ withVars (symbols t)
                $ foldMapWithKey scopeCorrect'' $ t^.fact
            , withVars (symbols $ t & defs .~ M.empty)
                $ foldMapWithKey scopeCorrect'' $ t^.defs
            , foldMapWithKey scopeCorrect'' (t^.extends) ]

instance Serialize Theory where
