module Logic.Theory 
    ( Theory(..)
    , fact
    , make_theory
    , all_theories
    , syntacticThm
    , th_notation
    , theory_ctx
    , theory_facts
    , empty_theory
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
import Control.Monad.RWS
import Control.Lens hiding (Context,from,to,rewriteM)

import           Data.Default
import           Data.List as L
import           Data.Map as M 

import GHC.Generics hiding ((:+:),prec)

import Utilities.Instances
import Utilities.Lens

all_theories :: Theory -> [Theory]
all_theories th = th : M.elems (all_theories' th)
    where
        _ = set theorySyntacticThm

all_theories' :: Theory -> Map String Theory
all_theories' th = M.unions $ view extends th : M.elems (M.map all_theories' $ view extends th)

basic_theory :: Theory
basic_theory = create $ do 
        types .= symbol_table [BoolSort, pair_sort, set_sort]
        funs  .= symbol_table [const_fun,ident_fun]
        fact  .= fromList 
           [ (label "@basic@@_0", axm0) 
           , (label "@basic@@_1", axm1) ]
        syntacticThm .= empty_monotonicity
            { _associative = fromList 
                    [("and",mztrue)
                    ,("or", mzfalse)
                    ,("=",  mztrue)]
            , _monotonicity = fromList $
                P.preserve implies_fun ["and","or"] 
             ++ [ (("=>","not"),Independent zfollows')
                , (("=>","=>"), Side (Just zfollows')
                                     (Just zimplies')) ] }
        notation .= functional_notation
   where
        zimplies' = Rel implies_fun Direct
        zfollows' = Rel implies_fun Flipped
        _ = theoryDummies Identity
--        t  = VARIABLE "t"
        t0 = VARIABLE "t0"
        t1 = VARIABLE "t1"
        (x,x_decl) = var "x" t0
        (y,y_decl) = var "y" t1
--        axm0 = fromJust $ mzforall [x_decl,y_decl] mztrue $
--                mzeq x y `mzeq` mzeq_symb x y
        axm0 = $typeCheck $ mzforall [x_decl,y_decl] mztrue $ 
            zselect (zconst x) y .=. x
        axm1 = $typeCheck $ mzforall [x_decl] mztrue $
            zselect zident x .=. x

th_notation :: Theory -> Notation
th_notation th = res
    where
        ths = th : elems (_extends th)
        res = flip precede logical_notation
            $ L.foldl OP.combine empty_notation 
            $ L.map _notation ths

theory_ctx :: Theory -> Context
theory_ctx th = 
        merge_all_ctx $
            (Context ts c new_fun (_defs th) dums) : L.map theory_ctx (M.elems d)
    where
        d      = _extends th
        ts     = _types th
        fun    = _funs th
        c      = _consts th
        dums   = th^.dummies
        new_fun = fun

    -- todo: prefix name of theorems of a z3_decoration
theory_facts :: Theory -> Map Label Expr
theory_facts th = 
        merge_all (new_fact : L.map theory_facts (M.elems d))
    where
        d      = _extends th
        facts  = _fact th
        new_fact = facts

instance HasSymbols Theory Var where
    symbols t = symbol_table $ defsAsVars (theory_ctx t)^.constants

instance Default Theory where
    def = genericDefault

instance NFData Theory where

instance HasScope Theory where
    scopeCorrect' t = mconcat
            [ withVars (symbols t)
                $ foldMapWithKey scopeCorrect'' $ t^.fact
            , withVars (symbols $ t & defs .~ M.empty)
                $ foldMapWithKey scopeCorrect'' $ t^.defs
            , foldMapWithKey scopeCorrect'' (t^.extends) ]

make_theory :: String -> M () -> Theory
make_theory name (M cmd) = to $ gBuild (from empty_theory) $ L.map from ts'
    where
        ts  = snd $ execRWS cmd () 0
        ts' = zipWith (\i -> fact %~ M.mapKeys (pad' i)) [0..] ts
        n = length $ show $ length ts
        pad m = name ++ replicate (n - length (show m)) ' ' ++ show m
        pad' k _ = label $ pad k
