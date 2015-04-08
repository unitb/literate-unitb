{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}
module Logic.Theory where

    -- Modules
import Logic.Expr
import Logic.Operator
import Logic.Proof

    -- Libraries
import Control.Arrow
import Control.DeepSeq
import Control.Monad.Writer

import           Data.Either
import           Data.Either.Combinators
import           Data.List as L
import           Data.Map as M hiding ( map )
import qualified Data.Set as S

import Language.Haskell.TH

import Utilities.Format

    -- Obsolete doc:
    -- the use of gen_param is tricky. Be careful
    -- generic functions should have type variables in them
    -- to match those type variables, we use the generic 
    -- parameter that features corresponding /generic/
    -- types. We unify the generic parameter with all 
    -- the types of all the variables and functions
    -- and use the resulting mapping to instantiate 
    -- the type variables. The generic type (rather than
    -- the type variable) is also used in function types.
data Theory = Theory 
        { extends    :: Map String Theory
        , types      :: Map String Sort
        , funs       :: Map String Fun
        , defs       :: Map String Def
        , consts     :: Map String Var
        , fact       :: Map Label Expr
        , dummies    :: Map String Var 
        , theorems   :: Map Label (Maybe Proof)
        , thm_depend :: [ (Label,Label) ]
        , notation   :: Notation }
    deriving (Eq, Show)

basic_theory :: Theory
basic_theory = empty_theory 
        { types = symbol_table [BoolSort, pair_sort]
--        , funs = symbol_table [everywhere_fun]
--        , gen_param = Just gT
--        , funs  = symbol_table [Fun [gT] "eq" [gT,gT] bool]
--        , fact  = fromList 
--            [ (label "@basic@@_0", axm0) ]
       , funs  = symbol_table [const_fun,ident_fun]
       , fact  = fromList 
           [ (label "@basic@@_0", axm0) 
           , (label "@basic@@_1", axm1)]
        , notation = functions }
   where
--        t  = VARIABLE "t"
        t0 = VARIABLE "t0"
        t1 = VARIABLE "t1"
        (x,x_decl) = var "x" t0
        (y,y_decl) = var "y" t1
--        axm0 = fromJust $ mzforall [x_decl,y_decl] mztrue $
--                mzeq x y `mzeq` mzeq_symb x y
        axm0 = $fromJust $ mzforall [x_decl,y_decl] mztrue $ 
            zselect (zconst x) y .= x
        axm1 = $fromJust $ mzforall [x_decl] mztrue $
            zselect zident x .= x

empty_theory :: Theory
empty_theory = Theory M.empty 
    M.empty M.empty M.empty M.empty 
    M.empty M.empty M.empty [] 
    (with_assoc empty_notation)

th_notation :: Theory -> Notation
th_notation th = res
    where
        ths = th : elems (extends th)
        res = flip precede logic
            $ L.foldl combine empty_notation 
            $ map notation ths

theory_ctx :: Theory -> Context
theory_ctx th = 
        merge_all_ctx $
            (Context ts c new_fun (defs th) dums) : L.map theory_ctx (M.elems d)
    where
        d      = extends th
        ts     = types th
        fun    = funs th
        c      = consts th
        dums   = dummies th
        new_fun = fun

    -- todo: prefix name of theorems of a z3_decoration
theory_facts :: Theory -> Map Label Expr
theory_facts th = 
        merge_all (new_fact : L.map theory_facts (M.elems d))
    where
        d      = extends th
        facts  = fact th
        new_fact = facts

declAxiom :: Loc -> ExprP -> Writer [ExprP] ()
declAxiom loc stmt = tell [mapLeft (map (locMsg loc ++)) $ zcast bool $ withForall stmt]

withForall :: ExprP -> ExprP 
withForall mx = do
    x <- mx
    let vs = S.toList $ used_var x
    mzforall vs mztrue $ Right x

axiom :: ExpQ
axiom = withLoc 'declAxiom

axioms :: String -> Writer [ExprP] () -> Map Label Expr
axioms name cmd
        | L.null ls = fromList $ L.map (first $ label . format "@{0}@@_{1}" name) $ zip ns rs
        | otherwise = error $ unlines $ concat ls
    where
        n  = length rs
        ns = map (pad . show) [1..n]
        pad ys = replicate (n - length ys) ' ' ++ ys
        rs = rights xs
        ls = lefts xs
        xs = execWriter cmd

instance NFData Theory where
    rnf (Theory a b c d e f g h i j) = 
            a `deepseq` rnf (b,c,d,e,f,g,h,i,j)
