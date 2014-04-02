{-# LANGUAGE BangPatterns, RecordWildCards #-}
module Theories.SetTheory where

    -- Modules
import Logic.Const
import Logic.Expr
import Logic.Genericity
import Logic.Label
import Logic.Operator
import Logic.Theory
import Logic.Type

    -- Libraries
import Data.List as L
import Data.Map as M hiding ( foldl ) 

import Utilities.Format

set_sort :: Sort
set_sort = DefSort "\\set" "set" ["a"] (array (GENERIC "a") bool)

set_type :: TypeSystem t => t -> t
set_type t = make_type set_sort [t]

set_theory :: Theory 
set_theory = Theory { .. } -- [] types funs empty facts empty
    where
        t  = VARIABLE "t"
        gT = GENERIC "t"
        gen_param = Just $ set_type gT

        extends = M.empty
        consts  = M.empty
        dummies = M.empty
        types = symbol_table [set_sort]
        funs = M.insert "union" (Fun [gT] "bunion" [set_type gT,set_type gT] $ set_type gT) $
            symbol_table [
                Fun [gT] "intersect" [set_type gT,set_type gT] $ set_type gT,
                Fun [gT] "empty-set" [] $ set_type gT,
                Fun [gT] "elem" [gT,set_type gT] bool,
                Fun [gT] "subset" [set_type gT,set_type gT] bool,
                Fun [gT] "set-diff" [set_type gT,set_type gT] $ set_type gT,
                Fun [gT] "mk-set" [gT] $ set_type gT ]
        fact :: Map Label Expr
        fact = fromList 
                [ (label $ dec' "0", axm0)
                , (label $ dec' "1", axm1)
                , (label $ dec' "2", axm2)
                , (label $ dec' "3", axm3)
                , (label $ dec' "4", axm4)
                , (label $ dec' "5", axm5)
                , (label $ dec' "6", axm6)
                ]
        thm_depend = []
        notation   = set_notation
                
            -- elem and mk-set
        Right axm0 = mzforall [x_decl,y_decl] mztrue ((x `zelem` zmk_set y) `mzeq` (x `mzeq` y))
            -- elem over set-diff
        Right axm1 = mzforall [x_decl,s1_decl,s2_decl] mztrue (
                            (x `zelem` (s1 `zsetdiff` s2)) 
                    `mzeq` ( (x `zelem` s1) `mzand` mznot (x `zelem` s2) ))
            -- elem over intersect
        Right axm2 = mzforall [x_decl,s1_decl,s2_decl] mztrue (
                            (x `zelem` (s1 `zintersect` s2)) 
                    `mzeq` ( (x `zelem` s1) `mzand` (x `zelem` s2) ))
            -- elem over union
        Right axm3 = mzforall [x_decl,s1_decl,s2_decl] mztrue (
                            (x `zelem` (s1 `zunion` s2)) 
                    `mzeq` ( (x `zelem` s1) `mzor` (x `zelem` s2) ))
            -- elem over empty-set
        Right axm4 = mzforall [x_decl] mztrue (
                            mznot (x `zelem` Right zempty_set)  )
        axm5 = fromJust $ mzforall [x_decl,s1_decl] mztrue (
                            mzeq (zelem x s1)
                                (zset_select s1 x)  )
--        Right axm2 = mzforall [x_decl,s1_decl] (mznot (x `zelem` zempty_set))
            -- subset extensionality
        axm6 = fromJust $ mzforall [s1_decl,s2_decl] mztrue $
                        ( s1 `zsubset` s2 )
                    `mzeq` (mzforall [x_decl] mztrue ( zelem x s1 `mzimplies` zelem x s2 ))
        (x,x_decl) = var "x" t
        (y,y_decl) = var "y" t
        (s1,s1_decl) = var "s1" $ set_type t
        (s2,s2_decl) = var "s2" $ set_type t
--            dec x  = x ++ z3_decoration t
        dec' x = "@set@@_" ++ x
        
        theorems = M.empty

zset_select   :: ExprP -> ExprP -> ExprP
zempty_set    :: Expr
zelem         :: ExprP -> ExprP -> ExprP
zsubset       :: ExprP -> ExprP -> ExprP
zsetdiff      :: ExprP -> ExprP -> ExprP
zintersect    :: ExprP -> ExprP -> ExprP

zunion        :: ExprP -> ExprP -> ExprP
zmk_set       :: ExprP -> ExprP
zset_enum     :: [ExprP] -> ExprP

zset_select = typ_fun2 (Fun [] "select" [set_type gA, gA] bool)

zempty_set   = Const [gA] "empty-set" $ set_type gA

zelem        = typ_fun2 (Fun [gA] "elem" [gA,set_type gA] bool)
zsubset      = typ_fun2 (Fun [gA] "subset" [set_type gA,set_type gA] bool)
zsetdiff     = typ_fun2 (Fun [gA] "set-diff" [set_type gA,set_type gA] $ set_type gA)
zintersect   = typ_fun2 (Fun [gA] "intersect" [set_type gA,set_type gA] $ set_type gA)

zunion       = typ_fun2 (Fun [gA] "bunion" [set_type gA,set_type gA] $ set_type gA)
zmk_set      = typ_fun1 (Fun [gA] "mk-set" [gA] $ set_type gA)
zset_enum xs = foldl zunion y ys 
    where
        (y:ys) = L.map zmk_set xs

dec :: String -> Type -> String
dec x t = x ++ z3_decoration t

item_type :: Type -> Either String Type
item_type t0@(Gen (USER_DEFINED s [t]))
        | s == set_sort         = Right t
        | otherwise             = Left $ format " {0} is not a set " t0
item_type t0                    = Left $ format " {0} is not a set " t0

    -- set theory
set_union   :: BinOperator
set_diff    :: BinOperator
membership  :: BinOperator
subset      :: BinOperator
superset    :: BinOperator
st_subset   :: BinOperator
st_superset :: BinOperator

set_union   = BinOperator "union" "\\bunion"        zunion
set_diff    = BinOperator "set-diff" "\\setminus"   zsetdiff
membership  = BinOperator "membership" "\\in"       zelem
subset      = BinOperator "subset"     "\\subseteq" zsubset
superset    = BinOperator "superset"   "\\supseteq" (flip zsubset)
st_subset   = BinOperator "st-subset"   "\\subset" zsubset
st_superset = BinOperator "st-superset" "\\supset" (flip zsubset)

set_notation :: Notation
set_notation = Notation
    { new_ops     = L.map Right 
                    [ set_union,set_diff,membership
                    , subset,superset,st_subset,st_superset]
    , prec = [ L.map (L.map Right)
                 [ [apply]
                 , [set_union,set_diff]
                 , [ equal
                   , membership, subset ] ]]
    , left_assoc  = [[set_union]]
    , right_assoc = []
    , relations   = []
    , chaining    = [ ((subset,subset),subset) 
                    , ((subset,st_subset),st_subset)
                    , ((st_subset,subset),st_subset)
                    , ((st_subset,st_subset),st_subset)
                    , ((superset,superset),superset) 
                    , ((superset,st_superset),st_superset)
                    , ((st_superset,superset),st_superset)
                    , ((st_superset,st_superset),st_superset)
                    ]  }
