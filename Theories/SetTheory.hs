{-# LANGUAGE BangPatterns #-}
module Theories.SetTheory where

    -- Modules
import Logic.Const
import Logic.Expr
import Logic.Genericity
import Logic.Label

import Theories.Theory

    -- Libraries
import Data.List as L
import Data.Map as M hiding ( foldl ) 

import Utilities.Format

set_sort = DefSort "\\set" "set" ["a"] (ARRAY (GENERIC "a") bool)
set_type t = USER_DEFINED set_sort [t]

set_theory :: Type -> Theory 
set_theory t = Theory [] types funs empty facts empty
    where
        types = symbol_table [set_sort]
        set_type = USER_DEFINED set_sort [t]
        funs = M.insert (dec "union") (Fun [t] (dec "bunion") [set_type,set_type] set_type) $
            symbol_table [
                Fun [] (dec "intersect") [set_type,set_type] set_type,
                Fun [] (dec "empty-set") [] set_type,
                Fun [] (dec "elem") [t,set_type] bool,
                Fun [] (dec "subset") [set_type,set_type] bool,
                Fun [] (dec "set-diff") [set_type,set_type] set_type,
                Fun [] (dec "mk-set") [t] set_type ]
        facts = fromList 
                [ (label $ dec' "0", axm0)
                , (label $ dec' "1", axm1)
                , (label $ dec' "2", axm2)
                , (label $ dec' "3", axm3)
                , (label $ dec' "4", axm4)
                , (label $ dec' "5", axm5)
                , (label $ dec' "6", axm6)
                ]
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
        (s1,s1_decl) = var "s1" set_type
        (s2,s2_decl) = var "s2" set_type
        dec x  = x ++ z3_decoration t
        dec' x = z3_decoration t ++ x

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

dec x t = x ++ z3_decoration t

item_type t0@(USER_DEFINED s [t]) 
        | s == set_sort         = Right t
        | otherwise             = Left $ format " {0} is not a set " t0
item_type t0                    = Left $ format " {0} is not a set " t0