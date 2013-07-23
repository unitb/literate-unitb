module UnitB.FunctionTheory where

import Control.Monad

import Data.Map

import UnitB.Theory
import UnitB.SetTheory hiding ( dec )

import Utilities.Format

import Z3.Def
import Z3.Const

ztfun = typed_fun2 (\s0 s1 -> do
            t0 <- item_type s0
            t1 <- item_type s1
            return $ Fun (dec "tfun" t0 t1) [s0,s1] $ fun_set t0 t1)

zdom = typed_fun1 (\f0 -> do
            t0 <- dom_type f0
            t1 <- ran_type f0
            return $ Fun (dec "dom" t0 t1) [f0] $ set_type t0)

--zapply       = fun2 $ Fun "select" [
--        ARRAY (GENERIC "b") $ GENERIC "a", 
--        GENERIC "b"] $ 
--    GENERIC "a"
obsolete_zovl        = fun3 $ Fun "store" [
        ARRAY (GENERIC "b") $ GENERIC "a", 
        GENERIC "b", GENERIC "a"] $ 
    ARRAY (GENERIC "b") $ GENERIC "a"

--mzapply = maybe2 zapply
mzovl = maybe3 obsolete_zovl

zapply  = typed_fun2 (\f0 x0 -> do
            dt0 <- dom_type f0
            rt0 <- ran_type f0
            unless (dt0 == x0) $ Left $ format "domain type {0} does not match the argument's type {1}" dt0 x0
            return $ Fun "select" [f0,dt0] rt0)
zovl    = typed_fun2 (\f0 f1 -> do
            dt0 <- dom_type f0
            dt1 <- dom_type f1
            rt0 <- ran_type f0
            rt1 <- ran_type f1
            unless (dt0 == dt1) $ Left $ format "domain types {0} and {1} do not match" dt0 dt1
            unless (rt0 == rt1) $ Left $ format  "range types {0} and {1} do not match" rt0 rt1
            return $ Fun (dec "ovl" dt0 rt0) [f0,f0] f0)
zmk_fun = typed_fun2 (\t0 t1 -> do
            return $ Fun (dec "mk-fun" t0 t1) [t0,t1] $ fun_type t0 t1)

dec x t0 t1 = x ++ z3_decoration t0 ++ z3_decoration t1

dom_type f0@(USER_DEFINED s [t0,t1])
        | s == fun_sort         = Right t0
        | otherwise             = Left $ format "{0} is not a function type" f0
dom_type f0                     = Left $ format "{0} is not a function type" f0

ran_type f0@(USER_DEFINED s [t0,t1])
        | s == fun_sort         = Right t1
        | otherwise             = Left $ format "{0} is not a function type" f0
ran_type f0                     = Left $ format "{0} is not a function type" f0

--item_type t0@(USER_DEFINED s [t]) 
--        | s == set_sort         = Right t
--        | otherwise             = Left $ format "{0} is not a set type" t0
--item_type t0                    = Left $ format "{0} is not a set type" t0

fun_sort = DefSort "\\pfun" "pfun" ["a","b"] (ARRAY (GENERIC "a") (GENERIC "b"))

fun_type t0 t1 = USER_DEFINED fun_sort [t0,t1] --ARRAY t0 t1

fun_set t0 t1 = set_type (fun_type t0 t1)

function_theory :: Type -> Type -> Theory 
function_theory t0 t1 = Theory [] types funs empty facts empty
    where
--        set_ths  = 
        fun_set  = set_type (fun_type t0 t1)
        types    = empty -- symbol_table [fun_sort]
        funs = 
            symbol_table 
                [  Fun (dec "empty-fun") [] $ fun_type t0 t1
                ,  Fun (dec "dom")   [fun_type t0 t1] $ set_type t0
                ,  Fun (dec "apply") [fun_type t0 t1,t0] t1
                ,  Fun (dec "ovl") [fun_type t0 t1,fun_type t0 t1] $ fun_type t0 t1
                ,  Fun (dec "mk-fun") [t0,t1] $ fun_type t0 t1 
                ]
        facts = fromList 
                [ (label $ dec "0", axm0)
--                , (label $ dec "1", axm1)
--                , (label $ dec "2", axm2)
                ]
        axm0 = fromJust $ mzforall [f1_decl,f2_decl] ((zdom f1 `zunion` zdom f2) `mzeq` (zdom (f1 `zovl` f2)))
--        Right axm1 = mzforall [f1_decl,f2_decl] (
--                          (x `zelem` (s1 `zsetdiff` s2)) 
--                    `mzeq` ( (x `zelem` s1) `mzand` mznot (x `zelem` s2) ))
--        Right axm2 = mzforall [x_decl,s1_decl,s2_decl] (
--                          (x `zelem` (s1 `zsetdiff` s2)) 
--                    `mzeq` ( (x `zelem` s1) `mzand` mznot (x `zelem` s2) ))
        (x,x_decl) = var "x" t0
        (y,y_decl) = var "y" t1
        (f1,f1_decl) = var "f1" $ fun_type t0 t1
        (f2,f2_decl) = var "f2" $ fun_type t0 t1
        dec x = x ++ z3_decoration t0 ++ z3_decoration t1
