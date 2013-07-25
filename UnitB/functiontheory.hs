{-# LANGUAGE BangPatterns #-}
module UnitB.FunctionTheory where

    -- Modules
import UnitB.Genericity
import UnitB.Theory
import UnitB.SetTheory hiding ( dec )

import Z3.Def
import Z3.Const

    -- Libraries
import Control.Monad

import Data.Map

import Utilities.Format

--import System.IO.Unsafe

ztfun = typ_fun2 (Fun [gA,gB] "tfun" [set_type gA, set_type gB] $ fun_set gA gB)
    where
        !() = unsafePerformIO (putStrLn "tfun")
--ztfun = typed_fun2 (\s0 s1 -> do
--            t0 <- item_type s0
--            t1 <- item_type s1
--            return $ Fun [t0,t1] (dec "tfun" t0 t1) [s0,s1] $ fun_set t0 t1)

zdom = typ_fun1 (Fun [gA,gB] "dom" [fun_type gA gB] $ set_type gA)
--zdom = typed_fun1 (\f0 -> do
--            t0 <- dom_type f0
--            t1 <- ran_type f0
--            return $ Fun [t0,t1] (dec "dom" t0 t1) [f0] $ set_type t0)

--zapply       = fun2 $ Fun "select" [
--        ARRAY (GENERIC "b") $ GENERIC "a", 
--        GENERIC "b"] $ 
--    GENERIC "a"
zstore        = typ_fun3 $ Fun [] "store" [
        ARRAY (gB) $ gA, 
        gB, gA] $ 
    ARRAY gB gA

--mzapply = maybe2 zapply
--mzovl = maybe3 obsolete_zovl

zselect = typ_fun2 (Fun [] "select" [ARRAY gA gB, gA] gB)

zapply  = typ_fun2 (Fun [] "select" [fun_type gA gB, gA] gB)
--    typed_fun2 (\f0 x0 -> do
--            dt0 <- dom_type f0
--            rt0 <- ran_type f0
--            unless (dt0 == x0) $ Left $ format "domain type {0} does not match the argument's type {1}" dt0 x0
--            return $ Fun [] "select" [f0,dt0] rt0)
zovl    = typ_fun2 (Fun [gA,gB] "ovl" [ft,ft] ft)
    where
        ft = fun_type gA gB
--    typed_fun2 (\f0 f1 -> do
--            dt0 <- dom_type f0
--            dt1 <- dom_type f1
--            rt0 <- ran_type f0
--            rt1 <- ran_type f1
--            unless (dt0 == dt1) $ Left $ format "domain types {0} and {1} do not match" dt0 dt1
--            unless (rt0 == rt1) $ Left $ format  "range types {0} and {1} do not match" rt0 rt1
--            return $ Fun [dt0,rt0] (dec "ovl" dt0 rt0) [f0,f0] f0)
zmk_fun = typ_fun2 (Fun [gA,gB] "mk-fun" [gA,gB] $ fun_type gA gB)
--    typed_fun2 (\t0 t1 -> do
--            return $ Fun [t0,t1] (dec "mk-fun" t0 t1) [t0,t1] $ fun_type t0 t1)

--gA = GENERIC "a"
gB = GENERIC "b"

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
                [  Fun [t0,t1] (dec "empty-fun") [] $ fun_type t0 t1
                ,  Fun [t0,t1] (dec "dom")   [fun_type t0 t1] $ set_type t0
                ,  Fun [t0,t1] (dec "apply") [fun_type t0 t1,t0] t1
                ,  Fun [t0,t1] (dec "ovl") [fun_type t0 t1,fun_type t0 t1] $ fun_type t0 t1
                ,  Fun [t0,t1] (dec "mk-fun") [t0,t1] $ fun_type t0 t1 
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
