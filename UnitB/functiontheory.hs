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

zdom = typ_fun1 (Fun [gA,gB] "dom" [fun_type gA gB] $ set_type gA)

zdomsubt = typ_fun2 (Fun [gA,gB] "dom-subt" [set_type gA, fun_type gA gB] $ fun_type gA gB)

zdomrest = typ_fun2 (Fun [gA,gB] "dom-rest" [set_type gA, fun_type gA gB] $ fun_type gA gB)

zapply  = typ_fun2 (Fun [gA,gB] "apply" [fun_type gA gB, gA] gB)

zovl    = typ_fun2 (Fun [gA,gB] "ovl" [ft,ft] ft)
    where
        ft = fun_type gA gB

zmk_fun = typ_fun2 (Fun [gA,gB] "mk-fun" [gA,gB] $ fun_type gA gB)

zempty_fun = Const [gA,gB] "empty-fun" $ fun_type gA gB

zlambda xs mx my = do
        x <- zcast BOOL mx
        y <- my
        return $ Binder Lambda xs x y

zstore        = typ_fun3 $ Fun [] "store" [
        ARRAY (gB) $ gA, 
        gB, gA] $ 
    ARRAY gB gA

--zselect = typ_fun2 (Fun [] "select" [ARRAY gA gB, gA] gB)

fun_set t0 t1 = set_type (fun_type t0 t1)

function_theory :: Type -> Type -> Theory 
function_theory t0 t1 = Theory [set_theory $ fun_type t0 t1, set_theory t0] types funs empty facts empty
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
                ,  Fun [t0,t1] (dec "dom-rest") [set_type t0,fun_type t0 t1] $ fun_type t0 t1
                ,  Fun [t0,t1] (dec "dom-subt") [set_type t0,fun_type t0 t1] $ fun_type t0 t1
                ,  Fun [t0,t1] (dec "mk-fun") [t0,t1] $ fun_type t0 t1 
                ,  Fun [t0,t1] (dec "tfun") [set_type t0,set_type t1] $ fun_set
                ]
        facts = fromList 
                [ (label $ dec' "0", axm0) :: (Label, Expr)
                , (label $ dec' "1", axm1)
--                , (label $ dec "2", axm2)
--                , (label $ dec "3", axm3)
                , (label $ dec' "2", axm4)
--                , (label $ dec "5", axm5)
                , (label $ dec' "3", axm6)
                , (label $ dec' "4", axm7)
--                , (label $ dec' "5", axm8)
--                , (label $ dec "3", axm9)
                , (label $ dec' "5", axm10)
                , (label $ dec' "6", axm11)
                , (label $ dec' "7", axm12)
                , (label $ dec' "8", axm13)
--                , (label $ dec' "9", axm14)
--                , (label $ dec' "10", axm15)
                ]
            -- dom and empty-fun
        axm1 = fromJust (zdom (as_fun $ Right zempty_fun) `mzeq` Right zempty_set)
            -- empty-fun and ovl
        axm2 = fromJust $ mzforall [f1_decl] mztrue ( (f1 `zovl` Right zempty_fun) `mzeq` f1 )
        axm3 = fromJust $ mzforall [f1_decl] mztrue ( (Right zempty_fun `zovl` f1) `mzeq` f1 )
            -- dom and mk-fun
        axm4 = fromJust $ mzforall [x_decl,y_decl] mztrue ( zdom (x `zmk_fun` y) `mzeq` zmk_set x )
            -- mk_fun and apply
        axm5 = fromJust $ mzforall [x_decl,y_decl] mztrue ( (zmk_fun x y `zapply` x) `mzeq` y )
            -- ovl and apply
        axm6 = fromJust $ mzforall [f1_decl,f2_decl,x_decl] mztrue ( 
                        (x `zelem` zdom f2) 
            `mzimplies` (zapply (f1 `zovl` f2) x `mzeq` zapply f2 x))
        axm7 = fromJust $ mzforall [f1_decl,f2_decl,x_decl] mztrue ( 
                        (x `zelem` (zdom f1 `zsetdiff` zdom f2))
            `mzimplies` (zapply (f1 `zovl` f2) x `mzeq` zapply f1 x))
            -- apply and mk-fun
        axm11 = fromJust $ mzforall [x_decl,y_decl] mztrue ( 
                (zmk_fun x y `zapply` x) `mzeq` y )
            -- dom-rest and apply
        axm12 = fromJust $ mzforall [f1_decl,s1_decl,x_decl] mztrue (
                        (x `zelem` (s1 `zintersect` zdom f1))
            `mzimplies` (zapply (s1 `zdomrest` f1) x `mzeq` zapply f1 x) )
            -- dom-subst and apply
        axm13 = fromJust $ mzforall [f1_decl,s1_decl,x_decl] mztrue (
                        (x `zelem` (zdom f1 `zsetdiff` s1))
            `mzimplies` (zapply (s1 `zdomsubt` f1) x `mzeq` zapply f1 x) )
            -- empty-fun as a total function
--        axm8 = fromJust $ mzforall [s2_decl] 
--            ( as_fun (Right zempty_fun) `zelem` ztfun (as_dom $ Right zempty_set) s2 )
            -- dom and overload
        axm0 = fromJust $ mzforall [f1_decl,f2_decl] mztrue ((zdom f1 `zunion` zdom f2) `mzeq` (zdom (f1 `zovl` f2)))
            -- dom and tfun
            -- dom-rest and tfun
            -- dom-subst and tfun
            -- dom-rest and dom
        axm9  = fromJust $ mzforall [f1_decl,s1_decl] mztrue ((zdom (s1 `zdomrest` f1)) `mzeq` (s1 `zintersect` zdom f1))
            -- dom-subst and dom
        axm10 = fromJust $ mzforall [f1_decl,s1_decl] mztrue ((zdom (s1 `zdomsubt` f1)) `mzeq` (zdom f1 `zsetdiff` s1))
        
--        axm14 = fromJust $ mzforall [f1_decl] mztrue (
--                    mzeq (zlambda [x_decl] mzfalse (zapply f1 x))
--                         $ Right zempty_fun)
        
--        axm15 = fromJust $ mzforall [f1_decl,x2_decl] mztrue (
--                    mzeq (zlambda [x_decl] (x `mzeq` x2) (zapply f1 x))
--                         $ zmk_fun x2 (zapply f1 x2) )

        as_fun e = zcast (fun_type t0 t1) e
--        as_fun e = e
--        as_dom e = zcast (set_type t0) e
        as_dom e = e
        
        (x,x_decl) = var "x" t0
        (x2,x2_decl) = var "x2" t0
        (y,y_decl) = var "y" t1
        (f1,f1_decl) = var "f1" $ fun_type t0 t1
        (f2,f2_decl) = var "f2" $ fun_type t0 t1
        (s1,s1_decl) = var "s1" $ set_type t0
        (s2,s2_decl) = var "s2" $ set_type t1
        dec x = x ++ z3_decoration t0 ++ z3_decoration t1
        dec' x = z3_decoration t0 ++ z3_decoration t1 ++ x
