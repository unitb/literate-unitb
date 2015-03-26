{-# LANGUAGE BangPatterns, RecordWildCards #-}
module Theories.FunctionTheory where

    -- Modules
import Logic.Expr
import Logic.Operator
import Logic.Theory

import Theories.SetTheory hiding ( dec )

    -- Libraries
import           Data.Map
import           Data.List as L

ztfun   :: ExprP -> ExprP -> ExprP
zdom    :: ExprP -> ExprP
zran    :: ExprP -> ExprP
zdomsubt    :: ExprP -> ExprP -> ExprP
zdomrest    :: ExprP -> ExprP -> ExprP
zrep_select :: ExprP -> ExprP -> ExprP
zovl        :: ExprP -> ExprP -> ExprP
zmk_fun     :: ExprP -> ExprP -> ExprP
zempty_fun  :: Expr
zlambda     :: [Var] -> ExprP -> ExprP -> ExprP
zstore      :: ExprP -> ExprP -> ExprP -> ExprP

ztfun = typ_fun2 (Fun [gA,gB] "tfun" [set_type gA, set_type gB] $ fun_set gA gB)

zdom = typ_fun1 (Fun [gA,gB] "dom" [fun_type gA gB] $ set_type gA)

zran = typ_fun1 (Fun [gA,gB] "ran" [fun_type gA gB] $ set_type gB)

zdomsubt = typ_fun2 (Fun [gA,gB] "dom-subt" [set_type gA, fun_type gA gB] $ fun_type gA gB)

zdomrest = typ_fun2 (Fun [gA,gB] "dom-rest" [set_type gA, fun_type gA gB] $ fun_type gA gB)

zrep_select = typ_fun2 (Fun [] "select" [fun_type gA gB, gA] $ maybe_type gB)

zovl    = typ_fun2 (Fun [gA,gB] "ovl" [ft,ft] ft)
    where
        ft = fun_type gA gB

zmk_fun = typ_fun2 (Fun [gA,gB] "mk-fun" [gA,gB] $ fun_type gA gB)

--zset = typ_fun1 (Fun [gA,gB] "set" [array gA $ maybe_type gB] $ set_type gB)

zempty_fun = FunApp (Fun [gA,gB] "empty-fun" [] $ fun_type gA gB) []

zlambda = zquantifier qlambda

lambda :: ExprP -> ExprP -> ExprP
lambda = typ_fun2 lambda_fun

lambda_fun :: Fun
lambda_fun = Fun [gA,gB] "lambda" [array gA bool,array gA gB] $ fun_type gA gB

qlambda :: HOQuantifier
qlambda = UDQuant lambda_fun gA (QT fun_type) InfiniteWD

zstore        = typ_fun3 $ Fun [] "store" [
        array (gB) $ gA, 
        gB, gA] $ 
    array gB gA

zinjective :: ExprP -> ExprP
zinjective  = typ_fun1 $ Fun [gA,gB] "injective" [fun_type gA gB] bool

-- zsurjective = typ_fun1 $ Fun [gA,gB] "surjective" 

--zselect = typ_fun2 (Fun [] "select" [ARRAY gA gB, gA] gB)

fun_set :: Type -> Type -> Type
t0 :: Type
t1 :: Type

fun_set t0 t1 = set_type (fun_type t0 t1)

t0 = VARIABLE "t0"
t1 = VARIABLE "t1"

function_theory :: Theory 
function_theory = Theory { .. }
    where        
        extends =  singleton "set" set_theory
        
        consts = empty
        dummies = empty
        theorems = empty
        
--        set_ths  = 
        fun_set t0 t1 = set_type (fun_type t0 t1)
        types    = symbol_table [fun_sort]
        defs = empty
        funs =
            symbol_table 
                [  lambda_fun
                ,  Fun [t0,t1] "empty-fun" [] $ fun_type t0 t1
                ,  Fun [t0,t1] "dom"    [fun_type t0 t1] $ set_type t0
                ,  Fun [t0,t1] "ran"    [fun_type t0 t1] $ set_type t1
                ,  Fun [t0,t1] "apply"  [fun_type t0 t1,t0] t1
                ,  Fun [t0,t1] "ovl"    [fun_type t0 t1,fun_type t0 t1] $ fun_type t0 t1
                ,  Fun [t0,t1] "dom-rest" [set_type t0,fun_type t0 t1] $ fun_type t0 t1
                ,  Fun [t0,t1] "dom-subt" [set_type t0,fun_type t0 t1] $ fun_type t0 t1
                ,  Fun [t0,t1] "mk-fun" [t0,t1] $ fun_type t0 t1 
                ,  Fun [t0,t1] "tfun" [set_type t0,set_type t1] $ fun_set t0 t1
                ,  Fun [t0,t1] "injective" [fun_type t0 t1] bool
                ]
            where
                t0 = GENERIC "t0"
                t1 = GENERIC "t1"

        thm_depend = []

        fact = fromList $ zip (L.map (label . dec') [0..])
                [ axm0, axm1, axm4, axm6
                , axm7, axm10, axm11, axm12
                , axm13, axm14, axm15, axm16
                , axm17, axm19, axm20
                , axm25, axm21, axm22, axm23
                , axm24, axm26, axm27, axm28
                , axm29, axm30, axm31, axm32
                , axm33, axm34, axm35, axm36
                , axm37, axm39
                ]

        notation = function_notation

            -- dom and empty-fun
        axm1 = fromJust (zdom (as_fun $ Right zempty_fun) `mzeq` Right zempty_set)
            -- empty-fun and ovl
--        axm2 = fromJust $ mzforall [f1_decl] mztrue ( (f1 `zovl` Right zempty_fun) `mzeq` f1 )
--        axm3 = fromJust $ mzforall [f1_decl] mztrue ( (Right zempty_fun `zovl` f1) `mzeq` f1 )
            -- dom and mk-fun
        axm4 = fromJust $ mzforall [x_decl,y_decl] mztrue ( zdom (x `zmk_fun` y) `mzeq` zmk_set x )
            -- ovl and apply
        axm6 = fromJust $ mzforall [f1_decl,f2_decl,x_decl] mztrue ( 
                        (x `zelem` zdom f2) 
            `mzimplies` (zapply (f1 `zovl` f2) x `mzeq` zapply f2 x))
        axm7 = fromJust $ mzforall [f1_decl,f2_decl,x_decl] mztrue ( 
                        (mzand (x `zelem` zdom f1)
                               (mznot $ x `zelem` zdom f2))
            `mzimplies` (zapply (f1 `zovl` f2) x `mzeq` zapply f1 x))
            -- apply and mk-fun
        axm11 = fromJust $ mzforall [x_decl,y_decl] mztrue ( 
                (zmk_fun x y `zapply` x) `mzeq` y )
            -- dom-rest and apply
        axm12 = fromJust $ mzforall [f1_decl,s1_decl,x_decl] mztrue (
                        (mzand (x `zelem` s1)
                               (x `zelem` zdom f1))
            `mzimplies` (zapply (s1 `zdomrest` f1) x `mzeq` zapply f1 x) )
            -- dom-subst and apply
        axm13 = fromJust $ mzforall [f1_decl,s1_decl,x_decl] mztrue (
                        (x `zelem` (zdom f1 `zsetdiff` s1))
            `mzimplies` (zapply (s1 `zdomsubt` f1) x `mzeq` zapply f1 x) )
            -- empty-fun as a total function
--        axm8 = fromJust $ mzforall [s2_decl] 
--            ( as_fun (Right zempty_fun) `zelem` ztfun (as_dom $ Right zempty_set) s2 )
            -- dom and overload
        axm0 = fromJust $ mzforall [f1_decl,f2_decl] mztrue (
                           (zdom (f1 `zovl` f2))
                    `mzeq` (zdom f1 `zunion` zdom f2) )
            -- dom and tfun
            -- dom-rest and tfun
            -- dom-subst and tfun
            -- dom-rest and dom
--        axm9  = fromJust $ mzforall [f1_decl,s1_decl] mztrue ((zdom (s1 `zdomrest` f1)) `mzeq` (s1 `zintersect` zdom f1))
            -- dom-subst and dom
        axm10 = fromJust $ mzforall [f1_decl,s1_decl] mztrue ((zdom (s1 `zdomsubt` f1)) `mzeq` (zdom f1 `zsetdiff` s1))
        
        axm39 = fromJust $ mzforall [r1_decl,term_decl,x_decl] mztrue $
                           zrep_select (lambda r term) x
                    `mzeq` zite (zselect r x) (zjust $ zselect term x) znothing

--        axm14 = fromJust $ mzforall [f1_decl] mztrue (
--                    mzeq (zlambda [x_decl] mzfalse (zapply f1 x))
--                         $ Right zempty_fun)
        
--        axm15 = fromJust $ mzforall [f1_decl,x2_decl] mztrue (
--                    mzeq (zlambda [x_decl] (x `mzeq` x2) (zapply f1 x))
--                         $ zmk_fun x2 (zapply f1 x2) )
            -- encoding of dom rest, dom subt, dom, apply, empty-fun, mk-fun
            -- empty-fun
            -- NOTE: this is not type correct (in literate-unitb) because we are using array operations on
            -- a pfun. It works because pfun [a,b] is represented as ARRAY [a,Maybe b], and Z3 considers them
            -- type correct.
        axm14 = fromJust $ mzforall [x_decl] mztrue 
                (      zrep_select (Right zempty_fun) x
                `mzeq` zcast (maybe_type t1) znothing )
            -- mk-fun
        axm15 = fromJust $ mzforall [x_decl,x2_decl,y_decl] mztrue 
                (      zrep_select (zmk_fun x y) x2
                `mzeq` zite (mzeq x x2) (zjust y) znothing )
            -- apply
        axm16 = fromJust $ mzforall [x_decl,f1_decl,f2_decl] mztrue 
                (      zrep_select (zovl f1 f2) x
                `mzeq` zite (mzeq (zrep_select f2 x) znothing)
                            (zrep_select f1 x)
                            (zrep_select f2 x) )
            -- domain
        axm17 = fromJust $ mzforall [x_decl,f1_decl] mztrue 
                (      zset_select (zdom f1) x
                `mzeq` mznot (zrep_select f1 x `mzeq` znothing))
            -- set comprehension

        axm19 = fromJust $ mzforall [x_decl,y_decl,f1_decl] mztrue 
                (      (zelem x (zdom f1) `mzand` (zapply f1 x `mzeq` y))
                `mzeq` (zrep_select f1 x `mzeq` zjust y))

            -- ovl and mk_fun
        axm20 = fromJust $ mzforall [f1_decl,x2_decl,x_decl,y_decl] mztrue ( 
                        mznot (x `mzeq` x2)
            `mzimplies` (zapply (f1 `zovl` zmk_fun x y) x2 `mzeq` zapply f1 x2))
        axm25 = fromJust $ mzforall [f1_decl,x_decl,y_decl] mztrue ( 
                        (zapply (f1 `zovl` zmk_fun x y) x `mzeq` y))
        
            -- ran and empty-fun
        axm21 = fromJust $  
                    zran (zcast (fun_type t0 t1) $ Right zempty_fun) 
            `mzeq` Right zempty_set

            -- ran and elem
        axm22 = fromJust $ mzforall [f1_decl,y_decl] mztrue (
                        ( y `zelem` zran f1 ) 
                    `mzeq` ( mzexists [x_decl] mztrue 
                            ( (x `zelem` zdom f1) `mzand` (zapply f1 x `mzeq` y))))
        
            -- ran mk-fun
        axm23 = fromJust $ mzforall [x_decl,y_decl] mztrue $
                        zran (zmk_fun x y) `mzeq` zmk_set y
        
            -- ran ovl
        axm24 = fromJust $ mzforall [f1_decl,f2_decl] mztrue $
                        zran (f1 `zovl` f2) `zsubset` (zran f1 `zunion` zran f2)
--                       zite (mzeq (zrep_select f1 x) znothing)
--                            (zrep_select f2 x)
--                            (zrep_select f1 x) )
        axm26 = fromJust $ mzforall [f1_decl,s1_decl,s2_decl] mztrue $
                        (f1 `zelem` ztfun s1 s2)
                `mzeq`  ( (s1 `mzeq` zdom f1) `mzand` (zran f1 `zsubset` s2))
            -- definition of injective
        axm27 = fromJust $ mzforall [f1_decl] mztrue $
                        zinjective f1
                `mzeq`  (mzforall [x_decl,x2_decl] 
                                    (mzand  (x `zelem` zdom f1) 
                                            (x2 `zelem` zdom f1))
                            $ (zapply f1 x `mzeq` zapply f1 x2) 
                            `mzimplies` (x `mzeq` x2) )
            -- injective, domsubt and ran (with mk_set)
        axm28 = fromJust $ mzforall [f1_decl,x_decl] 
                        (zinjective f1 `mzand` (x `zelem` zdom f1))
                        (       zran (zmk_set x `zdomsubt` f1)
                        `mzeq`  (zran f1 `zsetdiff` zmk_set (zapply f1 x))
                            ) 
            -- domsub, apply and mk-set
        axm29 = fromJust $ mzforall [f1_decl,x_decl,x2_decl] 
                        ((mznot $ x `mzeq` x2) `mzand` (x2 `zelem` zdom f1)) $
                        (       zapply (zmk_set x `zdomsubt` f1) x2
                        `mzeq`  zapply f1 x2
                            )
            -- domrest, apply and mk-set
        axm30 = fromJust $ mzforall [f1_decl,x_decl] 
                        (x `zelem` zdom f1) $
                        (       zapply (zmk_set x `zdomrest` f1) x
                        `mzeq`  zapply f1 x
                            )
            -- domsub, apply 
        axm31 = fromJust $ mzforall [f1_decl,x_decl,s1_decl] 
                        ((mznot $ x `zelem` s1) `mzand` (x `zelem` zdom f1)) $
                        (       zapply (s1 `zdomsubt` f1) x
                        `mzeq`  zapply f1 x
                            )
            -- domrest, apply
        axm32 = fromJust $ mzforall [f1_decl,x_decl,s1_decl] 
                        ((x `zelem` s1) `mzand` (x `zelem` zdom f1)) $
                        (       zapply (s1 `zdomrest` f1) x
                        `mzeq`  zapply f1 x                
                            )
            -- '.', '\in', 'ran'
        axm33 = fromJust $ mzforall [f1_decl,x_decl] 
                        ( x `zelem` zdom f1 ) $
                        zapply f1 x `zelem` zran f1
            -- '.', '\in', 'ran', 'domsub'
        axm34 = fromJust $ mzforall [f1_decl,x_decl,s1_decl] 
                        ( x `zelem` (zdom f1 `zsetdiff` s1) ) $
                        zapply f1 x `zelem` zran (s1 `zdomsubt` f1)
            -- '.', '\in', 'ran', 'domrest'
        axm35 = fromJust $ mzforall [f1_decl,x_decl,s1_decl] 
                        ( x `zelem` (zdom f1 `zintersect` s1) ) $
                        zapply f1 x `zelem` zran (s1 `zdomrest` f1)
            -- ran.(f | x -> _) with f injective and x in dom.f
        axm36 = fromJust $ mzforall [f1_decl,x_decl,y_decl] 
                        ( (x `zelem` zdom f1) `mzand` zinjective f1 ) $
                                (zran $ f1 `zovl` zmk_fun x y)
                        `mzeq`  (         (zran f1 `zsetdiff` zmk_set (f1 `zapply` x))
                                 `zunion` zmk_set y)
            -- ran.(f | x -> _) with x not in dom.f
        axm37 = fromJust $ mzforall [f1_decl,x_decl,y_decl] 
                        ( mznot $ x `zelem` zdom f1 ) $
                                (zran $ f1 `zovl` zmk_fun x y)
                        `mzeq`  (zran f1 `zunion` zmk_set y)
            -- 
        as_fun e = zcast (fun_type t0 t1) e
    
        (x,x_decl) = var "x" t0
        (x2,x2_decl) = var "x2" t0
        (y,y_decl) = var "y" t1
        (f1,f1_decl) = var "f1" $ fun_type t0 t1
        (f2,f2_decl) = var "f2" $ fun_type t0 t1
        (s1,s1_decl) = var "s1" $ set_type t0
        (s2,s2_decl) = var "s2" $ set_type t1
        (term,term_decl) = var "t" $ array t0 t1
        (r,r1_decl) = var "r" $ array t0 bool
        -- (s2,s2_decl) = var "s2" $ set_type t1
--        dec' x = z3_decoration t0 ++ z3_decoration t1 ++ x
        dec' x = "@function@@_" ++ pad ++ show x
          where
            pad = if x < 10 then "0" else ""
        
    -- notation
overload    :: BinOperator
mk_fun      :: BinOperator
total_fun   :: BinOperator
domrest     :: BinOperator
domsubt     :: BinOperator

overload    = BinOperator "overload" "|"        zovl
mk_fun      = BinOperator "mk-fun" "\\fun"      zmk_fun
total_fun   = BinOperator "total-fun" "\\tfun"  ztfun
domrest     = BinOperator "dom-rest" "\\domres" zdomrest
domsubt     = BinOperator "dom-subt" "\\domsub" zdomsubt

function_notation :: Notation
function_notation = with_assoc empty_notation
    { new_ops     = L.map Right 
                [ overload,mk_fun
                , total_fun,domrest
                , domsubt]
    , prec = [ L.map (L.map Right) 
                 [ [apply]
                 , [mk_fun]
                 , [overload]
                 , [domrest,domsubt] 
                 , [ equal ] ]
             , L.map (L.map Right)
               [ [ total_fun ]
               , [ membership ]] ]
    , left_assoc  = [[overload]]
    , right_assoc = [[domrest,domsubt]]
    , commands    = 
                [ Command "\\emptyfun" "emptyfun" 0 $ const $ Right zempty_fun
                , Command "\\dom" "dom" 1 $ zdom . head
                , Command "\\ran" "ran" 1 $ zran . head
                , Command "\\injective" "injective" 1 $ zinjective . head
                ]
    , quantifiers = [ ("\\qfun",qlambda) ]
    , relations   = []
    , chaining    = []  } 
