{-# LANGUAGE BangPatterns, RecordWildCards #-}
module Theories.FunctionTheory where

    -- Modules
import Logic.Const
import Logic.Expr
import Logic.Genericity
import Logic.Label
import Logic.Operator
import Logic.Theory
import Logic.Type

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
zset        :: ExprP -> ExprP
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

zset = typ_fun1 (Fun [gA,gB] "set" [fun_type gA gB] $ set_type gB)
--zset = typ_fun1 (Fun [gA,gB] "set" [array gA $ maybe_type gB] $ set_type gB)

zempty_fun = Const [gA,gB] "empty-fun" $ fun_type gA gB

    -- encoding is done on an expression per expression basis
zlambda xs mx my = do
        x <- zcast bool mx
        y <- my
        return $ Binder Lambda xs x y

zstore        = typ_fun3 $ Fun [] "store" [
        array (gB) $ gA, 
        gB, gA] $ 
    array gB gA

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
        funs =
            symbol_table 
                [  Fun [t0,t1] "empty-fun" [] $ fun_type t0 t1
                ,  Fun [t0,t1] "dom"    [fun_type t0 t1] $ set_type t0
                ,  Fun [t0,t1] "ran"    [fun_type t0 t1] $ set_type t1
                ,  Fun [t0,t1] "apply"  [fun_type t0 t1,t0] t1
                ,  Fun [t0,t1] "ovl"    [fun_type t0 t1,fun_type t0 t1] $ fun_type t0 t1
                ,  Fun [t0,t1] "dom-rest" [set_type t0,fun_type t0 t1] $ fun_type t0 t1
                ,  Fun [t0,t1] "dom-subt" [set_type t0,fun_type t0 t1] $ fun_type t0 t1
                ,  Fun [t0,t1] "mk-fun" [t0,t1] $ fun_type t0 t1 
                ,  Fun [t0,t1] "tfun" [set_type t0,set_type t1] $ fun_set t0 t1
                ,  Fun [t0,t1] "set" [fun_type t0 t1] $ set_type t1
                ]
            where
                t0 = GENERIC "t0"
                t1 = GENERIC "t1"

        thm_depend = []

        fact = fromList 
                [ (label $ dec' "00", axm0)
                , (label $ dec' "01", axm1)
--                , (label $ dec "2", axm2)
--                , (label $ dec "3", axm3)
                , (label $ dec' "02", axm4)
--                , (label $ dec "5", axm5)
                , (label $ dec' "03", axm6)
                , (label $ dec' "04", axm7)
--                , (label $ dec' "5", axm8)
--                , (label $ dec "3", axm9)
                , (label $ dec' "05", axm10)
                , (label $ dec' "06", axm11)
                , (label $ dec' "07", axm12)
                , (label $ dec' "08", axm13)
                    -- encoding of dom rest, dom subt, dom, apply, empty-fun, mk-fun
                , (label $ dec' "09", axm14)
                , (label $ dec' "10", axm15)
                , (label $ dec' "11", axm16)
                , (label $ dec' "12", axm17)
                , (label $ dec' "13", axm18)
                , (label $ dec' "14", axm19)
                , (label $ dec' "15", axm20)
                , (label $ dec' "16", axm25)
                , (label $ dec' "17", axm21)
                , (label $ dec' "18", axm22)
                , (label $ dec' "19", axm23)
                , (label $ dec' "20", axm24)
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
                            (zdom f1 `zunion` zdom f2) 
                    `mzeq` (zdom (f1 `zovl` f2)))
            -- dom and tfun
            -- dom-rest and tfun
            -- dom-subst and tfun
            -- dom-rest and dom
--        axm9  = fromJust $ mzforall [f1_decl,s1_decl] mztrue ((zdom (s1 `zdomrest` f1)) `mzeq` (s1 `zintersect` zdom f1))
            -- dom-subst and dom
        axm10 = fromJust $ mzforall [f1_decl,s1_decl] mztrue ((zdom (s1 `zdomsubt` f1)) `mzeq` (zdom f1 `zsetdiff` s1))
        
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
        axm18 = fromJust $ mzforall [y_decl,f1_decl] mztrue 
                (      zelem y (zset f1)
                `mzeq` (mzexists [x_decl] (x `zelem` zdom f1)
                            (zapply f1 x `mzeq` y)))

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
        as_fun e = zcast (fun_type t0 t1) e
    
        (x,x_decl) = var "x" t0
        (x2,x2_decl) = var "x2" t0
        (y,y_decl) = var "y" t1
        (f1,f1_decl) = var "f1" $ fun_type t0 t1
        (f2,f2_decl) = var "f2" $ fun_type t0 t1
        (s1,s1_decl) = var "s1" $ set_type t0
        -- (s2,s2_decl) = var "s2" $ set_type t1
--        dec' x = z3_decoration t0 ++ z3_decoration t1 ++ x
        dec' x = "@function@@_" ++ x
        
    -- notation
overload    :: BinOperator
mk_fun      :: BinOperator
total_fun   :: BinOperator
domrest     :: BinOperator
domsubt     :: BinOperator

overload    = BinOperator "overload" "|"        zovl
mk_fun      = BinOperator "mk-fun" "\\tfun"     zmk_fun
total_fun   = BinOperator "total-fun" "\\tfun"  ztfun
domrest     = BinOperator "dom-rest" "\\domres" zdomrest
domsubt     = BinOperator "dom-subt" "\\domsub" zdomsubt

function_notation :: Notation
function_notation = with_assoc empty_notation
    { new_ops     = L.map Right [overload,mk_fun,total_fun,domrest,domsubt]
    , prec = [ L.map (L.map Right) 
                 [ [apply]
                 , [mk_fun]
                 , [overload]
                 , [domrest,domsubt] 
                 , [ equal ] ]]
    , left_assoc  = [[overload]]
    , right_assoc = [[domrest,domsubt]]
    , commands    = 
                [ Command "\\emptyfun" "emptyfun" 0 $ const $ Right zempty_fun
                , Command "\\dom" "dom" 1 $ zdom . head
                , Command "\\ran" "ran" 1 $ zran . head
                ]
    , relations   = []
    , chaining    = []  } 
