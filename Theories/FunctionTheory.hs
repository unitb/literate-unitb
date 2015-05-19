{-# LANGUAGE BangPatterns, RecordWildCards, TemplateHaskell #-}
module Theories.FunctionTheory where

    -- Modules
import Logic.Expr
import Logic.Operator
import Logic.Theory

import Theories.SetTheory hiding ( dec )

    -- Libraries
-- import Control.Applicative hiding (empty)

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
zempty_fun  :: ExprP
zlambda     :: [Var] -> ExprP -> ExprP -> ExprP
zstore      :: ExprP -> ExprP -> ExprP -> ExprP

ztfun = typ_fun2 (mk_fun [gA,gB] "tfun" [set_type gA, set_type gB] $ fun_set gA gB)

zdom = typ_fun1 (mk_fun [gA,gB] "dom" [fun_type gA gB] $ set_type gA)

zran = typ_fun1 (mk_fun [gA,gB] "ran" [fun_type gA gB] $ set_type gB)

zdomsubt = typ_fun2 (mk_fun [gA,gB] "dom-subt" [set_type gA, fun_type gA gB] $ fun_type gA gB)

zdomrest = typ_fun2 (mk_fun [gA,gB] "dom-rest" [set_type gA, fun_type gA gB] $ fun_type gA gB)

zrep_select = typ_fun2 (mk_fun [] "select" [fun_type gA gB, gA] $ maybe_type gB)

zovl    = typ_fun2 (mk_fun [gA,gB] "ovl" [ft,ft] ft)
    where
        ft = fun_type gA gB

zmk_fun = typ_fun2 (mk_fun [gA,gB] "mk-fun" [gA,gB] $ fun_type gA gB)

--zset = typ_fun1 (Fun [gA,gB] "set" [array gA $ maybe_type gB] $ set_type gB)

zempty_fun = Right $ FunApp (mk_fun [gA,gB] "empty-fun" [] $ fun_type gA gB) []

zlambda = zquantifier qlambda

lambda :: ExprP -> ExprP -> ExprP
lambda = typ_fun2 lambda_fun

lambda_fun :: Fun
lambda_fun = mk_fun [gA,gB] "lambda" [set_type gA,array gA gB] $ fun_type gA gB

qlambda :: HOQuantifier
qlambda = UDQuant lambda_fun gA (QTSort fun_sort) InfiniteWD

zstore        = typ_fun3 $ mk_fun [] "store" [
        array (gB) $ gA, 
        gB, gA] $ 
    array gB gA

zinjective :: ExprP -> ExprP
zinjective  = typ_fun1 $ mk_fun [gA,gB] "injective" [fun_type gA gB] bool

-- zsurjective = typ_fun1 $ Fun [gA,gB] "surjective" 

--zselect = typ_fun2 (Fun [] "select" [ARRAY gA gB, gA] gB)

fun_set :: Type -> Type -> Type
t0 :: Type
t1 :: Type

fun_set t0 t1 = set_type (fun_type t0 t1)

-- right_fun :: Fun
-- right_fun = mk_fun [t0] "right" [maybe_type t0, maybe_type t0] (maybe_type t0)

-- zright :: ExprP -> ExprP -> ExprP
-- zright = typ_fun2 right_fun

t0 = VARIABLE "t0"
t1 = VARIABLE "t1"

function_theory :: Theory 
function_theory = Theory { .. }
    where        
        extends =  singleton "set" set_theory
        
        consts   = empty
        dummies  = empty
        theorems = empty
        
--        set_ths  = 
        fun_set t0 t1 = set_type (fun_type t0 t1)
        types    = symbol_table [fun_sort]
        defs = 
            symbol_table
                [ 
                  -- Def [t0,t1] "ovl" [f1_decl,f2_decl] (fun_type t0 t1) 
                  --   ($fromJust$ lright f1 f2)
                  -- Def [t0,t1] "empty-fun" [] (fun_type t0 t1) 
                  --   ($fromJust$ zlift (fun_type t0 t1) <$> znothing)
                -- , Def [t0,t1] "apply"  [f1_decl,x_decl] t1 
                --     ($fromJust$ zfromJust $ zrep_select f1 x)
                -- , Def [t0,t1] "injective" [f1_decl] bool
                --     ($fromJust $ (mzforall [x_decl,x2_decl] 
                --                           (mzand  (x `zelem` zdom f1) 
                --                                   (x2 `zelem` zdom f1))
                --                       $   (zapply f1 x .= zapply f1 x2) 
                --                              .=> (x .= x2) ))
                ]
            where
                -- lright = typ_fun2 (Fun [t1] "right" Lifted [fun_type t0 t1,fun_type t0 t1] (fun_type t0 t1))                
                -- zfromJust = typ_fun1 (mk_fun [] "fromJust" [maybe_type t0] t0)

                -- t0 = GENERIC "t0"
                -- t1 = GENERIC "t1"
                -- (f1,f1_decl) = var "f1" $ fun_type t0 t1
                -- (f2,f2_decl) = var "f2" $ fun_type t0 t1
                -- (x,x_decl) = var "x" t0
        
        funs =
            symbol_table 
                [  lambda_fun
                -- ,  right_fun
                ,  mk_fun [t0,t1] "empty-fun" [] (fun_type t0 t1)
                ,  mk_fun [t0,t1] "apply"  [fun_type t0 t1,t0] t1
                ,  mk_fun [t0,t1] "dom"    [fun_type t0 t1] $ set_type t0
                ,  mk_fun [t0,t1] "ran"    [fun_type t0 t1] $ set_type t1
                ,  mk_fun [t0,t1] "ovl"    [fun_type t0 t1,fun_type t0 t1] $ fun_type t0 t1
                ,  mk_fun [t0,t1] "dom-rest" [set_type t0,fun_type t0 t1] $ fun_type t0 t1
                ,  mk_fun [t0,t1] "dom-subt" [set_type t0,fun_type t0 t1] $ fun_type t0 t1
                ,  mk_fun [t0,t1] "mk-fun" [t0,t1] $ fun_type t0 t1 
                ,  mk_fun [t0,t1] "tfun" [set_type t0,set_type t1] $ fun_set t0 t1
                ,  mk_fun [t0,t1] "injective" [fun_type t0 t1] bool
                ]
            where
                t0 = GENERIC "t0"
                t1 = GENERIC "t1"

        thm_depend = []

        _fact = "function" `axioms` do
            $axiom $ zdom (as_fun zempty_fun) .= zempty_set
    --         $axiom $ zright m (zjust x) .= zjust x
    --         $axiom $ zright m znothing .= m
    --         $axiom $ zright m m .= m
            $axiom $ lambda zempty_set term .= zempty_fun
            $axiom $ zdom (lambda r term) .= r
            $axiom $   lambda (zmk_set x) term .= zmk_fun x (zselect term x) 
            $axiom $    lambda r term `zovl` zmk_fun x (zselect term x)
                     .= lambda (r `zunion` zmk_set x) term
            $axiom $   lambda r term `zovl` lambda r' term
                    .= lambda (r `zunion` r') term

            $axiom $    f1 `zovl` zempty_fun .= f1
            $axiom $    zempty_fun `zovl` f1 .= f1
                -- dom and mk-fun
            $axiom $ zdom (x `zmk_fun` y) .= zmk_set x
                -- ovl and apply
            $axiom $        (x `zelem` zdom f2) 
                        .=> (zapply (f1 `zovl` f2) x .= zapply f2 x)
            $axiom $      (x `zelem` zdom f1)
                       /\ (mznot $ x `zelem` zdom f2)
                .=> (zapply (f1 `zovl` f2) x .= zapply f1 x)
                -- apply and mk-fun
            $axiom $  zmk_fun x y `zapply` x .= y 
                -- dom-rest and apply
            $axiom $ (
                            (mzand (x `zelem` s1)
                                   (x `zelem` zdom f1))
                .=> (zapply (s1 `zdomrest` f1) x .= zapply f1 x) )
                -- dom-subst and apply
            $axiom $    x `zelem` (zdom f1 `zsetdiff` s1)
                    .=> zapply (s1 `zdomsubt` f1) x .= zapply f1 x 
                -- empty-fun as a total function
            $axiom $ as_fun zempty_fun `zelem` ztfun (as_dom zempty_set) s2
                -- dom and overload
            $axiom $   (zdom (f1 `zovl` f2))
                    .= (zdom f1 `zunion` zdom f2) 
                -- dom and tfun
                -- dom-rest and tfun
                -- dom-subst and tfun
                -- dom-rest and dom
            $axiom $ zdom (s1 `zdomrest` f1) .= s1 `zintersect` zdom f1
                -- dom-subst and dom
            $axiom $ (zdom (s1 `zdomsubt` f1)) .= (zdom f1 `zsetdiff` s1)
            
    --         $axiom $     zrep_select (lambda r term) x
    --                  .=  zite (zelem x r) (zjust $ zselect term x) znothing

            $axiom $     x `zelem` r .=> zapply (lambda r term) x .= zselect term x

    --             -- encoding of dom rest, dom subt, dom, apply, empty-fun, mk-fun
    --             -- empty-fun
    --             -- NOTE: this is not type correct (in literate-unitb) because we are using array operations on
    --             -- a pfun. It works because pfun [a,b] is represented as ARRAY [a,Maybe b], and Z3 considers them
    --             -- type correct.
    --         -- $axiom $ (   zrep_select zempty_fun x
    --         --           .= zcast (maybe_type t1) znothing )
    --             -- mk-fun
    --         $axiom $ (   zrep_select (zmk_fun x y) x2
    --                   .= zite (mzeq x x2) (zjust y) znothing )
    --             -- apply
    --         -- $axiom $ (   zrep_select (zovl f1 f2) x
    --         --           .= zite (zrep_select f2 x .= znothing)
    --         --                     (zrep_select f1 x)
    --         --                     (zrep_select f2 x) )
            --     -- domain
            -- $axiom $ 
            --         (      zset_select (zdom f1) x
            --         .= mznot (zrep_select f1 x .= znothing))
    --             -- set comprehension

            -- $axiom$ zrep_select (lambda r term) x .= zite (x `zelem` r) (zjust $ zselect term x) znothing

                -- Super duper important 
            $axiom $      (zelem x (zdom f1) /\ (zapply f1 x .= y))
                     .==  (zrep_select f1 x .= zjust y)

                -- ovl and mk_fun
            $axiom $        mznot (x .= x2)
                       .=> (zapply (f1 `zovl` zmk_fun x y) x2 .= zapply f1 x2)
            $axiom $       (zapply (f1 `zovl` zmk_fun x y) x .= y)
            
                -- ran and empty-fun
            $axiom $     zran (zcast (fun_type t0 t1) zempty_fun) 
                      .= zempty_set

                -- ran and elem
            $axiom $    ( y `zelem` zran f1 ) 
                    .== ( mzexists [x_decl] mztrue 
                                ( (x `zelem` zdom f1) /\ (zapply f1 x .= y)))
            
                -- ran mk-fun
            $axiom $   zran (zmk_fun x y) .= zmk_set y
            
    --             -- ran ovl
    --         $axiom $   zran (f1 `zovl` f2) `zsubset` (zran f1 `zunion` zran f2)
    -- --                       zite (mzeq (zrep_select f1 x) znothing)
    -- --                            (zrep_select f2 x)
    -- --                            (zrep_select f1 x) )
            $axiom $     (f1 `zelem` ztfun s1 s2)
                    .==  (s1 .= zdom f1) /\ (zran f1 `zsubset` s2)
                -- definition of injective
            $axiom $     zinjective f1
                    .==  (mzforall [x_decl,x2_decl] 
                                        (mzand  (x `zelem` zdom f1) 
                                                (x2 `zelem` zdom f1))
                                $   (zapply f1 x .= zapply f1 x2) 
                                .=> (x .= x2) )
            $axiom $     zinjective $ as_fun zempty_fun
            --     -- injective, domsubt and ran (with mk_set)
            -- $axiom $         zinjective f1 /\ (x `zelem` zdom f1)
            --             .=>       zran (zmk_set x `zdomsubt` f1)
            --                  .=  (zran f1 `zsetdiff` zmk_set (zapply f1 x))
                                
    --             -- domsub, apply and mk-set
    --         $axiom $        (mznot $ x .= x2) /\ (x2 `zelem` zdom f1)
    --                 .=>         zapply (zmk_set x `zdomsubt` f1) x2
    --                         .=  zapply f1 x2
                                
            --     -- domrest, apply and mk-set
            -- $axiom $        (x `zelem` zdom f1)
            --          .=>    (    zapply (zmk_set x `zdomrest` f1) x
            --                  .=  zapply f1 x )
    --             -- domsub, apply 
    --         $axiom $        ((mznot $ x `zelem` s1) /\ (x `zelem` zdom f1))
    --                  .=>    (    zapply (s1 `zdomsubt` f1) x
    --                          .=  zapply f1 x )
    --             -- domrest, apply
    --         $axiom $        ((x `zelem` s1) /\ (x `zelem` zdom f1))
    --                  .=>    (    zapply (s1 `zdomrest` f1) x
    --                          .=  zapply f1 x )
                -- '.', '\in', 'ran'
            $axiom $        ( x `zelem` zdom f1 )
                     .=>    zapply f1 x `zelem` zran f1
                -- '.', '\in', 'ran', 'domsub'
            $axiom $        ( x `zelem` (zdom f1 `zsetdiff` s1) )
                     .=>    zapply f1 x `zelem` zran (s1 `zdomsubt` f1)
                -- '.', '\in', 'ran', 'domrest'
            $axiom $        ( x `zelem` (zdom f1 `zintersect` s1) )
                     .=>    zapply f1 x `zelem` zran (s1 `zdomrest` f1)
                -- ran.(f | x -> _) with f injective and x in dom.f
            $axiom $        (x `zelem` zdom f1) /\ zinjective f1
                     .=>            (zran $ f1 `zovl` zmk_fun x y)
                               .=   (zran f1 `zsetdiff` zmk_set (f1 `zapply` x))
                                     `zunion` zmk_set y
                -- ran.(f | x -> _) with x not in dom.f
            $axiom $        ( mznot $ x `zelem` zdom f1 )
                     .=>         (zran $ f1 `zovl` zmk_fun x y)
                             .=  (zran f1 `zunion` zmk_set y)

        notation = function_notation

        as_fun e = zcast (fun_type t0 t1) e
        as_dom e = zcast (set_type t0) e

        (x,x_decl) = var "x" t0
        (x2,x2_decl) = var "x2" t0
        (y,_y_decl) = var "y" t1
        (f1,_f1_decl) = var "f1" $ fun_type t0 t1
        (f2,_f2_decl) = var "f2" $ fun_type t0 t1
        (s1,_s1_decl) = var "s1" $ set_type t0
        (s2,_s2_decl) = var "s2" $ set_type t1
        (term,_term_decl) = var "t" $ array t0 t1
        (r,_r_decl) = var "r" $ set_type t0
        (r',_r'_decl) = var "r0" $ set_type t0
        -- (m,_m_decl) = var "m" $ maybe_type t0
        -- (s2,s2_decl) = var "s2" $ set_type t1
--        dec' x = z3_decoration t0 ++ z3_decoration t1 ++ x
        -- _dec' x = "@function@@_" ++ pad ++ show (x :: Int)
        --   where
        --     pad = if x < 10 then "0" else ""
        
    -- notation
overload    :: BinOperator
mk_fun_op   :: BinOperator
total_fun   :: BinOperator
domrest     :: BinOperator
domsubt     :: BinOperator

overload    = BinOperator "overload" "|"        zovl
mk_fun_op   = BinOperator "mk-fun" "\\fun"      zmk_fun
total_fun   = BinOperator "total-fun" "\\tfun"  ztfun
domrest     = BinOperator "dom-rest" "\\domres" zdomrest
domsubt     = BinOperator "dom-subt" "\\domsub" zdomsubt

function_notation :: Notation
function_notation = with_assoc empty_notation
    { new_ops     = L.map Right 
                [ overload,mk_fun_op
                , total_fun,domrest
                , domsubt]
    , prec = [ L.map (L.map Right) 
                 [ [apply]
                 , [mk_fun_op]
                 , [overload]
                 , [domrest,domsubt] 
                 , [ equal ] ]
             , L.map (L.map Right)
               [ [ total_fun ]
               , [ membership ]] ]
    , left_assoc  = [[overload]]
    , right_assoc = [[domrest,domsubt]]
    , commands    = 
                [ Command "\\emptyfun" "emptyfun" 0 $ const zempty_fun
                , Command "\\dom" "dom" 1 $ zdom . head
                , Command "\\ran" "ran" 1 $ zran . head
                , Command "\\injective" "injective" 1 $ zinjective . head
                ]
    , quantifiers = [ ("\\qfun",qlambda) ]
    , relations   = []
    , chaining    = []  } 
