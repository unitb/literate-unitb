{-# LANGUAGE RecordWildCards, OverloadedStrings #-}
module Theories.PredCalc where

    -- Modules
import Logic.Expr
import Logic.Expr.Const
import Logic.Operator
import Logic.Theory

    -- Libraries
import Control.Lens

import qualified Data.Map.Class as M

import Prelude hiding ( pred )

import Utilities.Lens

everywhere_fun :: Fun
everywhere_fun = mk_fun [gA] (fromString'' "ew") [pred_type gA] bool

zew :: ExprP -> ExprP
zew = typ_fun1 everywhere_fun

pred :: Type
pred = pred_type gA

pimplies_fun :: Fun
pimplies_fun = mk_lifted_fun [] (fromString'' "=>") [pred,pred] pred

equiv_fun :: Fun
equiv_fun = mk_lifted_fun [] (fromString'' "equiv") [pred,pred] pred

and_fun :: Fun
and_fun = mk_lifted_fun [] (fromString'' "and") [pred,pred] pred

or_fun :: Fun
or_fun = mk_lifted_fun [] (fromString'' "or") [pred,pred] pred

neg_fun :: Fun
neg_fun = (mk_lifted_fun [] (fromString'' "not") [pred] pred)

zpimplies :: ExprP -> ExprP -> ExprP
zpimplies = typ_fun2 pimplies_fun

zpequiv :: ExprP -> ExprP -> ExprP
zpequiv   = typ_fun2 equiv_fun

zpand :: ExprP -> ExprP -> ExprP
zpand     = typ_fun2 and_fun

zpor :: ExprP -> ExprP -> ExprP
zpor      = typ_fun2 or_fun

zpneg :: ExprP -> ExprP
zpneg     = typ_fun1 neg_fun
    
pfollows :: BinOperator
pfollows = make BinOperator "pfollows" "\\pfollows" (flip zpimplies)

pimplies :: BinOperator
pimplies = make BinOperator "pimplies" "\\pimplies" zpimplies

pequiv :: BinOperator
pequiv = make BinOperator "pequiv" "\\pequiv" zpequiv

pconj :: BinOperator
pconj = make BinOperator "pand" "\\pand" zpand

pdisj :: BinOperator
pdisj = make BinOperator "por" "\\por" zpor

pneg :: UnaryOperator
pneg = make UnaryOperator "pneg" "\\pneg" zpneg

ptrue_fun :: Fun
ptrue_fun = mk_fun [gA] (fromString'' "ptrue") [] (pred_type gA)

pfalse_fun :: Fun
pfalse_fun = mk_fun [gA] (fromString'' "pfalse") [] (pred_type gA)

ptrue :: ExprP
ptrue   = Right $ FunApp ptrue_fun []

pfalse :: ExprP
pfalse  = Right $ FunApp pfalse_fun []

pred_sort :: Sort
pred_sort = DefSort (fromString'' "\\pred") (fromString'' "pred") [fromString'' "a"] $ array gA bool

pred_type :: TypeSystem t => t -> t
pred_type t = make_type pred_sort [t]

zrep_select :: ExprP -> ExprP -> ExprP
zrep_select = typ_fun2 (mk_fun [] (fromString'' "select") [pred_type gA, gA] bool)

pred_calc :: Theory
pred_calc = make_theory' "predcalc" $ do
          types .= symbol_table [pred_sort]
          funs  .= symbol_table [everywhere_fun, ptrue_fun, pfalse_fun]
          fact  .= M.singleton (label "pred_ew") (($typeCheck) $ 
                mzforall [x_decl] mztrue $ 
                        (zew x)
                    `mzeq` (mzforall [y_decl] mztrue $ zrep_select x y) )
          notation .= pred_not 
    where
        (x,x_decl) = var "x" $ pred_type t
        (y,y_decl) = var "y" t
        t = VARIABLE $ fromString'' "t"
    
    
pred_not :: Notation
pred_not = create $ do
   new_ops     .= Left pneg : map Right [pconj,pdisj,pimplies,pfollows,pequiv]
   prec .= [    [Right equal]
                : [Left  pneg ] 
                : map (map Right)
                     [ [pdisj,pconj]
                     , [pimplies,pfollows]
                     , [pequiv] ]]
   left_assoc  .= [[pequiv],[pdisj],[pconj]]
   right_assoc .= []
   relations   .= [pequiv,pimplies,pfollows]
   commands    .= 
        [ make Command "\\ptrue" "ptrue" 0 $ const ptrue
        , make Command "\\pfalse" "pfalse" 0 $ const pfalse
        , make Command "\\ew" "ew" 1 $ zew . head ]
   chaining    .= 
        [ ((pequiv,pimplies),pimplies)
        , ((pimplies,pequiv),pimplies)
        , ((pimplies,pimplies),pimplies)
        , ((pequiv,pequiv),pequiv)
        , ((pequiv,pfollows),pfollows)
        , ((pfollows,pequiv),pfollows)
        , ((pfollows,pfollows),pfollows) ] 
