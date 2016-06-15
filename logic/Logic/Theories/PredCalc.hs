{-# LANGUAGE RecordWildCards, OverloadedStrings #-}
module Logic.Theories.PredCalc where

    -- Modules
import Logic.Expr hiding (or_fun,and_fun)
import Logic.Expr.Const hiding (or_fun,and_fun)
import Logic.Operator
import Logic.Theory

    -- Libraries
import Control.Lens
import Control.Lens.Misc

import qualified Data.Map.Class as M

import Prelude hiding ( pred )

everywhere_fun :: Fun
everywhere_fun = mk_fun [gA] [smt|ew|] [pred_type gA] bool

zew :: ExprP -> ExprP
zew = typ_fun1 everywhere_fun

pred :: Type
pred = pred_type gA

pimplies_fun :: Fun
pimplies_fun = mk_lifted_fun [] [smt|=>|] [pred,pred] pred

equiv_fun :: Fun
equiv_fun = mk_lifted_fun [] [smt|equiv|] [pred,pred] pred

and_fun :: Fun
and_fun = mk_lifted_fun [] [smt|and|] [pred,pred] pred

or_fun :: Fun
or_fun = mk_lifted_fun [] [smt|or|] [pred,pred] pred

neg_fun :: Fun
neg_fun = (mk_lifted_fun [] [smt|not|] [pred] pred)

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
pfollows = make BinOperator "pfollows" "\\pfollows" Flipped pimplies_fun

pimplies :: BinOperator
pimplies = make BinOperator "pimplies" "\\pimplies" Direct pimplies_fun

pequiv :: BinOperator
pequiv = make BinOperator "pequiv" "\\pequiv" Direct equiv_fun

pconj :: BinOperator
pconj = make BinOperator "pand" "\\pand" Direct and_fun

pdisj :: BinOperator
pdisj = make BinOperator "por" "\\por" Direct or_fun

pneg :: UnaryOperator
pneg = make UnaryOperator "pneg" "\\pneg" neg_fun

ptrue_fun :: Fun
ptrue_fun = mk_fun [gA] [smt|ptrue|] [] (pred_type gA)

pfalse_fun :: Fun
pfalse_fun = mk_fun [gA] [smt|pfalse|] [] (pred_type gA)

ptrue :: ExprP
ptrue   = Right $ funApp ptrue_fun []

pfalse :: ExprP
pfalse  = Right $ funApp pfalse_fun []

pred_sort :: Sort
pred_sort = DefSort [tex|\pred|] [smt|pred|] [[smt|a|]] $ array gA bool

pred_type :: TypeSystem t => t -> t
pred_type t = make_type pred_sort [t]

zrep_select :: ExprP -> ExprP -> ExprP
zrep_select = typ_fun2 (mk_fun [] [smt|select|] [pred_type gA, gA] bool)

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
        t = VARIABLE [smt|t|]
    
    
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
        [ make Command "\\ptrue" "ptrue" 0 ptrue_fun
        , make Command "\\pfalse" "pfalse" 0 pfalse_fun
        , make Command "\\ew" "ew" 1 everywhere_fun ]
   chaining    .= 
        [ ((pequiv,pimplies),pimplies)
        , ((pimplies,pequiv),pimplies)
        , ((pimplies,pimplies),pimplies)
        , ((pequiv,pequiv),pequiv)
        , ((pequiv,pfollows),pfollows)
        , ((pfollows,pequiv),pfollows)
        , ((pfollows,pfollows),pfollows) ] 
