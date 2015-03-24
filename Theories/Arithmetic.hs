{-# LANGUAGE RecordWildCards #-}
module Theories.Arithmetic where

    -- Modules
import Logic.Expr
import Logic.Operator
import Logic.Theory

import Theories.FunctionTheory

    -- Libraries
import Data.List as L

    -- arithmetic
power   :: BinOperator
mult    :: BinOperator
plus    :: BinOperator
minus   :: BinOperator
less    :: BinOperator
greater :: BinOperator
leq     :: BinOperator
geq     :: BinOperator

power   = BinOperator "^" "^"           mzpow
mult    = BinOperator "*" "\\cdot"      mztimes
plus    = BinOperator "+" "+"           mzplus
minus   = BinOperator "-" "-"           mzminus
less    = BinOperator "<" "<"           mzless
greater = BinOperator ">" ">"           (flip mzless)
leq     = BinOperator "<=" "\\le"       mzle
geq     = BinOperator ">=" "\\ge"       (flip mzle)

zsum :: ExprP -> ExprP
zsum = typ_fun1 $ Fun [gT] "qsum" [fun_type gT int] int

gT :: Type
gT = VARIABLE "t"

arithmetic :: Theory
arithmetic = empty_theory { 
        types = symbol_table [IntSort,RealSort]
        , funs = symbol_table 
            [ Fun [gA] "qsum" [fun_type gA int] int ]
        , notation = arith }

arith :: Notation
arith = with_assoc empty_notation
    { new_ops     = L.map Right [power,mult,plus,leq,geq
                                ,less,greater,minus]
    , prec = [ L.map (L.map Right)
                     [ [apply]
                     , [power]
                     , [mult]
                     , [plus,minus]
                     , [mk_fun]
                     , [ equal,leq
                       , less
                       , geq,greater]]]
    , left_assoc  = [[mult],[plus]]
    , right_assoc = []
    , relations   = [equal,leq,geq,less,greater]
    , chaining    = 
          [ ((leq,leq),leq)
          , ((leq,less),less)
          , ((less,leq),less)
          , ((less,less),less)
          , ((geq,geq),geq)
          , ((geq,greater),greater)
          , ((greater,geq),greater)
          , ((greater,greater),greater) ] 
    , quantifiers = 
        [ ("\\qsum"
          , Quantifier $ \vs x y -> fromJust $ zsum $ Right $ Binder Lambda vs x y)]
    }
          