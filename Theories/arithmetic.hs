{-# LANGUAGE RecordWildCards #-}
module Theories.Arithmetic where

    -- Modules
import Logic.Const
import Logic.Label
import Logic.Operator
import Logic.Theory
import Logic.Type

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

power   = BinOperator "power" "^"       mzpow
mult    = BinOperator "mult" "\\cdot"   mztimes
plus    = BinOperator "plus" "+"        mzplus
minus   = BinOperator "minus" "-"       mzminus
less    = BinOperator "less" "<"        mzless
greater = BinOperator "greater" ">"     (flip mzless)
leq     = BinOperator "le" "\\le"       mzle
geq     = BinOperator "ge" "\\ge"       (flip mzle)

arithmetic :: Theory
arithmetic = empty_theory { 
        types = symbol_table [IntSort,RealSort]
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
          , ((greater,greater),greater) ] }
          