module Logic.Theories where

import Logic.Expr.Classes
import Logic.Names

import Logic.Theories.Arithmetic
import Logic.Theories.FunctionTheory
import Logic.Theories.PredCalc
import Logic.Theories.RelationTheory
import Logic.Theories.SetTheory
import Logic.Theory

import Utilities.Table

supportedTheories :: Table Name Theory
supportedTheories = symbol_table
    [ set_theory
    , function_theory
    , relation_theory
    , arithmetic
    , pred_calc ]

preludeTheories :: Table Name Theory
preludeTheories = symbol_table
    [ arithmetic
    , basic_theory ]
