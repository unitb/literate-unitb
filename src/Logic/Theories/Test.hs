module Logic.Theories.Test where

import Logic.Expr

import Logic.Theories.RelationTheory
import Logic.Theories.SetTheory

case0 = unify (set_type gA) (rel gA gB)
    where
        rel t1 t2 = Gen (USER_DEFINED s [t1,t2]) 
        s  = DefSort "relation" "relation" ["a","b"] (set_type $ pair_type gA gB)
        gA = GENERIC "a"
        gB = GENERIC "b"
