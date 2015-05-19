{-# LANGUAGE TemplateHaskell #-}
module Theories.RelationTheory where

import Logic.Expr
import Logic.Theory

import Theories.SetTheory

import Utilities.Tuple

relation_theory :: Theory
relation_theory = make_theory "relation" $ do
    -- rel_type <- sort_def "relation" $ \gA gB -> 
    --     set_type (pair_type gA gB)
    let rel_type gA gB = set_type (pair_type gA gB)
        rel_type :: Type -> Type -> Type
        -- id' = id :: Type -> Type
    zstar   <- command "star" $ \gA -> 
        (One $ rel_type gA gA,rel_type gA gA)
    zplus   <- command "plus" $ \gA -> 
        (One $ rel_type gA gA,rel_type gA gA)
    zseq    <- operator ";" "seq" $ \gA gB gC -> 
        ((rel_type gA gB,rel_type gB gC),rel_type gA gC)
    zlookup <- command "lookup" $ \gA gB -> 
        ((rel_type gA gB, set_type gA),set_type gB)
    zid <- function "id" $ \gA ->
        ((),rel_type gA gA)
    -- zreldom <- command "reldom" $ \gA gB ->
    --     (One $ rel_type gA gB, set_type gA)
    -- zrelran <- command "relran" $ \gA gB ->
    --     (One $ rel_type gA gB, set_type gB)
    t1  <- type_param
    t2  <- type_param
    t3  <- type_param
    rr  <- dummy "rr"  (rel_type t1 t1)
    rr' <- dummy "rr2" (rel_type t1 t1)
    r1  <- dummy "r1" (rel_type t1 t2)
    r2  <- dummy "r2" (rel_type t1 t2)
    r3  <- dummy "r3" (rel_type t2 t3)
    r4  <- dummy "r4" (rel_type t3 t1)
    x1  <- dummy "x1" t1
    x1' <- dummy "x3" t1
    x2  <- dummy "x2" t2
    s1  <- dummy "s1" $ set_type t1
    let p = mzpair x1 x1'
    $assert $ mzpair x1 x1' `zelem` zid .== x1 .= x1'
    $assert $ rr `zsubset` zstar rr
    $assert $ zid `zsubset` zstar rr
    $assert $ rr `zsubset` rr' .=> zstar rr `zsubset` zstar rr'
    $assert $ p `zelem` zstar (rr `zintersect` rr') .=> p `zelem` zstar rr
    $assert $ p `zelem` zstar rr .=> p `zelem` zstar (rr `zunion` rr')
    $assert $ (zstar rr `zseq` zstar rr) `zsubset` zstar rr
    $assert $ r1 `zsubset` r2 .=> (r1 `zseq` r3) `zsubset` (r2 `zseq` r3)
    $assert $ r1 `zsubset` r2 .=> (r4 `zseq` r1) `zsubset` (r4 `zseq` r2)
    $assert $ zplus rr .= zstar rr `zseq` rr
    $assert $ zplus rr .= rr `zseq` zstar rr
    $assert $ x2 `zelem` zlookup r1 s1 .== mzexists' [x1] (x1 `zelem` s1) (mzpair x1 x2 `zelem` r1)
    $assert $ x1 `zelem` s1 .=> 
              (    mzpair x1 x2 `zelem` r1 
               .=> x2 `zelem` zlookup r1 s1)
    -- _
