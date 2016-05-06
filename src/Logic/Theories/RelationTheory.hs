module Logic.Theories.RelationTheory where

    -- Modules
import Logic.Expr
import Logic.Theory
import Logic.Theory.Monad

import Logic.Theories.SetTheory

    -- Libraries
import Data.Functor.Identity

relation_theory :: Theory
relation_theory = make_theory "relations" $ do
    -- rel_type <- sort_def "relation" $ \gA gB -> 
    --     set_type (pair_type gA gB)
    let rel_type gA gB = set_type (pair_type gA gB)
        rel_type :: Type -> Type -> Type
        -- id' = id :: Type -> Type
    (star_op,zstar) <- unary [tex|\star|] [smt|star|] $ \gA -> 
        (Identity $ rel_type gA gA,rel_type gA gA)
    (plus_op,zplus) <- unary [tex|\plus|] [smt|plus|] $ \gA -> 
        (Identity $ rel_type gA gA,rel_type gA gA)
    (seq_op,zseq)  <- operator [tex|;|] [smt|seq|] $ \gA gB gC -> 
        ((rel_type gA gB,rel_type gB gC),rel_type gA gC)
    zlookup <- command [tex|lookup|] $ \gA gB -> 
        ((rel_type gA gB, set_type gA),set_type gB)
    zid <- command [tex|id|] $ \gA ->
        ((),rel_type gA gA)
    zasrel  <- command [tex|asrel|] $ \gA ->
        (Identity $ set_type gA,rel_type gA gA)
    zreldom <- command [tex|reldom|] $ \gA gB ->
        (Identity $ rel_type gA gB, set_type gA)
    -- zrelran <- command "relran" $ \gA gB ->
    --     (One $ rel_type gA gB, set_type gB)
    -- (domres,zreldomres) <- operator "\\rdomres" "rdomres" $ \gA gB ->
    --     ( (set_type gA,rel_type gA gB)
    --     , rel_type gA gB)
    let zreldomres s r = zasrel s `zseq` r
    t1  <- type_param
    t2  <- type_param
    t3  <- type_param
    t4  <- type_param
    rr  <- dummy "rr"  (rel_type t1 t1)
    rr' <- dummy "rr2" (rel_type t1 t1)
    r1  <- dummy "r1" (rel_type t1 t2)
    r2  <- dummy "r2" (rel_type t1 t2)
    r3  <- dummy "r3" (rel_type t2 t3)
    r4  <- dummy "r4" (rel_type t3 t1)
    r5  <- dummy "r5" (rel_type t3 t4)
    -- r6  <- dummy "r6" (rel_type t2 t1)
    x1  <- dummy "x1" t1
    x1' <- dummy "x3" t1
    x2  <- dummy "x2" t2
    x3  <- dummy "x4" t3
    x4  <- dummy "x5" t4
    s1  <- dummy "s1" $ set_type t1
    associativity (fromString'' "seq") zid
    preserve subset_fun $ map fromString'' ["seq","star"]
    precedence  [] 
        [[star_op,plus_op],[seq_op]] 
        [Right set_union,Right set_diff,Right set_intersect]
    left_associativity
        [seq_op] -- ranres
    let p  = mzpair x1 x1'
        p' = mzpair x1 x2
        p1 = mzpair x3 x4
        p2 = mzpair x1 x4
    -- $assert $   x1 `zelem` zreldom r1 
    --         .==. mzexists' [x2] mztrue (mzpair x1 x2 `zelem` r1)
        -- def of dom
    $assert $     mzpair x1 x2 `zelem` r1
              .=> x1 `zelem` zreldom r1
        -- dom over domres
    $assert $ zreldom (s1 `zreldomres` r1) .=. s1 `zintersect` zreldom r1
        -- p |-> _ in {p} <| _
    $assert $ p' `zelem` (zmk_set x1 `zreldomres` r1) .==. p' `zelem` r1
        -- singleton set to singleton rel
    $assert $ zasrel (zmk_set x1) .=. zmk_set (mzpair x1 x1)
        -- assoc of ;
    $assert $ (r1 `zseq` r3) `zseq` r5 .=. r1 `zseq` (r3 `zseq` r5)
        -- left monotonicity 
    $assert $ r1 `zsubset` r2 .=> (r1 `zseq` r3) `zsubset` (r2 `zseq` r3)
        -- right monotonicity 
    $assert $ r1 `zsubset` r2 .=> (r4 `zseq` r1) `zsubset` (r4 `zseq` r2)
        -- <| and ; assoc
    -- $assert $ (s1 `zreldomres` r1) `zseq` r3 .=. s1 `zreldomres` (r1 `zseq` r3)
        -- *(_ \/ _) to *(_ ; _)
    $assert $ zstar (rr `zunion` rr') .=. zstar (zstar rr `zseq` rr') `zseq` zstar rr
    $assert $ zstar (rr `zunion` rr') .=. zstar rr' `zseq` zstar (rr `zseq` zstar rr')
        -- unfold
    $assert $ (zstar rr `zseq` rr) `zunion` zid .=. zstar rr
    $assert $ (rr `zseq` zstar rr) `zunion` zid .=. zstar rr
        -- ; over \/ 
    $assert $ (r1 `zunion` r2) `zseq` r3 .=. (r1 `zseq` r3) `zunion` (r2 `zseq` r3)
    $assert $ r4 `zseq` (r1 `zunion` r2)  .=. (r4 `zseq` r1) `zunion` (r4 `zseq` r2)
    $assert $ zmk_set p `zseq` zset_all .=. zmk_set x1 `zreldomres` zset_all 
    $assert $ zmk_set p' `zseq` zset_all `zseq` zmk_set p1 .=. zmk_set p2
    -- $assert $ zstar (r1 `zseq` r6) .=. ( r1 `zseq` zstar (r6 `zseq` r1) `zseq` r6 ) `zunion` zid
    $assert $ zasrel (zmk_set x1) `zseq` zset_all `zseq` zasrel (zmk_set x2)
              .=. zmk_set (mzpair x1 x2)

    $assert $ mzpair x1 x1' `zelem` zid .==. x1 .=. x1'
    $assert $ zid `zseq` r1 .=. r1
    $assert $ r1 `zseq` zid .=. r1
    $assert $ rr `zsubset` zstar rr
    -- $assert $ zid `zsubset` zstar rr
    $assert $ rr `zsubset` rr' .=> zstar rr `zsubset` zstar rr'
    $assert $ p `zelem` zstar (rr `zintersect` rr') .=> p `zelem` zstar rr
    $assert $ p `zelem` zstar rr .=> p `zelem` zstar (rr `zunion` rr')
    $assert $ zstar rr `zseq` zstar rr .=. zstar rr
    $assert $ r1 `zsubset` r2 .=> (r1 `zseq` r3) `zsubset` (r2 `zseq` r3)
    $assert $ r1 `zsubset` r2 .=> (r4 `zseq` r1) `zsubset` (r4 `zseq` r2)
    $assert $ zplus rr .=. zstar rr `zseq` rr
    $assert $ zplus rr .=. rr `zseq` zstar rr
    $assert $ x2 `zelem` zlookup r1 s1 .==. mzexists' [x1] (x1 `zelem` s1) (mzpair x1 x2 `zelem` r1)
    $assert $ x1 `zelem` s1 .=> 
              (    mzpair x1 x2 `zelem` r1 
               .=> x2 `zelem` zlookup r1 s1)
    -- $assert $ x2 `zelem` zlookup r1 s1 .==. mzpair x1 x2 `zelem` r1
    -- _
