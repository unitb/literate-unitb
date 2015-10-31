{-# LANGUAGE BangPatterns, RecordWildCards #-}
module Theories.SetTheory where

    -- Modules
import Logic.Expr
import Logic.Operator
import Logic.Theory hiding (preserve)
import Logic.Proof

    -- Libraries
import Control.Lens hiding ((.=))

import Data.Default
import Data.List as L
import Data.Map as M hiding ( foldl ) 

import Utilities.Format

set_type :: TypeSystem t => t -> t
set_type t = make_type set_sort [t]

as_array :: TypeSystem t => t -> String -> AbsExpr t q
as_array t x = FunApp (mk_lifted_fun [] x [] t) []

map_array :: String -> Type -> [ExprP] -> ExprP
map_array name t xs = do
    xs <- sequence xs
    return $ FunApp (mk_lifted_fun [] name (L.map type_of xs) t) xs

mzfinite :: ExprP -> ExprP
mzfinite = typ_fun1 $ mk_fun [gA] "finite" [set_type gA] bool

zfinite :: Expr -> Expr
zfinite e = ($typeCheck) (mzfinite $ Right e)

set_theory :: Theory 
set_theory = Theory { .. } -- [] types funs empty facts empty
    where
        t  = VARIABLE "t"
        t0  = VARIABLE "t0"
        gT = GENERIC "t"

        _extends = M.empty
        _consts  = M.empty
        _theoryDummies = M.empty
        _types = M.empty
        _theorySyntacticThm = def
            { _associative = fromList $ 
                    [ ("intersect",zset_all)
                    , ("union",zempty_set) ]
            , _monotonicity = fromList $
                   preserve subset_fun ["intersect","union"]
                ++ [ ( ("=>","subset")
                     , Side (Just $ Rel subset_fun Flipped) (Just $ Rel subset_fun Direct))
                   , ( ("=>","st-subset")
                     , Side (Just $ Rel subset_fun Flipped) (Just $ Rel subset_fun Direct))
                   , ( ("subset","compl")
                     , Independent (Rel subset_fun Flipped))
                   , ( ("st-subset","compl")
                     , Independent (Rel subset_fun Flipped))
                   , ( ("subset","set-diff")
                     , Side (Just $ Rel subset_fun Direct) (Just $ Rel subset_fun Flipped))
                   ]
                 }
        _defs = symbol_table 
                [ Def [gT] "empty-set" [] (set_type gT) 
                        $ zlift (set_type gT) zfalse
                , Def [gT] "all" [] (set_type gT) 
                        $ zlift (set_type gT) ztrue
                , Def [gT] "elem" [x_decl, s1_decl] bool 
                        $ ($typeCheck) (zset_select s1 x)
                , Def [gT] "set-diff" [s1_decl,s2_decl] (set_type gT)
                        $ ($typeCheck) $ s1 `zintersect` map_array "not" (set_type gT) [s2]
                , Def [gT] "compl" [s1_decl] (set_type gT)
                        $ ($typeCheck) $ map_array "not" (set_type gT) [s1]
                , Def [gT] "st-subset" [s1_decl,s2_decl] bool
                        $ ($typeCheck) $ (s1 `zsubset` s2)
                            `mzand`  mznot (s1 `mzeq` s2)
                ]
        _funs = 
            -- M.insert "union" (Fun [gT] "bunion" [set_type gT,set_type gT] $ set_type gT) $
            symbol_table
                [ comprehension_fun
                , qunion_fun
                , mk_fun [gT] "mk-set" [gT] $ set_type gT 
                , mk_fun [gT] "finite" [set_type gT] $ bool
                ]
        _fact :: Map Label Expr
        _fact = "set" `axioms` do
                -- elem and mk-set
            $axiom $  (x `zelem` zmk_set y) .==  x .= y
                -- comprehension
            $axiom $       zelem y (zset r1 term)
                      .== (mzexists [x'_decl] (x' `zelem` r1)
                                (zselect term x' .= y))
                    -- with empty set
            $axiom $     zset r1 term .= zmk_set y
                    .==  mzforall [x'_decl] (zelem x' r1)
                                 (       (zselect term x' `mzeq` y) )
                -- finite
            $axiom $      mzfinite s1
                     .=> (mzfinite $ s1 `zsetdiff` s2)
            $axiom $     mzfinite s1 /\ mzfinite s2
                     .=> (mzfinite $ s1 `zunion` s2)
            $axiom $ mzfinite $ zmk_set x
            $axiom $ mzfinite $ zcast (set_type t) zempty_set
            $axiom $ zsubset s1 s2 .=> (mzfinite s2 .=> mzfinite s1)
            $axiom $ zset r1 zident .= r1
                -- quantifier union
            $axiom $ zunion_qu (zcast (set_type t0) zempty_set) terms .= zempty_set
            $axiom $ zunion_qu (zmk_set x') terms .= zselect terms x'
            $axiom $   zunion_qu (r1 `zunion` r2) terms 
                    .= zunion_qu r1 terms `zunion` zunion_qu r2 terms 
            $axiom $    mzforall [x'_decl] (x' `zelem` r1) ( zselect terms x' .= zselect terms' x' )
                    .=> zunion_qu r1 terms .= zunion_qu r1 terms'
                -- elem over union
            -- $axiom $ mzforall [x_decl,s1_decl,s2_decl] mztrue (
            --                     (x `zelem` (s1 `zunion` s2)) 
            --             `mzeq` ( (x `zelem` s1) `mzor` (x `zelem` s2) ))
                -- elem over empty-set
    --        Right axm2 = mzforall [x_decl,s1_decl] (mznot (x `zelem` zempty_set))
            -- $axiom $ mzforall [s1_decl,s2_decl] mztrue $
            --                 ( s1 `zsubset` s2 )
            --             `mzeq` (mzforall [x_decl] mztrue ( zelem x s1 `mzimplies` zelem x s2 ))
            -- $axiom $ mzforall [s1_decl,s2_decl] mztrue $
            --                 mzand ( s1 `zsubset` s2 )
            --                       ( s2 `zsubset` s1 )
            --             `mzeq` (s1 `mzeq` s2)

            -- fromList 
            --     [ (label $ dec' "0", axm0)
            --     -- , (label $ dec' "3", axm3)
            --     -- , (label $ dec' "6", axm6)
            --     , (label $ dec' "3", axm18)
            --     , (label $ dec' "6", axm38)
            --     , (label $ dec' "7", axm1)
            --     , (label $ dec' "8", axm2)
            --     , (label $ dec' "9", axm3)
            --     , (label $ dec' "10", axm4)
            --     -- , (label $ dec' "7", axm7)
            --     ]
        _thm_depend = []
        _notation   = set_notation
                

        (x,x_decl) = var "x" t
        (x',x'_decl) = var "x" t0
        (y,_y_decl) = var "y" t
        (s1,s1_decl) = var "s1" $ set_type t
        (s2,s2_decl) = var "s2" $ set_type t
        (r1,_r1_decl) = var "r1" $ set_type t0
        (r2,_r2_decl) = var "r2" $ set_type t0
        (term,_term_decl) = var "term" $ array t0 t
        (terms,_terms_decl) = var "terms" $ array t0 (set_type t)
        (terms',_) = var "terms0" $ array t0 (set_type t)
--            dec x  = x ++ z3_decoration t
        -- dec' x = "@set@@_" ++ x
        
        _theorems = M.empty

zset_select   :: ExprP -> ExprP -> ExprP
zempty_set    :: ExprP
zset_all      :: ExprP
zelem         :: IsQuantifier q => ExprPG Type q -> ExprPG Type q -> ExprPG Type q
zsubset       :: ExprP -> ExprP -> ExprP
zstsubset     :: ExprP -> ExprP -> ExprP
zsetdiff      :: ExprP -> ExprP -> ExprP
zintersect    :: ExprP -> ExprP -> ExprP
zcompl        :: ExprP -> ExprP

zunion        :: ExprP -> ExprP -> ExprP
zmk_set       :: ExprP -> ExprP
zset_enum     :: [ExprP] -> ExprP

comprehension :: HOQuantifier
comprehension = UDQuant comprehension_fun gA (QTFromTerm set_sort) InfiniteWD

comprehension_fun :: Fun
comprehension_fun = mk_fun [gA,gB] "set" [set_type gA, array gA gB] $ set_type gB

zcomprehension :: [Var] -> ExprP -> ExprP -> ExprP
zcomprehension = zquantifier comprehension

qunion :: HOQuantifier
qunion = UDQuant qunion_fun (set_type gA) QTTerm InfiniteWD

zunion_qu :: IsQuantifier q => ExprPG Type q -> ExprPG Type q -> ExprPG Type q
zunion_qu = typ_fun2 qunion_fun

qunion_fun :: Fun
qunion_fun = mk_fun [gA,gB] "qunion" [set_type gA, array gA (set_type gB)] (set_type gB)

zset :: IsQuantifier q => ExprPG Type q -> ExprPG Type q -> ExprPG Type q
zset = typ_fun2 comprehension_fun

zset_select = typ_fun2 (mk_fun [] "select" [set_type gA, gA] bool)

zelem        = typ_fun2 (mk_fun [gA] "elem" [gA,set_type gA] bool)
zsetdiff     = typ_fun2 (mk_fun [gA] "set-diff" [set_type gA,set_type gA] $ set_type gA)


zempty_set   = Right $ FunApp (mk_fun [gA] "empty-set" [] $ set_type gA) []
zset_all     = Right $ FunApp (mk_fun [gA] "all" [] $ set_type gA) []
zsubset      = typ_fun2 subset_fun
zstsubset    = typ_fun2 st_subset_fun
zintersect   = typ_fun2 (mk_fun [] "intersect" [set_type gA,set_type gA] $ set_type gA)
zunion       = typ_fun2 (mk_fun [] "union" [set_type gA,set_type gA] $ set_type gA)
zcompl       = typ_fun1 (mk_fun [gA] "compl" [set_type gA] $ set_type gA)

zmk_set      = typ_fun1 (mk_fun [gA] "mk-set" [gA] $ set_type gA)
zset_enum (x:xs) = foldl zunion y ys 
    where
        y  = zmk_set x
        ys = L.map zmk_set xs
zset_enum [] = zempty_set

st_subset_fun :: Fun
st_subset_fun = mk_fun [gA] "st-subset" [set_type gA,set_type gA] bool

subset_fun :: Fun
subset_fun = mk_fun [] "subset" [set_type gA,set_type gA] bool

dec :: String -> Type -> String
dec x t = x ++ z3_decoration t

item_type :: Type -> Either String Type
item_type t0@(Gen s [t])
        | s == set_sort         = Right t
        | otherwise             = Left $ format " {0} is not a set " t0
item_type t0                    = Left $ format " {0} is not a set " t0

    -- set theory
set_union   :: BinOperator
set_intersect :: BinOperator
set_diff    :: BinOperator
membership  :: BinOperator
subset      :: BinOperator
superset    :: BinOperator
st_subset   :: BinOperator
st_superset :: BinOperator
compl       :: UnaryOperator

set_union       = BinOperator "union" "\\bunion"        zunion
set_intersect   = BinOperator "intersect" "\\binter" zintersect
set_diff        = BinOperator "set-diff" "\\setminus"   zsetdiff
membership      = BinOperator "elem" "\\in"       zelem
subset          = BinOperator "subset"     "\\subseteq" zsubset
superset        = BinOperator "superset"   "\\supseteq" (flip zsubset)
st_subset       = BinOperator "st-subset"   "\\subset" zstsubset
st_superset     = BinOperator "st-superset" "\\supset" (flip zstsubset)
compl           = UnaryOperator "complement" "\\compl" zcompl

set_notation :: Notation
set_notation = empty_notation
    & new_ops     .~ Left compl : 
                     L.map Right 
                     [ set_union,set_diff,membership,set_intersect
                     , subset,superset,st_subset,st_superset
                     ]
    & prec .~ [   [ Left compl ]
                : L.map (L.map Right)
                  [ [apply]
                  , [pair_op,set_union,set_diff,set_intersect]
                  , [ equal
                    , membership, subset
                    , st_subset, superset
                    , st_superset ] ]]
    & left_assoc  .~ [[set_union]]
    & right_assoc .~ []
    & relations   .~ []
    & quantifiers .~ [ ("\\qset",comprehension)
                     , ("\\qunion",qunion) ]
    & commands    .~ [ Command "\\emptyset" "emptyset" 0 $ const $ zempty_set
                     , Command "\\all" "all" 0 $ const $ zset_all
                     , Command "\\finite" "finite" 1 $ from_list mzfinite ]
    & chaining    .~ [ ((subset,subset),subset) 
                     , ((subset,st_subset),st_subset)
                     , ((st_subset,subset),st_subset)
                     , ((st_subset,st_subset),st_subset)
                     , ((superset,superset),superset) 
                     , ((superset,st_superset),st_superset)
                     , ((st_superset,superset),st_superset)
                     , ((st_superset,st_superset),st_superset)
                     ]  

