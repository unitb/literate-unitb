{-# LANGUAGE BangPatterns
      , RecordWildCards
      , OverloadedStrings #-}
module Logic.Theories.SetTheory where

    -- Modules
import Logic.Expr
import Logic.Expr.Const
import Logic.Operator
import Logic.Theory 
import Logic.Theory.Monad hiding (preserve)
import Logic.Proof

    -- Libraries
import Control.Arrow
import Control.Lens
import Control.Lens.Misc

import Data.Default
import Data.List as L
import Data.Map.Class as M

import Text.Printf.TH

import Utilities.MapSyntax
import Utilities.Table

as_array :: TypeSystem t => t -> Name -> AbsExpr Name t q
as_array t x = funApp (mk_lifted_fun [] x [] t) []

map_array :: Name -> Type -> [ExprP] -> ExprP
map_array name t xs = do
    xs <- sequence xs
    return $ funApp (mk_lifted_fun [] name (L.map type_of xs) t) xs

mzfinite :: (IsName n,IsQuantifier q)
         => ExprPG n Type q -> ExprPG n Type q
mzfinite = typ_fun1 finite_fun

finite_fun :: IsName n => AbsFun n Type
finite_fun = mk_fun [gA] (z3Name "finite") [set_type gA] bool

zfinite :: Expr -> Expr
zfinite e = ($typeCheck) (mzfinite $ Right e)

set_theory' :: Table Name Theory
set_theory' = singleton (makeName "sets") set_theory

set_theory :: Theory 
set_theory = Theory { .. }
    where
        t  = VARIABLE $ z3Name "t"
        t0  = VARIABLE $ z3Name "t0"
        gT = GENERIC $ z3Name "t"

        _theory'Name = z3Name "sets"
        _extends = M.empty
        _consts  = M.empty
        _theory'Dummies = M.empty
        _types = M.empty
        _theory'SyntacticThm = def
            { _associative = fromList $ L.map (first z3Name)
                    [ ("intersect",zset_all)
                    , ("union",zempty_set) ]
            , _monotonicity = fromList $
                   preserve subset_fun (L.map z3Name ["intersect","union"])
                ++ L.map (first $ z3Name *** z3Name)
                   [ ( ("=>","subset")
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
        _theory'Defs = symbol_table
                [ z3Def [gT] "empty-set" [] (set_type gT) 
                        $ zlift (set_type gT) zfalse
                , z3Def [gT] "all" [] (set_type gT) 
                        $ zlift (set_type gT) ztrue
                , z3Def [gT] "elem" [x_decl, s1_decl] bool 
                        $ ($typeCheck) (zset_select s1 x)
                , z3Def [gT] "set-diff" [s1_decl,s2_decl] (set_type gT)
                        $ ($typeCheck) $ s1 `zintersect` 
                            map_array (z3Name "not") (set_type gT) [s2]
                , z3Def [gT] "compl" [s1_decl] (set_type gT)
                        $ ($typeCheck) $ 
                            map_array (z3Name "not") (set_type gT) [s1]
                , z3Def [gT] "st-subset" [s1_decl,s2_decl] bool
                        $ ($typeCheck) $ (s1 `zsubset` s2)
                            `mzand`  mznot (s1 `mzeq` s2)
                ]
        _funs = 
            -- M.insert "union" (Fun [gT] "bunion" [set_type gT,set_type gT] $ set_type gT) $
            symbol_table
                [ comprehension_fun
                , qunion_fun
                , zpow_set_fun
                , mk_fun [gT] (z3Name "mk-set") [gT] $ set_type gT 
                , mk_fun [gT] (z3Name "finite") [set_type gT] $ bool
                ]
        _fact :: Table Label Expr
        _fact = "set" `axioms` do
                -- elem and mk-set
            $axiom $  (x `zelem` zmk_set y) .==.  x .=. y
                -- comprehension
            $axiom $        zelem y (zset r1 term)
                      .==. (mzexists [x'_decl] (x' `zelem` r1)
                                (zselect term x' .=. y))
                    -- with empty set
            $axiom $      zset r1 term .=. zmk_set y
                    .==.  mzforall [x'_decl] (zelem x' r1)
                                 (       (zselect term x' `mzeq` y) )
                -- finite
            $axiom $      mzfinite s1
                     .=> (mzfinite $ s1 `zsetdiff` s2)
            $axiom $     mzfinite s1 /\ mzfinite s2
                     .=> (mzfinite $ s1 `zunion` s2)
            $axiom $ mzfinite $ zmk_set x
            $axiom $ mzfinite $ zcast (set_type t) zempty_set
            $axiom $ zsubset s1 s2 .=> (mzfinite s2 .=> mzfinite s1)
            $axiom $ zset r1 zident .=. r1
                -- quantifier union
            $axiom $ zunion_qu (zcast (set_type t0) zempty_set) terms .=. zempty_set
            $axiom $ zunion_qu (zmk_set x') terms .=. zselect terms x'
            $axiom $    zunion_qu (r1 `zunion` r2) terms 
                    .=. zunion_qu r1 terms `zunion` zunion_qu r2 terms 
            $axiom $    mzforall [x'_decl] (x' `zelem` r1) ( zselect terms x' .=. zselect terms' x' )
                    .=> zunion_qu r1 terms .=. zunion_qu r1 terms'
            $axiom $    s2 `zelem` zpow_set s1 .=. s2 `zsubset` s1
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
zsubset       :: (IsName n,IsQuantifier q)
              => ExprPG n Type q 
              -> ExprPG n Type q 
              -> ExprPG n Type q
zstsubset     :: ExprP -> ExprP -> ExprP
zsetdiff      :: (IsName n,IsQuantifier q)
              => ExprPG n Type q 
              -> ExprPG n Type q 
              -> ExprPG n Type q
zintersect    :: ExprP -> ExprP -> ExprP
zcompl        :: ExprP -> ExprP

zunion        :: ExprP -> ExprP -> ExprP
zmk_set       :: ExprP -> ExprP
zpow_set      :: ExprP -> ExprP
zset_enum     :: [ExprP] -> ExprP

comprehension :: HOQuantifier
comprehension = UDQuant comprehension_fun gA (QTFromTerm set_sort) InfiniteWD

comprehension_fun :: IsName n => AbsFun n Type
comprehension_fun = mk_fun' [gA,gB] "set" [set_type gA, array gA gB] $ set_type gB

zcomprehension :: [Var] -> ExprP -> ExprP -> ExprP
zcomprehension = zquantifier comprehension

zrecord_set' :: MapSyntax Name ExprP ()
             -> ExprP
zrecord_set' = zrecord_set . runMap'

zrecord_set :: Map Name ExprP
            -> ExprP
zrecord_set m' = do
        let m = M.mapKeysMonotonic Field m'
            msg e = [printf|Expecting a set type for: %s\n  of type: %s|] 
                      (pretty e) (pretty $ type_of e)
            getElements :: ExprP -> Either [String] Type
            getElements e = e >>= \e -> maybe (Left [msg e]) Right $ type_of e^?_ElementType
        (r,r_decl) <- var "r" . recordTypeOfFields <$> traverseValidation getElements m
        let range = mzall $ mapWithKey (\field e -> zfield r field `zelem` e) m'
        zcomprehension [r_decl] range r

qunion :: HOQuantifier
qunion = UDQuant qunion_fun (set_type gA) QTTerm InfiniteWD

zunion_qu :: (IsQuantifier q,IsName n) => ExprPG n Type q -> ExprPG n Type q -> ExprPG n Type q
zunion_qu = typ_fun2 qunion_fun

qunion_fun :: IsName n => AbsFun n Type
qunion_fun = mk_fun' [gA,gB] "qunion" [set_type gA, array gA (set_type gB)] (set_type gB)

zset :: (IsQuantifier q,IsName n) => ExprPG n Type q -> ExprPG n Type q -> ExprPG n Type q
zset = typ_fun2 comprehension_fun

zset_select = typ_fun2 (mk_fun' [] "select" [set_type gA, gA] bool)

zempty_set   = Right $ funApp zempty_set_fun []
zset_all     = Right $ funApp zset_all_fun []
zsubset      = typ_fun2 subset_fun
zsetdiff     = typ_fun2 zsetdiff_fun
zstsubset    = typ_fun2 st_subset_fun
zintersect   = typ_fun2 zintersect_fun
zunion       = typ_fun2 zunion_fun
zcompl       = typ_fun1 zcompl_fun

zunion_fun, zintersect_fun, zcompl_fun, zempty_set_fun, zset_all_fun, zpow_set_fun :: Fun
zsetdiff_fun :: IsName n => AbsFun n Type
zunion_fun     = mk_fun' [] "union" [set_type gA,set_type gA] $ set_type gA
zsetdiff_fun   = mk_fun' [gA] "set-diff" [set_type gA,set_type gA] $ set_type gA
zintersect_fun = mk_fun' [] "intersect" [set_type gA,set_type gA] $ set_type gA
zcompl_fun     = mk_fun' [gA] "compl" [set_type gA] $ set_type gA
zempty_set_fun = mk_fun' [gA] "empty-set" [] $ set_type gA
zset_all_fun   = mk_fun' [gA] "all" [] $ set_type gA
zpow_set_fun   = mk_fun' [gA] "pow" [set_type gA] $ set_type (set_type gA)

zmk_set      = typ_fun1 (mk_fun' [gA] "mk-set" [gA] $ set_type gA)
zpow_set     = typ_fun1 zpow_set_fun
zset_enum (x:xs) = foldl zunion y ys 
    where
        y  = zmk_set x
        ys = L.map zmk_set xs
zset_enum [] = zempty_set

st_subset_fun :: IsName n => AbsFun n Type
st_subset_fun = mk_fun' [gA] "st-subset" [set_type gA,set_type gA] bool

subset_fun :: IsName n => AbsFun n Type
subset_fun = mk_fun' [] "subset" [set_type gA,set_type gA] bool

dec :: String -> Type -> String
dec x t = x ++ z3_decoration t

item_type :: Type -> Either String Type
item_type t0@(Gen s [t])
        | s == set_sort         = Right t
        | otherwise             = Left $ [printf| %s is not a set |] (pretty t0)
item_type t0                    = Left $ [printf| %s is not a set |] (pretty t0)

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

set_union       = make BinOperator "union" "\\bunion"      Direct zunion_fun
set_intersect   = make BinOperator "intersect" "\\binter"  Direct zintersect_fun
set_diff        = make BinOperator "set-diff" "\\setminus" Direct zsetdiff_fun
membership      = make BinOperator "elem" "\\in"           Direct (elem_fun gA)
subset          = make BinOperator "subset"     "\\subseteq" Direct subset_fun
superset        = make BinOperator "superset"   "\\supseteq" Flipped subset_fun
st_subset       = make BinOperator "st-subset"   "\\subset"  Direct  st_subset_fun
st_superset     = make BinOperator "st-superset" "\\supset"  Flipped st_subset_fun
compl           = make UnaryOperator "complement" "\\compl"  zcompl_fun

set_notation :: Notation
set_notation = create $ do
    new_ops     .= Left compl : 
                     L.map Right 
                     [ set_union,set_diff,membership,set_intersect
                     , subset,superset,st_subset,st_superset
                     ]
    prec .= [   [ Left compl ]
                : L.map (L.map Right)
                  [ [apply]
                  , [pair_op,set_union,set_diff,set_intersect]
                  , [ equal
                    , membership, subset
                    , st_subset, superset
                    , st_superset ] ]]
    left_assoc  .= [[set_union]]
    right_assoc .= []
    relations   .= []
    quantifiers .= [ (fromString'' "\\qset",comprehension)
                   , (fromString'' "\\qunion",qunion) ]
    commands    .= [ make Command "\\emptyset" "empty-set" 0 zempty_set_fun
                   , make Command "\\all" "all" 0 zset_all_fun
                   , make Command "\\pow" "pow" 1 zpow_set_fun
                   , make Command "\\finite" "finite" 1 finite_fun ]
    chaining    .= [ ((subset,subset),subset) 
                   , ((subset,st_subset),st_subset)
                   , ((st_subset,subset),st_subset)
                   , ((st_subset,st_subset),st_subset)
                   , ((superset,superset),superset) 
                   , ((superset,st_superset),st_superset)
                   , ((st_superset,superset),st_superset)
                   , ((st_superset,st_superset),st_superset)
                   ]  

