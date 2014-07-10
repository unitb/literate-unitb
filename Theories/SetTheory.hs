{-# LANGUAGE BangPatterns, RecordWildCards #-}
module Theories.SetTheory where

    -- Modules
import Logic.Expr
import Logic.Operator
import Logic.Theory

    -- Libraries
import Data.List as L
import Data.Map as M hiding ( foldl ) 

import Utilities.Format

set_sort :: Sort
set_sort = DefSort "\\set" "set" ["a"] (array (GENERIC "a") bool)

set_type :: TypeSystem t => t -> t
set_type t = make_type set_sort [t]

as_array :: TypeSystem t => t -> AbsExpr t -> AbsExpr t
as_array t x = FunApp (Fun [] ("(as const " ++ show (as_tree t) ++ ")") [] t) [x]

map_array :: String -> Type -> [ExprP] -> ExprP
map_array name t xs = do
    xs <- sequence xs
    return $ FunApp (Fun [] ("(_ map " ++ name ++ ")") (L.map type_of xs) t) xs

set_theory :: Theory 
set_theory = Theory { .. } -- [] types funs empty facts empty
    where
        t  = VARIABLE "t"
        gT = GENERIC "t"

        extends = M.empty
        consts  = M.empty
        dummies = M.empty
        types = symbol_table [set_sort]
        defs = symbol_table 
                [ Def [gT] "empty-set" [] (set_type gT) 
                        (ztypecast "const" (set_type gT) zfalse)
                , Def [gT] "elem" [x_decl, s1_decl] bool 
                        (fromJust $ zset_select s1 x)
                , Def [gT] "set-diff" [s1_decl,s2_decl] (set_type gT)
                        (fromJust $ s1 `zintersect` map_array "not" (set_type gT) [s2])
                , Def [gT] "compl" [s1_decl] (set_type gT)
                        (fromJust $ map_array "not" (set_type gT) [s1])
                ]
        funs = 
            -- M.insert "union" (Fun [gT] "bunion" [set_type gT,set_type gT] $ set_type gT) $
            symbol_table [
                Fun [gT] "mk-set" [gT] $ set_type gT ]
        fact :: Map Label Expr
        fact = fromList 
                [ (label $ dec' "0", axm0)
                -- , (label $ dec' "3", axm3)
                -- , (label $ dec' "6", axm6)
                -- , (label $ dec' "7", axm7)
                ]
        thm_depend = []
        notation   = set_notation
                
            -- elem and mk-set
        axm0 = fromJust $ mzforall [x_decl,y_decl] mztrue 
                    ((x `zelem` zmk_set y) `mzeq` (x `mzeq` y))
            -- elem over union
        -- axm3 = fromJust $ mzforall [x_decl,s1_decl,s2_decl] mztrue (
        --                     (x `zelem` (s1 `zunion` s2)) 
        --             `mzeq` ( (x `zelem` s1) `mzor` (x `zelem` s2) ))
            -- elem over empty-set
--        Right axm2 = mzforall [x_decl,s1_decl] (mznot (x `zelem` zempty_set))
        -- axm6 = fromJust $ mzforall [s1_decl,s2_decl] mztrue $
        --                 ( s1 `zsubset` s2 )
        --             `mzeq` (mzforall [x_decl] mztrue ( zelem x s1 `mzimplies` zelem x s2 ))
        -- axm7 = fromJust $ mzforall [s1_decl,s2_decl] mztrue $
        --                 mzand ( s1 `zsubset` s2 )
        --                       ( s2 `zsubset` s1 )
        --             `mzeq` (s1 `mzeq` s2)
        (x,x_decl) = var "x" t
        (y,y_decl) = var "y" t
        (s1,s1_decl) = var "s1" $ set_type t
        (s2,s2_decl) = var "s2" $ set_type t
--            dec x  = x ++ z3_decoration t
        dec' x = "@set@@_" ++ x
        
        theorems = M.empty

zset_select   :: ExprP -> ExprP -> ExprP
zempty_set    :: Expr
zelem         :: ExprP -> ExprP -> ExprP
zsubset       :: ExprP -> ExprP -> ExprP
zsetdiff      :: ExprP -> ExprP -> ExprP
zintersect    :: ExprP -> ExprP -> ExprP
zcompl        :: ExprP -> ExprP

zunion        :: ExprP -> ExprP -> ExprP
zmk_set       :: ExprP -> ExprP
zset_enum     :: [ExprP] -> ExprP

zset_select = typ_fun2 (Fun [] "select" [set_type gA, gA] bool)

zelem        = typ_fun2 (Fun [gA] "elem" [gA,set_type gA] bool)
zsetdiff     = typ_fun2 (Fun [gA] "set-diff" [set_type gA,set_type gA] $ set_type gA)


zempty_set   = Const [gA] "empty-set" $ set_type gA
zsubset      = typ_fun2 (Fun [] "subset" [set_type gA,set_type gA] bool)
zintersect   = typ_fun2 (Fun [] "intersect" [set_type gA,set_type gA] $ set_type gA)
zunion       = typ_fun2 (Fun [] "union" [set_type gA,set_type gA] $ set_type gA)
zcompl       = typ_fun1 (Fun [gA] "compl" [set_type gA] $ set_type gA)

zmk_set      = typ_fun1 (Fun [gA] "mk-set" [gA] $ set_type gA)
zset_enum (x:xs) = foldl zunion y ys 
    where
        y  = zmk_set x
        ys = L.map zmk_set xs
zset_enum [] = return zempty_set

dec :: String -> Type -> String
dec x t = x ++ z3_decoration t

item_type :: Type -> Either String Type
item_type t0@(Gen (USER_DEFINED s [t]))
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
membership      = BinOperator "membership" "\\in"       zelem
subset          = BinOperator "subset"     "\\subseteq" zsubset
superset        = BinOperator "superset"   "\\supseteq" (flip zsubset)
st_subset       = BinOperator "st-subset"   "\\subset" zsubset
st_superset     = BinOperator "st-superset" "\\supset" (flip zsubset)
compl           = UnaryOperator "complement" "\\compl" zcompl

set_notation :: Notation
set_notation = with_assoc empty_notation
    { new_ops     = Left compl : 
                    L.map Right 
                    [ set_union,set_diff,membership,set_intersect
                    , subset,superset,st_subset,st_superset
                    ]
    , prec = [   [ Left compl ]
               : L.map (L.map Right)
                 [ [apply]
                 , [set_union,set_diff,set_intersect]
                 , [ equal
                   , membership, subset ] ]]
    , left_assoc  = [[set_union]]
    , right_assoc = []
    , relations   = []
    , commands    = [Command "\\emptyset" "emptyset" 0 $ const $ Right zempty_set]
    , chaining    = [ ((subset,subset),subset) 
                    , ((subset,st_subset),st_subset)
                    , ((st_subset,subset),st_subset)
                    , ((st_subset,st_subset),st_subset)
                    , ((superset,superset),superset) 
                    , ((superset,st_superset),st_superset)
                    , ((st_superset,superset),st_superset)
                    , ((st_superset,st_superset),st_superset)
                    ]  }
