module UnitB.SetTheory where

import Data.Map

import UnitB.Theory

import Z3.Const
import Z3.Def

set_theory :: Type -> Theory 
set_theory t = Theory [] types funs empty facts empty
    where
        types = symbol_table [set_sort]
        set_sort = Sort "\\set" "set" 1
        set_type = USER_DEFINED set_sort [t]
        funs = symbol_table [
            Fun "elem" [t,set_type] BOOL,
            Fun "set-diff" [set_type,set_type] set_type,
            Fun "mk-set" [t] set_type ]
        facts = fromList 
            [ (label "0", zforall [x_decl,y_decl] ((x `zelem` zmk_set y) `zeq` (x `zeq` y)))
            , (label "1", zforall [x_decl,s1_decl,s2_decl] (
                          (x `zelem` (s1 `zsetdiff` s2)) 
                    `zeq` ( (x `zelem` s1) `zand` znot (x `zelem` s2) )))
            ]
        (x,x_decl) = var "x" t
        (y,y_decl) = var "y" t
        (s1,s1_decl) = var "s1" set_type
        (s2,s2_decl) = var "s2" set_type
--            Fun 
        
