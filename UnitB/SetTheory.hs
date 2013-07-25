{-# LANGUAGE BangPatterns #-}
module UnitB.SetTheory where

import Control.Monad

    -- Modules
import UnitB.Genericity
import UnitB.Theory

import Z3.Z3

    -- Libraries
import Data.List as L
import Data.Map as M hiding ( foldl ) 

--import System.IO.Unsafe

import Utilities.Format

set_sort = Sort "\\set" "set" 1
set_type t = USER_DEFINED set_sort [t]

set_theory :: Type -> Theory 
set_theory t = Theory [] types funs empty facts empty
    where
        types = symbol_table [set_sort]
        set_type = USER_DEFINED set_sort [t]
        funs = M.insert (dec "union") (Fun [t] (dec "bunion") [set_type,set_type] set_type) $
            symbol_table [
                Fun [] (dec "empty-set") [] set_type,
                Fun [] (dec "elem") [t,set_type] BOOL,
                Fun [] (dec "set-diff") [set_type,set_type] set_type,
                Fun [] (dec "mk-set") [t] set_type ]
        facts = fromList 
                [ (label $ dec "0", axm0)
                , (label $ dec "1", axm1)
--                , (label $ dec "2", axm2)
                ]
        Right axm0 = mzforall [x_decl,y_decl] ((x `zelem` zmk_set y) `mzeq` (x `mzeq` y))
        Right axm1 = mzforall [x_decl,s1_decl,s2_decl] (
                          (x `zelem` (s1 `zsetdiff` s2)) 
                    `mzeq` ( (x `zelem` s1) `mzand` mznot (x `zelem` s2) ))
--        Right axm2 = mzforall [x_decl,s1_decl] (mznot (x `zelem` zempty_set))
        (x,x_decl) = var "x" t
        (y,y_decl) = var "y" t
        (s1,s1_decl) = var "s1" set_type
        (s2,s2_decl) = var "s2" set_type
        dec x = x ++ z3_decoration t
--            Fun 
        
--typed_expr   

zempty_set   = Const [gA] "empty-set" $ set_type gA

gA = GENERIC "a"

zelem        = typ_fun2 (Fun [gA] "elem" [gA,set_type gA] BOOL)
    where 
        !() = unsafePerformIO (putStrLn "elem")
--                maybe2 $ fun2 $ Fun [gA] "elem" [gA,set_type gA] BOOL
--                typed_fun2 (\t0 s0 -> do
--                            t1 <- item_type s0
--                            unless (t0 == t1) $ Left $ format " {0} does not match the element type of {1} " t0 s0
--                            return $ Fun [gA] (dec "elem" t0) [t0, SET t1] BOOL) x y
zsetdiff     = typ_fun2 (Fun [gA] "set-diff" [set_type gA,set_type gA] $ set_type gA)
    where 
        !() = unsafePerformIO (putStrLn "set-diff")
--                maybe2 $ fun2 $ Fun [gA] "set-diff" [set_type gA,set_type gA] $ set_type gA
--                typed_fun2 $ (\s0 s1 -> do
--                            t0 <- item_type s0
--                            t1 <- item_type s1
--                            unless (t0 == t1) $ Left $ format " the element type of {0} and {1} do not match " t0 s0
--                            return $ Fun [gA] (dec "set-diff" t0) [s0,s0] s0)
zunion       = typ_fun2 (Fun [gA] "bunion" [set_type gA,set_type gA] $ set_type gA)
    where 
        !() = unsafePerformIO (putStrLn "union")
--                maybe2 $ fun2 $ Fun [gA] "bunion" [set_type gA,set_type gA] $ set_type gA
--                typed_fun2 $ (\s0 s1 -> do
--                            t0 <- item_type s0
--                            t1 <- item_type s1
--                            unless (t0 == t1) $ Left $ format " the element type of {0} and {1} do not match " t0 s0
--                            return $ Fun [gA] (dec "bunion" t0) [s0,s0] s0)
zmk_set      = typ_fun1 (Fun [gA] "mk-set" [gA] $ set_type gA)
    where 
        !() = unsafePerformIO (putStrLn "mk-set")
--                    maybe1 $ fun1 $ Fun [gA] "mk-set" [gA] $ set_type gA 
                     -- $ (\t0 -> let s0 = set_type t0 in
                     --       return $ Fun [gA] (dec "mk-set" t0) [s0,s0] s0)
zset_enum xs = foldl zunion y ys 
    where
        (y:ys) = L.map zmk_set xs

dec x t = x ++ z3_decoration t

item_type t0@(USER_DEFINED s [t]) 
        | s == set_sort         = Right t
        | otherwise             = Left $ format " {0} is not a set " t0
item_type t0                    = Left $ format " {0} is not a set " t0