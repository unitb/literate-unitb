module UnitB.Genericity where

import Control.Monad

import Data.Foldable as F
    hiding ( foldl )
import Data.Map as M 
    hiding ( foldl, map, union, unions )
import qualified Data.Map as M
import Data.Set as S 
    hiding ( map, fromList, insert, foldl )

import Data.Graph

import Prelude as L

import Z3.Z3 hiding ( type_of )

import Tests.UnitTest

data Unification = Uni
    { left_to_right :: Map String Type
    , right_to_left :: Map String Type
    , vertices :: Map String Vertex
    , dependencies :: Graph 
    }

suffix_generics :: String -> Type -> Type
suffix_generics _ BOOL = BOOL
suffix_generics _ INT = INT
suffix_generics _ REAL = REAL
suffix_generics xs (GENERIC x) = GENERIC (x ++ "@" ++ xs)
suffix_generics xs (USER_DEFINED s ts) = USER_DEFINED s $ map (suffix_generics xs) ts

    -- A
unify_aux :: Type -> Type -> Maybe (Map String Type)
unify_aux BOOL BOOL = Just
unify_aux INT INT   = Just
unify_aux REAL REAL = Just
unify_aux t0@(GENERIC x) t1@(GENERIC y) u
        | x == y = Just u { 
        | True   = Nothing
unify_aux (GENERIC x) t
        | S.null $ generics t = Just $ M.singleton x t
        | otherwise           = Nothing
unify_aux t (GENERIC x)
        | S.null $ generics t = Just $ M.singleton x t
        | otherwise           = Nothing
unify_aux (USER_DEFINED x xs) (USER_DEFINED y ys) 
        | x == y && length xs == length ys = foldl f (Just M.empty) (zip xs ys)
        | otherwise                        = Nothing
    where
        f mr (x,y) = do
                r0 <- mr
                r1 <- unify x y
                merge_inst r0 r1
unify_aux (SET t0) (SET t1) = unify t0 t1
unify_aux _ _ = Nothing

    -- merge type instances
merge_inst :: Map String Type -> Map String Type -> Maybe (Map String Type)
merge_inst r0 r1 = foldWithKey h (Just M.empty) (M.map Just r0 `union` M.map Just r1)
    where
        union xs ys = unionWith g xs ys
        g mx my = do
                x <- mx
                y <- my
                guard (x == y)
                return x
        h k (Just x) (Just m) = Just $ insert k x m
        h _ _ _               = Nothing

class Generic a where
    generics :: a -> Set String
    
instance Generic Type where
    generics BOOL = S.empty
    generics INT  = S.empty
    generics REAL = S.empty
    generics (GENERIC s)        = S.singleton s
    generics (ARRAY t0 t1)      = generics t0 `S.union` generics t1
    generics (USER_DEFINED s ts)= unions $ map generics ts
    generics (SET t)            = generics t  

--instance Generic Expr where
--    d

instance Generic Fun where
    generics (Fun _ ts t) = unions (generics t : map generics ts)

--map_type f t@INT                 = t
--map_type f t@REAL                = t
--map_type f t@BOOL                = t
--map_type f t@(ARRAY t0 t1)       = ARRAY (f t0) (f t1)
--map_type f t@(GENERIC _)         = t
--map_type f t@(USER_DEFINED s ts) = USER_DEFINED s $ map f ts
--map_type f (SET t)               = SET $ f t

--fold_type

instantiate :: Map String Type -> Type -> Type
instantiate m t = f t
    where
        f (GENERIC x) = m ! x
        f t           = rewrite f t

specialize :: Map String Type -> Expr -> Expr
specialize m e = f e
    where
        f (Const x t)       = Const x $ g t
        f (Word x)          = Word $ h x
        f x@(FunApp (Fun n ts t) args) = rewrite f $ FunApp (Fun n (map g ts) $ g t) args
        f x@(Binder q vs e) = rewrite f $ Binder q (map h vs) e
        g t = instantiate m t
        h (Var x t) = Var x $ g t

-- is_type_correct

type_of :: Expr -> Maybe (Type, Map String Type)
type_of (Const _ t)      = Just (t, M.empty)
type_of (Word (Var _ t)) = Just (t, M.empty)
type_of (FunApp (Fun n ts r) args) 
        | length ts == length args = do
                m <- foldM f M.empty (zip ts args)
                let r0 = instantiate m r
                return (r0,m)
        | otherwise = Nothing
    where
        f m2 (t1, x) = do
            (t0, m0) <- type_of x
            m1 <- unify t0 t1
--            m2 <- mm
            m3 <- merge_inst m0 m1
            merge_inst m2 m3

--generic_fun_count e = f 0 e
--    where
--        f n e = h e + visit f n e
--        h (Word v) = g v
--        h (Const _ t) = S.size $ generics t
--        h (FunApp (Fun _ ts t) xs) = S.size $ generics t + L.sum (map (S.size . generics) ts)
--        h (Binder q vs x) = L.sum $ map g vs
--        g (Var _ t) = S.size $ generics t

make_gen_param_unique e = f 0 e
    where
        f e = rewrite f e

    ----------------
    -- UNIT TESTS --
    ----------------
test_case = Case "genericity" test True

test = test_cases 
        [  Case "unification, t0" (return $ unify gtype stype0) (Just $ fromList [("c",INT), ("b",REAL)])
        ,  Case "unification, t1" (return $ unify gtype stype1) (Just $ fromList [("c",SET INT), ("b",REAL)])
        ,  Case "unification, t2" (return $ unify gtype stype2) Nothing
        ,  Case "type instantiation" (return $ instantiate (fromList [("c", SET INT),("b",REAL)]) gtype) stype1
        ,  Case "type inference 0" case2 result2
        ,  Case "type inference 1" case3 result3
--        ,  Case "type inference 2" case4 result4
                -- does not work because we cannot match 
                -- a generic parameter to a generic expression
        ,  Case "type inference 3" case5 result5
        ,  Case "type inference 4" case6 result6
        ]
    where
        fun_sort = Sort "\\tfun" "fun" 2
        gtype    = USER_DEFINED fun_sort [GENERIC "c", SET $ GENERIC "b"]
        
        stype0   = USER_DEFINED fun_sort [INT, SET REAL]
        stype1   = USER_DEFINED fun_sort [SET INT, SET REAL]
        stype2   = USER_DEFINED fun_sort [SET INT, REAL]

(case2,result2) = (return $ type_of p, Just (BOOL, fromList [("a",INT)]))
    where
        gA = GENERIC "a"
        x1 = Word $ Var "x1" (SET INT)
        x2 = Word $ Var "x2" (SET INT)
        x3 = Word $ Var "x3" (SET INT)
        y  = Word $ Var "y" INT
        z  = Word $ Var "z" REAL
        union  = Fun "union" [SET gA,SET gA] $ SET gA
        member = Fun "member" [gA, SET gA] BOOL
        p = FunApp member [y, FunApp union [x1,x2]]

--case3   :: IO (Maybe (Type, Map String Type))
--result3 :: Maybe (Type, Map String Type)
--(case3,result3) = (return $ type_of p, Just (BOOL, fromList [("a",INT),("b",SET INT)]))
( case3,result3,case5,result5,case6,result6 ) = ( 
                    return $ specialize (fromList [("a",GENERIC "b")]) $ FunApp union [x3,x4]
                    , FunApp (Fun "union" [SET gB,SET gB] $ SET gB) [x3,x4] 
--                    , return $ type_of pp
--                    , Just (BOOL, fromList [("a",INT),("b",SET INT)])
                    , return p
                    , q
                    , return pp
                    , qq
                    )
    where
        gA = GENERIC "a"
        gB = GENERIC "b"
        x1 = Word $ Var "x1" (SET INT)
        x2 = Word $ Var "x2" (SET INT)
        x3 = Word $ Var "x3" (SET $ SET INT)
        x4 = Word $ Var "x3" (SET $ SET INT)
        y  = Word $ Var "y" INT
        z  = Word $ Var "z" REAL
        union  = Fun "union" [SET gA,SET gA] $ SET gA
        member = Fun "member" [gA, SET gA] BOOL
        pp = FunApp member [FunApp union [x1,x2], specialize (fromList [("a",SET $ GENERIC "a")]) $ FunApp union [x3,x4]]
        qq = FunApp member [FunApp union [x1,x2], FunApp (Fun "union" [SET $ SET gA,SET $ SET gA] $ SET $ SET gB) [x3,x4]]
        p = FunApp member [FunApp union [x1,x2], specialize (fromList [("a",GENERIC "b")]) $ FunApp union [x3,x4]]
        q = FunApp member [FunApp union [x1,x2], FunApp (Fun "union" [SET gB,SET gB] $ SET gB) [x3,x4]]
        