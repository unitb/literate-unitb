{-# LANGUAGE DeriveDataTypeable #-}
module Z3.Def where

import Data.List
import Data.Typeable

import Utilities.Format

data Expr = 
        Word Var 
--        | Number Int
        | Const String Type
        | FunApp Fun [Expr]
        | Binder Quantifier [Var] Expr
    deriving (Eq, Typeable)

type_of (Word (Var _ t))        = t
type_of (Const _ t)             = t
type_of (FunApp (Fun _ ts t) _) = t
type_of (Binder _ _ e)          = type_of e

data Quantifier = Forall | Exists 
    deriving Eq

data Type = 
        BOOL | INT | REAL 
        | ARRAY Type Type 
        | GENERIC String 
        | USER_DEFINED Sort [Type]
        | SET Type
    deriving (Eq, Show, Typeable)

data StrList = List [StrList] | Str String

fold_map :: (a -> b -> (a,c)) -> a -> [b] -> (a,[c])
fold_map f s [] = (s,[])
fold_map f s0 (x:xs) = (s2,y:ys)
    where
        (s1,y)  = f s0 x
        (s2,ys) = fold_map f s1 xs

class Tree a where
    as_tree  :: a -> StrList
    rewrite' :: (b -> a -> (b,a)) -> b -> a -> (b,a)

visit    :: Tree a => (b -> a -> b) -> b -> a -> b
visit f s x = fst $ rewrite' g s x
    where
        g s0 y = (f s0 y, y)
rewrite  :: Tree a => (a -> a) -> a -> a
rewrite f x = snd $ rewrite' g () x
    where
        g () x = ((), f x)

instance Tree Type where
    as_tree BOOL = Str "Bool"
    as_tree INT  = Str "Int"
    as_tree REAL = Str "Real"
    as_tree (ARRAY t0 t1) = List [Str "Array", as_tree t0, as_tree t1]
    as_tree (GENERIC x) = Str x
    as_tree (SET t) = List [Str "Array", as_tree t, Str "Bool"]
    as_tree (USER_DEFINED s []) = Str $ z3_name s
    as_tree (USER_DEFINED s xs) = List (Str (z3_name s) : map as_tree xs)
    rewrite' f s x@BOOL = (s,x)
    rewrite' f s x@INT  = (s,x)
    rewrite' f s x@REAL = (s,x)
    rewrite' f s0 x@(ARRAY t0 t1) = (s2,ARRAY t2 t3)
        where
            (s1,t2) = f s0 t0
            (s2,t3) = f s1 t1
    rewrite' f s x@(GENERIC _) = (s,x)
    rewrite' f s x@(SET t) = (fst $ f s t, SET $ snd $ f s t)
    rewrite' f s0 x@(USER_DEFINED s xs) = (s1, USER_DEFINED s ys)
        where
            (s1,ys) = fold_map f s0 xs

z3_decoration t = f $ as_tree t :: String
    where
        f (List ys) = format "@Open{0}@Close" $ intercalate "@Comma" $ map f ys
        f (Str y)   = format "@@{0}" y

data Sort =
        BoolSort | IntSort | RealSort 
        | DefSort String String [String] Type
        | Sort String String Int --[String]
    deriving (Eq, Show)

z3_name (BoolSort) = "Bool"
z3_name (IntSort) = "Int"
z3_name (RealSort) = "Real"
z3_name (Sort _ x _) = x
z3_name (DefSort _ x _ _) = x

data Decl = 
    FunDecl String [Type] Type 
    | ConstDecl String Type
    | FunDef String [Var] Type Expr
    | SortDecl Sort

data Command = Decl Decl | Assert Expr | CheckSat Bool | GetModel

data Fun = Fun String [Type] Type
    deriving Eq

data Var = Var String Type
    deriving Eq

data Def = Def String [Var] Type Expr
    deriving Eq
