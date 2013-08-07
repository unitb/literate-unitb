{-# LANGUAGE DeriveDataTypeable #-}
module Z3.Def where

import Data.List
import Data.Typeable

import Utilities.Format

data Expr = 
        Word Var 
        | Const [Type] String Type
        | FunApp Fun [Expr]
        | Binder Quantifier [Var] Expr Expr
    deriving (Eq, Typeable)

type_of (Word (Var _ t))          = t
type_of (Const _ _ t)             = t
type_of (FunApp (Fun _ _ ts t) _) = t
type_of (Binder _ _ _ e)          = type_of e

data Quantifier = Forall | Exists | Lambda
    deriving Eq

merge_range Forall = Str "=>"
merge_range Exists = Str "and"

data Type = 
        BOOL | INT | REAL 
        | ARRAY Type Type 
        | GENERIC String 
        | USER_DEFINED Sort [Type]
        | SET Type
    deriving (Eq, Ord, Typeable)

instance Show Type where
    show BOOL                = "BOOL"
    show INT                 = "INT"
    show REAL                = "REAL"
    show (ARRAY t0 t1)       = format "ARRAY {0}" [t0,t1]
    show (GENERIC n)         = format "_{0}" n 
    show (USER_DEFINED s []) = (z3_name s)
    show (USER_DEFINED s ts) = format "{0} {1}" (z3_name s) ts
    show (SET t) = format "SET {0}" t


data StrList = List [StrList] | Str String

fold_mapM :: Monad m => (a -> b -> m (a,c)) -> a -> [b] -> m (a,[c])
fold_mapM f s [] = return (s,[])
fold_mapM f s0 (x:xs) = do
        (s1,y)  <- f s0 x
        (s2,ys) <- fold_mapM f s1 xs
        return (s2,y:ys)

fold_map :: (a -> b -> (a,c)) -> a -> [b] -> (a,[c])
fold_map f s [] = (s,[])
fold_map f s0 (x:xs) = (s2,y:ys)
    where
        (s1,y)  = f s0 x
        (s2,ys) = fold_map f s1 xs

class Tree a where
    as_tree   :: a -> StrList
    rewriteM' :: Monad m => (b -> a -> m (b,a)) -> b -> a -> m (b,a)
    rewrite'  :: (b -> a -> (b,a)) -> b -> a -> (b,a)
    rewrite' f x t = (rewriteM' g x t) ()
        where
            g x t () = f x t
 
visit    :: Tree a => (b -> a -> b) -> b -> a -> b
visit f s x = fst $ rewrite' g s x
    where
        g s0 y = (f s0 y, y)
rewrite  :: Tree a => (a -> a) -> a -> a
rewrite f x = snd $ rewrite' g () x
    where
        g () x = ((), f x)

visitM :: (Monad m, Tree a) => (b -> a -> m b) -> b -> a -> m b
visitM f x t = visit g (return x) t
    where
        g x t = do
            y <- x
            f y t

rewriteM :: (Monad m, Tree a) => (a -> m a) -> a -> m a
rewriteM f t = do
        ((),x) <- rewriteM' g () t
        return x
    where 
        g () x = do
            y <- f x
            return ((),y)

instance Tree Type where
    as_tree BOOL = Str "Bool"
    as_tree INT  = Str "Int"
    as_tree REAL = Str "Real"
    as_tree (ARRAY t0 t1) = List [Str "Array", as_tree t0, as_tree t1]
    as_tree (GENERIC x) = Str x
    as_tree (SET t) = List [Str "Array", as_tree t, Str "Bool"]
    as_tree (USER_DEFINED s []) = Str $ z3_name s
    as_tree (USER_DEFINED s xs) = List (Str (z3_name s) : map as_tree xs)
--    rewrite' f s x@BOOL = (s,x)
--    rewrite' f s x@INT  = (s,x)
--    rewrite' f s x@REAL = (s,x)
--    rewrite' f s0 x@(ARRAY t0 t1) = (s2,ARRAY t2 t3)
--        where
--            (s1,t2) = f s0 t0
--            (s2,t3) = f s1 t1
--    rewrite' f s x@(GENERIC _) = (s,x)
--    rewrite' f s x@(SET t) = (fst $ f s t, SET $ snd $ f s t)
--    rewrite' f s0 x@(USER_DEFINED s xs) = (s1, USER_DEFINED s ys)
--        where
--            (s1,ys) = fold_map f s0 xs
    rewriteM' f s x@BOOL = return (s,x)
    rewriteM' f s x@INT  = return (s,x)
    rewriteM' f s x@REAL = return (s,x)
    rewriteM' f s0 x@(ARRAY t0 t1) = do
            (s1,t2) <- f s0 t0
            (s2,t3) <- f s1 t1
            return (s2,ARRAY t2 t3)
    rewriteM' f s x@(GENERIC _) = return (s,x)
    rewriteM' f s x@(SET t) = do
            (s,t) <- f s t
            return (s,SET t)
    rewriteM' f s0 x@(USER_DEFINED s xs) = do
            (s1,ys) <- fold_mapM f s0 xs
            return (s1, USER_DEFINED s ys)

z3_decoration :: Type -> String
z3_decoration t = f $ as_tree t :: String
    where
        f (List ys) = format "@Open{0}@Close" xs
            where xs = concatMap f ys :: String
        f (Str y)   = format "@@{0}" y

data Sort =
        BoolSort | IntSort | RealSort 
        | DefSort String String [String] Type
        | Sort String String Int --[String]
    deriving (Eq, Ord, Show)

z3_name (BoolSort) = "Bool"
z3_name (IntSort) = "Int"
z3_name (RealSort) = "Real"
z3_name (Sort _ x _) = x
z3_name (DefSort _ x _ _) = x

data Decl = 
    FunDecl [Type] String [Type] Type 
    | ConstDecl String Type
    | FunDef [Type] String [Var] Type Expr
    | SortDecl Sort

data Command = Decl Decl | Assert Expr | CheckSat Bool | GetModel

data Fun = Fun [Type] String [Type] Type
    deriving Eq

data Var = Var String Type
    deriving (Eq,Ord)

data Def = Def [Type] String [Var] Type Expr
    deriving Eq

instance Show StrList where
    show (List xs) = "(" ++ intercalate " " (map show xs) ++ ")"
    show (Str s)   = s

instance Show Quantifier where
    show Forall = "forall"
    show Exists = "exists"

instance Tree Expr where
    as_tree (Word (Var xs _))    = Str xs
    as_tree (Const ys xs _)      = Str (xs ++ concatMap z3_decoration ys)
    as_tree (FunApp (Fun xs name _ _) [])  = 
        Str (name ++ concatMap z3_decoration xs)
    as_tree (FunApp (Fun xs name _ _) ts)  = 
        List (Str (name ++ concatMap z3_decoration xs) : (map as_tree ts))
    as_tree (Binder q xs r xp)  = List 
        [ Str $ show q
        , List $ map as_tree xs
        , List 
            [ merge_range q
            , as_tree r
            , as_tree xp ] ]
    rewriteM' f s x@(Word (Var xs _))           = return (s,x)
    rewriteM' f s x@(Const _ _ _)               = return (s,x)
    rewriteM' f s0 (FunApp g@(Fun _ _ _ _) xs)  = do
            (s1,ys) <- fold_mapM f s0 xs
            return (s1,FunApp g ys)
    rewriteM' f s0 (Binder q xs r0 x)  = do
            (s1,r1) <- f s0 r0
            (s2,y)  <- f s1 x
            return (s2,Binder q xs r1 y)

instance Show Expr where
    show e = show $ as_tree e

instance Tree Decl where
    as_tree (FunDecl _ name dom ran) =
            List [ Str "declare-fun", 
                Str name, 
                (List $ map as_tree dom), 
                (as_tree ran) ]
    as_tree (ConstDecl n t) =
            List [ Str "declare-const", Str n, as_tree t ]
    as_tree (FunDef _ name dom ran val) =
            List [ Str "define-fun", 
                Str name, 
                (List $ map as_tree dom), 
                (as_tree ran),
                (as_tree val) ]
    as_tree (SortDecl (Sort tag name n)) = 
            List [ 
                Str "declare-sort",
                Str name,
                Str $ show n ]
    as_tree (SortDecl (DefSort tag name xs def)) = 
            List 
                [ Str "define-sort"
                , Str name
                , List $ map Str xs
                , as_tree def 
                ]
    rewriteM' = id
    
instance Tree Var where
    as_tree (Var vn vt) = List [Str vn, as_tree vt]
    rewriteM' = id

instance Tree Sort where
    as_tree (DefSort _ x xs def) = 
            List 
                [ Str x
                , List $ map Str xs
                , as_tree def
                ]
    as_tree (Sort _ x n) = List [Str x, Str $ show n]
    rewriteM' = id

instance Show Var where
    show (Var n t) = n ++ ": " ++ show (as_tree t)

instance Show Fun where
    show (Fun xs n ts t) = n ++ show xs ++ ": " 
        ++ intercalate " x " (map (show . as_tree) ts)
        ++ " -> " ++ show (as_tree t)

instance Show Def where
    show (Def xs n ps t e) = n ++ show xs ++  ": " 
        ++ intercalate " x " (map (show . as_tree) ps)
        ++ " -> " ++ show (as_tree t)
        ++ "  =  " ++ show (as_tree e)