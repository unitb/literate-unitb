{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Logic.Expr.Type where

    -- Modules
import Logic.Expr.Classes

    -- Libraries
import Control.DeepSeq

import           Data.Typeable

import           GHC.Generics

import           Utilities.Format

class (Ord a, Tree a, Show a) => TypeSystem a where
    type_cons :: a -> Maybe (TypeCons a)
    make_type :: Sort -> [a] -> a

instance TypeSystem GenericType where
    type_cons (Gen x) = Just x
    type_cons _       = Nothing
    make_type s ts    = Gen (USER_DEFINED s ts)

instance TypeSystem FOType where
    type_cons (FOT x) = Just x
    make_type s ts    = FOT (USER_DEFINED s ts)

type Type = GenericType

data GenericType = 
        Gen (TypeCons GenericType) 
        | GENERIC String
        | VARIABLE String
    deriving (Eq, Ord, Typeable, Generic)

data FOType      = FOT (TypeCons FOType)
    deriving (Eq, Ord, Typeable)

data TypeCons a = USER_DEFINED Sort [a]
    deriving (Eq, Ord, Show, Generic, Typeable)

instance Tree GenericType where
    as_tree (Gen t) = cons_to_tree t
    as_tree (GENERIC x)   = Str x
    as_tree (VARIABLE n)  = Str $ "_" ++ n
    rewriteM' f s0 (Gen (USER_DEFINED s ts)) = do
            (s1,ys) <- fold_mapM f s0 ts
            return (s1, Gen (USER_DEFINED s ys))
    rewriteM' _ s x@(VARIABLE _) = return (s,x)
    rewriteM' _ s x@(GENERIC _)  = return (s,x)

instance Tree FOType where
    as_tree (FOT t) = cons_to_tree t
    rewriteM' f s0 (FOT (USER_DEFINED s ts)) = do
            (s1,ys) <- fold_mapM f s0 ts
            return (s1, FOT (USER_DEFINED s ys))

as_generic :: FOType -> GenericType
as_generic (FOT (USER_DEFINED s ts)) = Gen $ USER_DEFINED s (map as_generic ts)

cons_to_tree :: Tree a => TypeCons a -> StrList
cons_to_tree (USER_DEFINED s []) = Str $ z3_name s
cons_to_tree (USER_DEFINED s ts) = List (Str (z3_name s) : map as_tree ts)

instance NFData t => NFData (TypeCons t) where
    rnf (USER_DEFINED s xs) = rnf (s,xs)

instance NFData FOType where
    rnf (FOT t) = rnf t

instance NFData GenericType where
    rnf (GENERIC xs)  = rnf xs 
    rnf (VARIABLE xs) = rnf xs
    rnf (Gen t)       = rnf t

--instance Type t => Tree (TypeCons t) where
----    as_tree (GENERIC x)   = Str x
----    as_tree (VARIABLE n)  = Str $ "_" ++ n
--    as_tree (USER_DEFINED s []) = Str $ z3_name s
--    as_tree (USER_DEFINED s xs) = List (Str (z3_name s) : map as_tree xs)
----    rewriteM' _ s x@(VARIABLE _) = return (s,x)
----    rewriteM' _ s x@(GENERIC _)  = return (s,x)
--    rewriteM' f s0 (USER_DEFINED s xs) = do
--            (s1,ys) <- fold_mapM f s0 $ catMaybes $ map type_cons xs
--            return (s1, USER_DEFINED s ys)

data Sort =
        BoolSort | IntSort | RealSort 
        | DefSort 
            String   -- Latex name
            String   -- Type name
            [String] -- Generic Parameter
            GenericType -- Type with variables
        | Sort String String Int --[String]
        | Datatype 
            [String]    -- Parameters
            String      -- type name
            [(String, [(String,GenericType)])] -- alternatives and named components
    deriving (Eq, Ord, Show, Generic)

instance Show FOType where
    show (FOT (USER_DEFINED s [])) = (z3_name s)
    show (FOT (USER_DEFINED s ts)) = format "{0} {1}" (z3_name s) ts

instance Show GenericType where
    show (GENERIC n)         = format "_{0}" n 
    show (VARIABLE n)        = format "'{0}" n 
    show (Gen (USER_DEFINED s [])) = (z3_name s)
    show (Gen (USER_DEFINED s ts)) = format "{0} {1}" (z3_name s) ts

instance NFData Sort where
    rnf BoolSort = ()
    rnf IntSort  = ()
    rnf RealSort = ()
    rnf (DefSort xs ys zs t) = rnf (xs,ys,zs,t) 
    rnf (Sort xs ys n)       = rnf (xs,ys,n)
    rnf (Datatype xs ys zs)  = rnf (xs,ys,zs)

instance Named Sort where
    name (Sort x _ _) = x
    name (DefSort x _ _ _) = x
    name (Datatype _ x _)  = x
    name BoolSort   = "\\Bool"
    name IntSort    = "\\Int"
    name RealSort   = "\\Real"

z3_name :: Sort -> String
z3_name (BoolSort) = "Bool"
z3_name (IntSort)  = "Int"
z3_name (RealSort) = "Real"
z3_name (Sort _ x _)       = x
z3_name (DefSort _ x _ _)  = x
z3_name (Datatype _ x _)   = x
