{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TemplateHaskell    #-}
module Logic.Expr.Type where

    -- Modules
import Logic.Expr.Classes

    -- Libraries
import Control.DeepSeq
import Control.Monad.Reader

import           Data.Data
import           Data.DeriveTH
import qualified Data.Set as S

import           GHC.Generics

import           Utilities.Format

class TypeOf a ~ TypeOf (TypeOf a) => Typed a where
    type TypeOf a :: *

referenced_types :: FOType -> S.Set FOType
referenced_types t@(FOT _ ts) = S.insert t $ S.unions $ map referenced_types ts

instance Typed GenericType where
    type TypeOf GenericType = GenericType

class (Ord a, Tree a, Show a, Typed a, TypeOf a ~ a) => TypeSystem a where
    type_cons :: a -> Maybe (TypeCons a)
    make_type :: Sort -> [a] -> a

instance TypeSystem GenericType where
    type_cons (Gen s xs) = Just (USER_DEFINED s xs)
    type_cons _          = Nothing
    make_type    = Gen

instance Typed FOType where
    type TypeOf FOType = FOType

instance TypeSystem FOType where
    type_cons (FOT s xs) = Just (USER_DEFINED s xs)
    make_type = FOT

instance Tree () where
    as_tree' () = return $ List []
    rewriteM' f = f

instance Typed () where
    type TypeOf () = ()

instance TypeSystem () where
    type_cons () = Nothing
    make_type _ _ = ()

type Type = GenericType

data GenericType = 
        Gen Sort [GenericType] 
        | GENERIC String
        | VARIABLE String
    deriving (Eq, Ord, Typeable, Generic, Data)

data FOType      = FOT Sort [FOType]
    deriving (Eq, Ord, Typeable)

data TypeCons a = USER_DEFINED Sort [a]
    deriving (Eq, Ord, Show, Generic, Typeable)

instance Tree GenericType where
    as_tree' (Gen s ts) = cons_to_tree $ USER_DEFINED s ts
    as_tree' (GENERIC x)   = return $ Str x
    as_tree' (VARIABLE n)  = return $ Str $ "_" ++ n
    rewriteM' f s0 (Gen s ts) = do
            (s1,ys) <- fold_mapM f s0 ts
            return (s1, Gen s ys)
    rewriteM' _ s x@(VARIABLE _) = return (s,x)
    rewriteM' _ s x@(GENERIC _)  = return (s,x)

instance Tree FOType where
    as_tree' (FOT s ts) = cons_to_tree $ USER_DEFINED s ts
    rewriteM' f s0 (FOT s ts) = do
            (s1,ys) <- fold_mapM f s0 ts
            return (s1, FOT s ys)

as_generic :: FOType -> GenericType
as_generic (FOT s ts) = Gen s (map as_generic ts)

cons_to_tree :: Tree a => TypeCons a -> Reader OutputMode StrList
cons_to_tree (USER_DEFINED s []) = do
    opt <- ask
    let n = case opt of
                ProverOutput -> z3_name s
                UserOutput -> name s
    return $ Str n
cons_to_tree (USER_DEFINED s ts) = do
    opt <- ask
    let n = case opt of
                ProverOutput -> z3_name s
                UserOutput -> name s
    return $ List (Str n : map as_tree ts)

data Sort =
        BoolSort | IntSort | RealSort 
        | DefSort 
            String      -- Latex name
            String      -- Type name
            [String]    -- Generic Parameter
            GenericType -- Type with variables
        | Sort String String Int --[String]
        | Datatype 
            [String]    -- Parameters
            String      -- type name
            [(String, [(String,GenericType)])] 
                        -- alternatives and named components
    deriving (Eq, Ord, Show, Typeable, Data, Generic)

typeParams :: Sort -> Int
typeParams BoolSort = 0
typeParams IntSort  = 0
typeParams RealSort = 0
typeParams (Sort _ _ n) = n
typeParams (DefSort _ _ ps _) = length ps
typeParams (Datatype xs _ _)  = length xs

instance Show FOType where
    show (FOT s []) = (z3_name s)
    show (FOT s ts) = format "{0} {1}" (z3_name s) ts

instance Show GenericType where
    show (GENERIC n)         = format "_{0}" n 
    show (VARIABLE n)        = format "'{0}" n 
    show (Gen s []) = name s
    show (Gen s ts) = format "{0} {1}" (name s) ts

instance Named Sort where
    name (Sort x _ _) = x
    name (DefSort x _ _ _) = x
    name (Datatype _ x _)  = x
    name BoolSort   = "\\Bool"
    name IntSort    = "\\Int"
    name RealSort   = "\\Real"
    decorated_name' s = do
        opt <- ask
        case opt of
            ProverOutput -> return $ z3_name s
            UserOutput -> return $ name s

    z3_name (Sort _ x _) = x
    z3_name (DefSort _ x _ _) = x
    z3_name (Datatype _ x _)  = x
    z3_name BoolSort   = "Bool"
    z3_name IntSort    = "Int"
    z3_name RealSort   = "Real"

pair_sort :: Sort
pair_sort = -- Sort "Pair" "Pair" 2
               Datatype ["a","b"] "Pair" 
                    [ ("pair", 
                        [ ("first",  GENERIC "a")
                        , ("second", GENERIC "b") ]) ]


pair_type :: TypeSystem t => t -> t -> t
pair_type x y = make_type pair_sort [x,y]

null_sort :: Sort
null_sort = Sort "Null" "Null" 2

null_type :: TypeSystem t => t
null_type = make_type null_sort []

maybe_sort :: Sort
maybe_sort   = Sort "\\maybe" "Maybe" 1

maybe_type :: TypeSystem t => t -> t
maybe_type t = make_type maybe_sort [t]

fun_sort :: Sort
fun_sort = DefSort "\\pfun" "pfun" ["a","b"] (array (GENERIC "a") (maybe_type $ GENERIC "b"))

fun_type :: TypeSystem t => t -> t -> t
fun_type t0 t1 = make_type fun_sort [t0,t1] --ARRAY t0 t1

bool :: TypeSystem t => t
bool = make_type BoolSort []
    
array_sort :: Sort
array_sort = Sort "Array" "Array" 2

array :: TypeSystem t => t -> t -> t
array t0 t1 = make_type array_sort [t0,t1]

set_sort :: Sort
set_sort = DefSort "\\set" "set" ["a"] (array (GENERIC "a") bool)

derive makeNFData ''TypeCons
derive makeNFData ''FOType
derive makeNFData ''GenericType
derive makeNFData ''Sort
