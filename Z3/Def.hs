{-# LANGUAGE DeriveDataTypeable #-}
module Z3.Def where

import Data.Typeable

data Expr = 
        Word Var 
--        | Number Int
        | Const String Type
        | FunApp Fun [Expr]
        | Binder Quantifier [Var] Expr
    deriving (Eq, Typeable)

data Quantifier = Forall | Exists 
    deriving Eq

data Type = 
        BOOL | INT | REAL 
        | ARRAY Type Type 
        | GENERIC String 
        | USER_DEFINED Sort [Type]
        | SET Type
    deriving (Eq, Show, Typeable)

data Sort =
        BoolSort | IntSort | RealSort 
        | Sort String String Int --[String]
    deriving (Eq, Show)

z3_name (BoolSort) = "Bool"
z3_name (IntSort) = "Int"
z3_name (RealSort) = "Real"
z3_name (Sort _ x _) = x

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

data Operator = 
        SetDiff
        | Apply
        | Plus | Mult | Equal
        | Membership
        | Leq | Implies 
        | Follows | And | Power
    deriving (Eq,Ord,Show,Enum)
