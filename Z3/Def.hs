module Z3.Def where


data Expr = 
        Word Var 
        | Number Int
        | Const String Type
        | FunApp Fun [Expr]
        | Binder Quantifier [Var] Expr
    deriving Eq

data Quantifier = Forall | Exists 
    deriving Eq

data Type = BOOL | INT | REAL 
        | ARRAY Type Type 
        | GENERIC String 
        | USER_DEFINED String
        | SET Type
    deriving Eq

data Decl = FunDecl String [Type] Type 
    | ConstDecl String Type
    | FunDef String [Var] Type Expr

data Command = Decl Decl | Assert Expr | CheckSat Bool | GetModel

data Fun = Fun String [Type] Type
    deriving Eq

data Var = Var String Type
    deriving Eq

data Def = Def String [Var] Type Expr
    deriving Eq

data Operator = 
        Plus | Mult | Equal
        | Membership
        | Leq | Implies 
        | Follows | And | Power
    deriving (Eq,Ord,Show,Enum)
