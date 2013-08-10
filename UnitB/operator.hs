module UnitB.Operator where

import Data.List as L
import Data.Map hiding ( foldl )

import UnitB.SetTheory
import UnitB.FunctionTheory

import Z3.Def
import Z3.Const

data UnaryOperator = Negation

data BinOperator = 
        SetDiff
        | Apply
        | Plus  | Mult | Power
        | Equal | Leq | Geq
        | Less | Greater
        | Membership | Union 
        | Overload | DomSubt | DomRest
        | MkFunction
        | TotalFunction
        | And | Or
        | Implies | Follows 
        | Equiv
    deriving (Eq,Ord,Show,Enum)

    -- To add an operator:
    -- o add it in the parser
    -- o add it in the associativity chain
    -- o add it in a theory
    -- o add a token for it in data type Operator
    -- o create a function that generates an expression
    --      from the token
mk_expr :: BinOperator -> Expr -> Expr -> Either String Expr
mk_expr Plus x y    = Right x `mzplus` Right y
mk_expr Mult x y    = Right x `mztimes` Right y
mk_expr Power x y   = Right x `mzpow` Right y
mk_expr Apply x y   = Right x `zapply` Right y

mk_expr Equal x y      = Right x `mzeq` Right y
mk_expr Leq x y        = Right x `mzle` Right y
mk_expr Geq y x        = Right x `mzle` Right y
    -- here the operands are inverted. we use only mzle in the
    -- backend on purpose to not have many operators than
    -- doing the same thing

mk_expr Less x y       = Right x `mzless` Right y
mk_expr Greater y x    = Right x `mzless` Right y


mk_expr Equiv x y   = Right x `mzeq` Right y
mk_expr And x y     = Right x `mzand` Right y 
mk_expr Or x y      = Right x `mzor` Right y 
mk_expr Implies x y    = Right x `mzimplies` Right y 
mk_expr Follows x y    = Right y `mzimplies` Right x

mk_expr Membership x y = Right x `zelem` Right y
mk_expr SetDiff x y    = Right x `zsetdiff` Right y
mk_expr Union x y      = Right x `zunion` Right y

mk_expr TotalFunction x y = Right x `ztfun` Right y
mk_expr Overload x y      = Right x `zovl` Right y
mk_expr DomSubt x y       = Right x `zdomsubt` Right y
mk_expr DomRest x y       = Right x `zdomrest` Right y
mk_expr MkFunction x y    = Right x `zmk_fun` Right y

mk_unary :: UnaryOperator -> Expr -> Either String Expr
mk_unary Negation x       = Right $ znot x

    -- TODO: disallow chain x y if both x y are not relational symbols
chain Equal x         = x
chain x Equal         = x
chain Implies Implies = Implies
chain Follows Follows = Follows
chain Leq Leq         = Leq
chain Less Leq        = Less
chain Leq Less        = Less
chain Less Less       = Less
chain Geq Geq         = Geq
chain Greater Geq     = Greater
chain Geq Greater     = Greater
chain Greater Greater = Greater
chain _ _             = error "operators cannot be chained"


data Assoc = LeftAssoc | RightAssoc | Ambiguous
    deriving Show

associativity :: [([BinOperator],Assoc)]
associativity = 
        [ ([Apply],LeftAssoc)
        , ([Power],Ambiguous)
        , ([Mult],LeftAssoc)
        , ([Plus],LeftAssoc)
        , ([MkFunction],Ambiguous)
        , ([Overload],LeftAssoc)
        , ([Union],LeftAssoc)
        , ([SetDiff],Ambiguous)
        , ([TotalFunction],Ambiguous)
        , ([DomRest,DomSubt],LeftAssoc)
        , ([Equal,Leq,Less,Membership,Geq,Greater],Ambiguous)
        , ([And],LeftAssoc)
        , ([Or],LeftAssoc)
        , ([Implies,Follows],Ambiguous) 
        , ([Equiv],LeftAssoc)
        ]

logical x = x `elem` [Implies, Follows, And, Or, Equiv]

prod (xs,z) = [ ((x,y),z) | x <- xs, y <- xs ]

pairs = fromList (concat (do
            ((x,_),xs) <- zip a $ tail $ tails a
            (y,_)      <- xs
            a          <- x
            b          <- y
            return [
                ((a,b),LeftAssoc),
                ((b,a),RightAssoc) ])
        ++ concatMap prod a    )
    where
        a = associativity

assoc x y = pairs ! (x,y)

binds :: UnaryOperator -> BinOperator -> Assoc
binds Negation x
    | logical x = LeftAssoc
    | otherwise = RightAssoc