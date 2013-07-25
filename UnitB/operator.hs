module UnitB.Operator where

import Data.List as L
import Data.Map hiding ( foldl )

import UnitB.SetTheory
import UnitB.FunctionTheory

import Z3.Def
import Z3.Const

data Operator = 
        SetDiff
        | Apply
        | Plus | Mult | Equal
        | Membership | Union 
        | Overload | DomSubt | DomRest
        | MkFunction
        | TotalFunction
        | Leq | Implies 
        | Follows | And | Power
    deriving (Eq,Ord,Show,Enum)

    -- To add an operator:
    -- o add it in the parser
    -- o add it in the associativity chain
    -- o add it in a theory
    -- o add a token for it in data type Operator
    -- o create a function that generates an expression
    --      from the token
mk_expr :: Operator -> Expr -> Expr -> Either String Expr
mk_expr Plus x y    = Right x `mzplus` Right y
mk_expr Mult x y    = Right x `mztimes` Right y
mk_expr And x y     = Right x `mzand` Right y 
mk_expr Power x y   = Right x `mzpow` Right y
mk_expr Apply x y   = Right x `zapply` Right y

mk_expr Equal x y      = Right x `mzeq` Right y
mk_expr Implies x y    = Right x `mzimplies` Right y 
mk_expr Follows x y    = Right x `mzfollows` Right y 
mk_expr Leq x y        = Right x `mzle` Right y
mk_expr Membership x y = Right x `zelem` Right y

mk_expr SetDiff x y    = Right x `zsetdiff` Right y
mk_expr Union x y      = Right x `zunion` Right y

mk_expr TotalFunction x y = Right x `ztfun` Right y
mk_expr Overload x y      = Right x `zovl` Right y
mk_expr DomSubt x y      = Right x `zdomsub` Right y
mk_expr DomRest x y       = Right x `zdomrest` Right y
mk_expr MkFunction x y    = Right x `zmk_fun` Right y

    -- TODO: disallow chain x y if both x y are not relational symbols
chain Equal x         = x
chain x Equal         = x
chain Implies Implies = Implies
chain Follows Follows = Follows
chain Leq Leq         = Leq
chain _ _             = error "operators cannot be chained"


data Assoc = LeftAssoc | RightAssoc | Ambiguous
    deriving Show

associativity :: [([Operator],Assoc)]
associativity = [
        ([Apply],LeftAssoc),
        ([Power],Ambiguous),
        ([Mult],LeftAssoc),
        ([Plus],LeftAssoc),
        ([MkFunction],Ambiguous),
        ([Overload],LeftAssoc),
        ([Union],LeftAssoc),
        ([SetDiff],Ambiguous),
        ([TotalFunction],Ambiguous),
        ([DomRest,DomSubt],LeftAssoc),
        ([Equal,Leq,Membership],Ambiguous),
        ([And],LeftAssoc),
        ([Implies,Follows],Ambiguous) ]

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