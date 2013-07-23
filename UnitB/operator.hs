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
        | Membership
        | TotalFunction
        | Leq | Implies 
        | Follows | And | Power
    deriving (Eq,Ord,Show,Enum)

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

mk_expr TotalFunction x y = Right x `ztfun` Right y

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
        ([SetDiff],Ambiguous),
        ([TotalFunction],Ambiguous),
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