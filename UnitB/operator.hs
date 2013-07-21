module UnitB.Operator where

import Data.List as L
import Data.Map hiding ( foldl )

import UnitB.SetTheory

import Z3.Def
import Z3.Const

data Operator = 
        SetDiff
        | Apply
        | Plus | Mult | Equal
        | Membership
        | Leq | Implies 
        | Follows | And | Power
    deriving (Eq,Ord,Show,Enum)

mk_expr :: Operator -> Expr -> Expr -> Maybe Expr
mk_expr Plus x y    = Just x `mzplus` Just y
mk_expr Mult x y    = Just x `mztimes` Just y
mk_expr And x y     = Just x `mzand` Just y 
mk_expr Power x y   = Just x `mzpow` Just y
mk_expr Apply x y   = Just (x `zapply` y)

mk_expr Equal x y      = Just x `mzeq` Just y
mk_expr Implies x y    = Just x `mzimplies` Just y 
mk_expr Follows x y    = Just x `mzfollows` Just y 
mk_expr Leq x y        = Just x `mzle` Just y
mk_expr Membership x y = Just x `zelem` Just y

mk_expr SetDiff x y    = Just x `zsetdiff` Just y

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
        ([Equal,Leq],Ambiguous),
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