module Logic.OldOperator where

import Logic.Operator

    -- Libraries
import Data.Array
import Data.List
import Data.Map
import Data.Typeable

data XUnaryOperator = Negation
    deriving (Eq, Ord)

data XBinOperator = 
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
    deriving (Eq,Ord,Show,Enum,Ix,Typeable)

associativity :: [([XBinOperator],Assoc)]
associativity = 
        [ ([Apply],LeftAssoc)
        , ([Power],NoAssoc)
        , ([Mult],LeftAssoc)
        , ([Plus],LeftAssoc)
        , ([MkFunction],NoAssoc)
        , ([Overload],LeftAssoc)
        , ([Union],LeftAssoc)
        , ([SetDiff],NoAssoc)
        , ([TotalFunction],NoAssoc)
        , ([DomRest,DomSubt],LeftAssoc)
        , ([ Equal,Leq,Less
           , Membership,Geq,Greater],NoAssoc)
        , ([And],LeftAssoc)
        , ([Or],LeftAssoc)
        , ([Implies,Follows],NoAssoc) 
        , ([Equiv],LeftAssoc)
        ]

logical :: XBinOperator -> Bool
logical x = x `elem` [Implies, Follows, And, Or, Equiv]

bin_op_range :: (XBinOperator, XBinOperator)
bin_op_range = (x,y)
    where
        x = toEnum 0
        y = last $ enumFrom x

pairs :: Map (XBinOperator, XBinOperator) Assoc
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

prod :: ([a],b) -> [((a,a),b)]
prod (xs,z) = [ ((x,y),z) | x <- xs, y <- xs ]
