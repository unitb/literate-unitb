{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE RecordWildCards    #-}
module Logic.Operator where

    -- Modules
import Logic.Expr
import Logic.Const

    -- Libraries
import Data.Array as A
import Data.Either
import Data.Function
--import Data.IORef
import Data.List as L
import Data.Map as M hiding ( foldl )
import Data.Tuple
import Data.Typeable

--import System.IO.Unsafe

import Utilities.Format
import Utilities.Graph

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

    -- To add an operator:
    -- o add it in the parser
    -- o add it in the associativity chain
    -- o add it in a theory
    -- o add a token for it in data type Operator
    -- o create a function that generates an expression
    --      from the token
mk_expr (BinOperator _ _ f) x y = f (Right x) (Right y)
--mk_expr :: XBinOperator -> Expr -> Expr -> Either String Expr
--mk_expr Plus x y    = Right x `mzplus` Right y
--mk_expr Mult x y    = Right x `mztimes` Right y
--mk_expr Power x y   = Right x `mzpow` Right y
--mk_expr Apply x y   = Right x `zapply` Right y
--
--mk_expr Equal x y      = Right x `mzeq` Right y
--mk_expr Leq x y        = Right x `mzle` Right y
--mk_expr Geq y x        = Right x `mzle` Right y
--    -- here the operands are inverted. we use only mzle in the
--    -- backend on purpose to not have many operators than
--    -- doing the same thing
--
--mk_expr Less x y       = Right x `mzless` Right y
--mk_expr Greater y x    = Right x `mzless` Right y
--
--
--mk_expr Equiv x y   = Right x `mzeq` Right y
--mk_expr And x y     = Right x `mzand` Right y 
--mk_expr Or x y      = Right x `mzor` Right y 
--mk_expr Implies x y    = Right x `mzimplies` Right y 
--mk_expr Follows x y    = Right y `mzimplies` Right x
--
--mk_expr Membership x y = Right x `zelem` Right y
--mk_expr SetDiff x y    = Right x `zsetdiff` Right y
--mk_expr Union x y      = Right x `zunion` Right y
--
--mk_expr TotalFunction x y = Right x `ztfun` Right y
--mk_expr Overload x y      = Right x `zovl` Right y
--mk_expr DomSubt x y       = Right x `zdomsubt` Right y
--mk_expr DomRest x y       = Right x `zdomrest` Right y
--mk_expr MkFunction x y    = Right x `zmk_fun` Right y

mk_unary :: UnaryOperator -> Expr -> Either String Expr
--mk_unary Negation x       = Right $ znot x
mk_unary (UnaryOperator _ _ f) x = f $ Right x

    -- TODO: disallow chain x y if both x y are not relational symbols
--chain Equal x         = x
--chain x Equal         = x
--chain Implies Implies = Implies
--chain Follows Follows = Follows
--chain Leq Leq         = Leq
--chain Less Leq        = Less
--chain Leq Less        = Less
--chain Less Less       = Less
--chain Geq Geq         = Geq
--chain Greater Geq     = Greater
--chain Geq Greater     = Greater
--chain Greater Greater = Greater
--chain _ _             = error "operators cannot be chained"


data Assoc = LeftAssoc | RightAssoc | Ambiguous
    deriving (Show,Eq,Typeable)

associativity :: [([XBinOperator],Assoc)]
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
        , ([ Equal,Leq,Less
           , Membership,Geq,Greater],Ambiguous)
        , ([And],LeftAssoc)
        , ([Or],LeftAssoc)
        , ([Implies,Follows],Ambiguous) 
        , ([Equiv],LeftAssoc)
        ]

data Notation = Notation
    { new_ops :: [Operator]
    , prec :: [[[Operator]]] 
    , left_assoc :: [[BinOperator]]
    , right_assoc :: [[BinOperator]]
    , relations :: [BinOperator]
    , chaining :: [((BinOperator,BinOperator),BinOperator)]
    }

empty_notation = Notation 
    { new_ops = []
    , prec = []
    , left_assoc = []
    , right_assoc = [] 
    , relations = []
    , chaining = [] }

combine x y 
    | L.null $ new_ops x `intersect` new_ops y = Notation
        { new_ops      = new_ops x ++ new_ops y
        , prec         = prec x ++ prec y
        , left_assoc   = left_assoc x ++ left_assoc y
        , right_assoc  = right_assoc x ++ right_assoc y 
        , relations    = relations x ++ relations y
        , chaining     = chaining x ++ chaining y }
    | otherwise        = error $ format "Notation, combine: redundant operator names. {0}" common
    where
        f (Right (BinOperator x _ _)) = x
        f (Left _)                  = "negation"
        intersect = intersectBy ((==) `on` f)
        common = L.map f $ new_ops x `intersect` new_ops y

precede x y 
    | L.null $ new_ops x `intersect` new_ops y = 
        let z = (combine x y) in
            z { 
                prec = prec z ++ [ xs ++ ys | xs <- prec x, ys <- prec y ] }
--        Notation
--        { new_ops      = new_ops x ++ new_ops y
--        , prec         =  ++ prec x ++ prec y
--        , left_assoc   = left_assoc x ++ left_assoc y
--        , right_assoc  = right_assoc x ++ right_assoc y }
    | otherwise        = error $ format "Notation, precede: redundant operator names. {0}" common
    where
        f (Right (BinOperator x _ _)) = x
        f (Left _)                  = "negation"
        intersect = intersectBy ((==) `on` f)
        common = L.map f $ new_ops x `intersect` new_ops y

--type Reduce = Either String Expr -> Either String Expr -> Either String Expr
type ExprP = Either String Expr 

data UnaryOperator = UnaryOperator String String (ExprP -> ExprP)
    deriving Typeable

instance Eq UnaryOperator where
    UnaryOperator x0 x1 _ == UnaryOperator y0 y1 _ = (x0,x1) == (y0,y1)

instance Ord UnaryOperator where
    compare (UnaryOperator x0 x1 _) (UnaryOperator y0 y1 _) = compare (x0,x1) (y0,y1)

instance Show UnaryOperator where
    show (UnaryOperator x _ _) = x -- format str x y
--        where
--            str = "Unary { token = {0}, lexeme = {1} }"

data BinOperator = BinOperator String String (ExprP -> ExprP -> ExprP)
    deriving Typeable

instance Eq BinOperator where
    BinOperator x0 x1 _ == BinOperator y0 y1 _ = (x0,x1) == (y0,y1)

instance Ord BinOperator where
    compare (BinOperator x0 x1 _) (BinOperator y0 y1 _) = compare (x0,x1) (y0,y1)

instance Show BinOperator where
    show (BinOperator x _ _) = x -- format str x y
--        where
--            str = "Binary { token = {0}, lexeme = {1} }"

type Operator = Either UnaryOperator BinOperator

precedence ops = m_closure_with (new_ops ops)
        $ concatMap g $ prec ops
    where
        f (xs,ys) = [ (x,y) | x <- xs, y <- ys ]
        g xs = concatMap f $ zip xs (drop 1 xs)

left_assoc_graph :: Notation -> Matrix BinOperator Bool
left_assoc_graph ops  = assoc_graph (rights $ new_ops ops) $ left_assoc ops

right_assoc_graph :: Notation -> Matrix BinOperator Bool
right_assoc_graph ops = assoc_graph (rights $ new_ops ops) $ right_assoc ops

bin_op_range :: (XBinOperator, XBinOperator)
bin_op_range = (x,y)
    where
        x = toEnum 0
        y = last $ enumFrom x

assoc_graph :: [BinOperator] -> [[BinOperator]] -> Matrix BinOperator Bool
assoc_graph rs xss = as_matrix_with rs ys
    where
        ys = concatMap (\xs -> [ (x,y) | x <- xs, y <- xs ]) xss

assoc' :: Notation -> Matrix Operator Assoc
assoc' ops 
		| not $ L.null complete = error $ "assoc': all new operators are not declared: " ++ show complete
        | not $ L.null cycles   = error $ "assoc': cycles exist in the precedence graph" ++ show cycles
        | otherwise   = foldl (unionWith join) M.empty
                  [ M.map (f LeftAssoc) pm
                  , M.map (f RightAssoc) $ mapKeys swap pm
                  , M.map (f LeftAssoc) $ mapKeys g lm
                  , M.map (f RightAssoc) $ mapKeys g rm ]
            -- fromList (zip bs $ L.map g bs)
    where
        cycles = L.filter (\x -> pm M.! (x,x)) (new_ops ops)
        complete = all_ops L.\\ (nub $ new_ops ops)
        all_ops = nub $	concat (concat (prec ops) 
					 ++ L.map (L.map Right) (left_assoc ops)
					 ++ L.map (L.map Right) (right_assoc ops)
					 ++ L.map (\((x,y),z) -> L.map Right [x,y,z]) (chaining ops))
				++ L.map Right (relations ops)
        pm = precedence ops
        lm = left_assoc_graph ops
        rm = right_assoc_graph ops
--        bs = range $ bounds pm
            -- pm (mapKeys swap pm)
            -- M.map (f LeftAssoc) pm
            -- M.map (f RightAssoc) $ mapKeys swap pm
            -- M.map (f LeftAssoc) lm
            -- M.map (f RightAssoc) rm
        f a b 
            | b         = a
            | otherwise = Ambiguous
        g (x,y) = (Right x,Right y)
        join x Ambiguous = x
        join Ambiguous x = x
        join _ _ = error "operator parser: conflicting precedences"
--        g (i,j)
--            | pm M.! (i,j) = LeftAssoc
--            | pm M.! (j,i) = RightAssoc
--            | lm M.! (i,j) = LeftAssoc
--            | rm M.! (i,j) = RightAssoc
--            | otherwise    = Ambiguous

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

    -- Basic functions
apply = BinOperator "apply" "."     zapply
equal = BinOperator "equal" "="     mzeq

functions = Notation
    { new_ops     = L.map Right [equal,apply]
    , prec = [ L.map (L.map Right)
                     [ [apply]
                     , [equal] ]]
    , left_assoc  = [[apply]]
    , right_assoc = []
    , relations   = []
    , chaining    = [] }

double (x,y) = ((x,x),(y,y))