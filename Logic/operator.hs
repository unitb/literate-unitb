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
import Data.List as L
import Data.Map as M hiding ( foldl )
import Data.Tuple
import Data.Typeable

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

    -- NOTE: All the instructions below can now be done in 
    -- the theories
    -- To add an operator:
    -- o add it in the parser
    -- o add it in the associativity chain
    -- o add it in a theory
    -- o add a token for it in data type Operator
    -- o create a function that generates an expression
    --      from the token
mk_expr (BinOperator _ _ f) x y = f (Right x) (Right y)

mk_unary :: UnaryOperator -> Expr -> Either String Expr
mk_unary (UnaryOperator _ _ f) x = f $ Right x

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
    } deriving (Eq,Show)

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
--		| not $ L.null complete = error $ "assoc': all new operators are not declared: " ++ show complete
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

    -- logic
disj    = BinOperator "or" "\\lor"          mzor
conj    = BinOperator "and" "\\land"        mzand
implies = BinOperator "implies" "\\implies" mzimplies
follows = BinOperator "follows" "\\follows" (flip mzimplies)
equiv   = BinOperator "implies" "\\equiv"   mzeq
neg     = UnaryOperator "neg" "\\neg"       mznot

logic = Notation
    { new_ops     = Left neg : L.map Right [conj,disj,implies,follows,equiv]
    , prec = [    [Left neg] 
                : L.map (L.map Right)
                     [ [disj,conj]
                     , [implies,follows]
                     , [equiv] ]]
    , left_assoc  = [[equiv],[disj],[conj]]
    , right_assoc = []
    , relations   = [equiv,implies,follows]
    , chaining    = 
        [ ((equiv,implies),implies)
        , ((implies,equiv),implies)
        , ((implies,implies),implies)
        , ((equiv,equiv),equiv)
        , ((equiv,follows),follows)
        , ((follows,equiv),follows)
        , ((follows,follows),follows) ]  }

double (x,y) = ((x,x),(y,y))