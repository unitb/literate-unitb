{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
module Logic.Operator where

    -- Modules
import Logic.Expr hiding ( pair )
import Logic.Const
import Logic.Classes

    -- Libraries
import Data.Either
import Data.Function
import Data.List as L
--import Data.Map as M hiding ( foldl )
import Data.Typeable

import           Utilities.Format
import           Utilities.Graph hiding ( Matrix )
import qualified Utilities.Graph as G 

type Matrix a b = G.Matrix a b

    -- NOTE: All the instructions below can now be done in 
    -- the theories
    -- To add an operator:
    -- o add it in the parser
    -- o add it in the associativity chain
    -- o add it in a theory
    -- o add a token for it in data type Operator
    -- o create a function that generates an expression
    --      from the token
mk_expr :: BinOperator -> Expr -> Expr -> Either String Expr
mk_expr (BinOperator _ _ f) x y = f (Right x) (Right y)

mk_unary :: UnaryOperator -> Expr -> Either String Expr
mk_unary (UnaryOperator _ _ f) x = f $ Right x

data Assoc = LeftAssoc | RightAssoc | Ambiguous
    deriving (Show,Eq,Typeable)

data Notation = Notation
    { new_ops :: [Operator]
    , prec :: [[[Operator]]] 
    , left_assoc :: [[BinOperator]]
    , right_assoc :: [[BinOperator]]
    , relations :: [BinOperator]
    , chaining :: [((BinOperator,BinOperator),BinOperator)]
    } deriving (Eq,Show)

empty_notation :: Notation
empty_notation = Notation 
    { new_ops = []
    , prec = []
    , left_assoc = []
    , right_assoc = [] 
    , relations = []
    , chaining = [] }

combine :: Notation -> Notation -> Notation
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

precede :: Notation -> Notation -> Notation
precede x y 
        | L.null $ new_ops x `intersect` new_ops y = 
        let z = (combine x y) in
            z { 
                prec = prec z ++ [ xs ++ ys | xs <- prec x, ys <- prec y ] }
--                              ++ [ [[xs], [ys]] | xs <- new_ops x, ys <- new_ops y ] }
--        Notation
--        { new_ops      = new_ops x ++ new_ops y
--        , prec         =  ++ prec x ++ prec y
--        , left_assoc   = left_assoc x ++ left_assoc y
--        , right_assoc  = right_assoc x ++ right_assoc y }
        | otherwise        = error $ format "Notation, precede: redundant operator names. {0}" common
    where
        f (Right x) = show x
        f (Left y)  = show y
        intersect = intersectBy ((==) `on` f)
        common = L.map f $ new_ops x `intersect` new_ops y

data UnaryOperator = UnaryOperator String String (ExprP -> ExprP)
    deriving Typeable

instance Eq UnaryOperator where
    UnaryOperator x0 x1 _ == UnaryOperator y0 y1 _ = (x0,x1) == (y0,y1)

instance Ord UnaryOperator where
    compare (UnaryOperator x0 x1 _) (UnaryOperator y0 y1 _) = compare (x0,x1) (y0,y1)

instance Show UnaryOperator where
    show (UnaryOperator x y _) = show (x,y) -- format str x y

instance Named Operator where
    name (Right (BinOperator _ xs _))  = xs
    name (Left (UnaryOperator _ xs _)) = xs

data BinOperator = BinOperator String String (ExprP -> ExprP -> ExprP)
    deriving Typeable

instance Eq BinOperator where
    BinOperator x0 x1 _ == BinOperator y0 y1 _ = (x0,x1) == (y0,y1)

instance Ord BinOperator where
    compare (BinOperator x0 x1 _) (BinOperator y0 y1 _) = compare (x0,x1) (y0,y1)

instance Show BinOperator where
    show (BinOperator x y _) = show (x,y) -- format str x y
--        where
--            str = "Binary { token = {0}, lexeme = {1} }"

type Operator = Either UnaryOperator BinOperator

precedence :: Notation -> Matrix Operator Bool
precedence ops = m_closure_with (new_ops ops)
        $ concatMap g $ prec ops
    where
        f (xs,ys) = [ (x,y) | x <- xs, y <- ys ]
        g xs = concatMap f $ zip xs (drop 1 xs)

left_assoc_graph :: Notation -> Matrix BinOperator Bool
left_assoc_graph ops  = assoc_graph (rights $ new_ops ops) $ left_assoc ops

right_assoc_graph :: Notation -> Matrix BinOperator Bool
right_assoc_graph ops = assoc_graph (rights $ new_ops ops) $ right_assoc ops

assoc_graph :: [BinOperator] -> [[BinOperator]] -> Matrix BinOperator Bool
assoc_graph rs xss = as_matrix_with rs ys
    where
        ys = concatMap (\xs -> [ (x,y) | x <- xs, y <- xs ]) xss

assoc' :: Notation -> Matrix Operator Assoc
assoc' ops 
--		| not $ L.null complete = error $ "assoc': all new operators are not declared: " ++ show complete
        | not $ L.null cycles   = error $ "assoc': cycles exist in the precedence graph" ++ show cycles
        | otherwise   = foldl (G.unionWith join) (G.empty Ambiguous)
                  [ G.map (f LeftAssoc) pm :: Matrix Operator Assoc
                  , G.map (f RightAssoc) $ G.transpose pm
                  , G.map (f LeftAssoc) $ G.mapKeys g lm
                  , G.map (f RightAssoc) $ G.mapKeys g rm ]
            -- fromList (zip bs $ L.map g bs)
    where
        cycles = L.filter (\x -> pm G.! (x,x)) (new_ops ops)
--        complete = all_ops L.\\ (nub $ new_ops ops)
--        all_ops = nub $	concat (concat (prec ops) 
--					 ++ L.map (L.map Right) (left_assoc ops)
--					 ++ L.map (L.map Right) (right_assoc ops)
--					 ++ L.map (\((x,y),z) -> L.map Right [x,y,z]) (chaining ops))
--				++ L.map Right (relations ops)
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

    -- Basic functions
apply :: BinOperator
equal :: BinOperator
pair  :: BinOperator

apply = BinOperator "apply" "."     zapply
equal = BinOperator "equal" "="     mzeq
pair  = BinOperator "pair"  "\\mapsto" mzpair

functions :: Notation
functions = Notation
    { new_ops     = L.map Right [equal,apply,pair]
    , prec = [ L.map (L.map Right)
                     [ [apply]
                     , [pair]
                     , [equal] ]]
    , left_assoc  = [[apply],[pair]]
    , right_assoc = []
    , relations   = []
    , chaining    = [] }

    -- logic
disj    :: BinOperator
conj    :: BinOperator
implies :: BinOperator
follows :: BinOperator
equiv   :: BinOperator
neg     :: UnaryOperator

disj    = BinOperator "or" "\\lor"          mzor
conj    = BinOperator "and" "\\land"        mzand
implies = BinOperator "implies" "\\implies" mzimplies
follows = BinOperator "follows" "\\follows" (flip mzimplies)
equiv   = BinOperator "equiv" "\\equiv"   mzeq
neg     = UnaryOperator "neg" "\\neg"       mznot

logic :: Notation
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

double :: (a,b) -> ((a,a),(b,b))
double (x,y) = ((x,x),(y,y))