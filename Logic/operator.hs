{-# LANGUAGE DeriveDataTypeable #-}
module Logic.Operator where

    -- Modules
import Theories.SetTheory
import Theories.FunctionTheory

import Logic.Expr
import Logic.Const

    -- Libraries
import Data.Array as A
import Data.IORef
import Data.List as L
import Data.Map as M hiding ( foldl )
import Data.Typeable

import System.IO.Unsafe

import Utilities.Graph

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
    deriving (Eq,Ord,Show,Enum,Ix,Typeable)

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
    deriving (Show,Eq,Typeable)

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
        , ([ Equal,Leq,Less
           , Membership,Geq,Greater],Ambiguous)
        , ([And],LeftAssoc)
        , ([Or],LeftAssoc)
        , ([Implies,Follows],Ambiguous) 
        , ([Equiv],LeftAssoc)
        ]

data Notation = Notation
    { prec :: [[[BinOperator]]] 
    , left_assoc :: [[BinOperator]]
    , right_assoc :: [[BinOperator]] }

empty_notation = Notation 
    { prec = []
    , left_assoc = []
    , right_assoc = [] }

combine x y = Notation
    { prec         = prec x ++ prec y
    , left_assoc   = left_assoc x ++ left_assoc y
    , right_assoc  = right_assoc x ++ right_assoc y }

functions = Notation
    { prec        = [[ [Apply]
                     , [Equal] ]]
    , left_assoc  = [[Apply]]
    , right_assoc = [] }
logic = Notation
    { prec        = [[ [Apply]
                     , [Equal]
                     , [Or,And]
                     , [Implies,Follows]
                     , [Equiv] ]]
    , left_assoc  = [[Equiv],[And],[Or]]
    , right_assoc = []  }
set_notation = Notation
    { prec    = [[ [Apply]
                 , [Overload]
                 , [Union,SetDiff]
                 , [DomRest,DomSubt] 
                 , [ Equal
                   , Membership] 
                 , [ And, Or ] ]]
    , left_assoc  = [[Union],[Overload]
                    ,[DomRest,DomSubt]]
    , right_assoc = []  }
arith = Notation
    { prec        = [[ [Apply]
                     , [Power]
                     , [Mult]
                     , [Plus]
                     , [MkFunction]
                     , [Overload]
                     , [ Equal,Leq
                       , Less
                       , Geq,Greater] 
                     , [ And, Or ]]]
    , left_assoc  = [[Mult],[Plus]]
    , right_assoc = [] }

notations = foldl combine empty_notation
    [ functions
    , logic
    , arith
    , set_notation ] 

precedence ops = m_closure_with (range bin_op_range)
        $ concatMap g $ prec ops
    where
        f (xs,ys) = [ (x,y) | x <- xs, y <- ys ]
        g xs = concatMap f $ zip xs (drop 1 xs)

type Matrix a b = Array (a,a) b

left_assoc_graph :: Notation -> Matrix BinOperator Bool
left_assoc_graph ops  = assoc_graph $ left_assoc ops

right_assoc_graph :: Notation -> Matrix BinOperator Bool
right_assoc_graph ops = assoc_graph $ right_assoc ops

bin_op_range = (x,y)
    where
        x = toEnum 0
        y = last $ enumFrom x

assoc_graph :: [[BinOperator]] -> Matrix BinOperator Bool
assoc_graph xss = as_matrix_with (range bin_op_range) ys
    where
        ys = concatMap (\xs -> [ (x,y) | x <- xs, y <- xs ]) xss

assoc' :: Notation -> Matrix BinOperator Assoc
assoc' ops = array (bounds pm) (zip bs $ L.map g bs)
    where
        pm = precedence ops
        lm = left_assoc_graph ops
        rm = right_assoc_graph ops
        bs = range $ bounds pm
        g (i,j)
            | pm A.! (i,j) = LeftAssoc
            | pm A.! (j,i) = RightAssoc
            | lm A.! (i,j) = LeftAssoc
            | rm A.! (i,j) = RightAssoc
            | otherwise  = Ambiguous

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

--assoc x y = pairs M.! (x,y)
assoc x y = unsafePerformIO $ do
    r <- readIORef assoc_table
    return $ r M.! (x,y)

--assoc_table = unsafePerformIO $ newIORef $ fromList (A.assocs $ assoc' notations)
assoc_table = unsafePerformIO $ newIORef $ fromList [((SetDiff,SetDiff),Ambiguous),((SetDiff,Apply),RightAssoc),((SetDiff,Plus),RightAssoc),((SetDiff,Mult),RightAssoc),((SetDiff,Power),RightAssoc),((SetDiff,Equal),LeftAssoc),((SetDiff,Leq),Ambiguous),((SetDiff,Geq),Ambiguous),((SetDiff,Less),Ambiguous),((SetDiff,Greater),Ambiguous),((SetDiff,Membership),LeftAssoc),((SetDiff,Union),Ambiguous),((SetDiff,Overload),RightAssoc),((SetDiff,DomSubt),LeftAssoc),((SetDiff,DomRest),LeftAssoc),((SetDiff,MkFunction),RightAssoc),((SetDiff,TotalFunction),Ambiguous),((SetDiff,And),LeftAssoc),((SetDiff,Or),LeftAssoc),((SetDiff,Implies),LeftAssoc),((SetDiff,Follows),LeftAssoc),((SetDiff,Equiv),LeftAssoc),((Apply,SetDiff),LeftAssoc),((Apply,Apply),LeftAssoc),((Apply,Plus),LeftAssoc),((Apply,Mult),LeftAssoc),((Apply,Power),LeftAssoc),((Apply,Equal),LeftAssoc),((Apply,Leq),LeftAssoc),((Apply,Geq),LeftAssoc),((Apply,Less),LeftAssoc),((Apply,Greater),LeftAssoc),((Apply,Membership),LeftAssoc),((Apply,Union),LeftAssoc),((Apply,Overload),LeftAssoc),((Apply,DomSubt),LeftAssoc),((Apply,DomRest),LeftAssoc),((Apply,MkFunction),LeftAssoc),((Apply,TotalFunction),Ambiguous),((Apply,And),LeftAssoc),((Apply,Or),LeftAssoc),((Apply,Implies),LeftAssoc),((Apply,Follows),LeftAssoc),((Apply,Equiv),LeftAssoc),((Plus,SetDiff),LeftAssoc),((Plus,Apply),RightAssoc),((Plus,Plus),LeftAssoc),((Plus,Mult),RightAssoc),((Plus,Power),RightAssoc),((Plus,Equal),LeftAssoc),((Plus,Leq),LeftAssoc),((Plus,Geq),LeftAssoc),((Plus,Less),LeftAssoc),((Plus,Greater),LeftAssoc),((Plus,Membership),LeftAssoc),((Plus,Union),LeftAssoc),((Plus,Overload),LeftAssoc),((Plus,DomSubt),LeftAssoc),((Plus,DomRest),LeftAssoc),((Plus,MkFunction),LeftAssoc),((Plus,TotalFunction),Ambiguous),((Plus,And),LeftAssoc),((Plus,Or),LeftAssoc),((Plus,Implies),LeftAssoc),((Plus,Follows),LeftAssoc),((Plus,Equiv),LeftAssoc),((Mult,SetDiff),LeftAssoc),((Mult,Apply),RightAssoc),((Mult,Plus),LeftAssoc),((Mult,Mult),LeftAssoc),((Mult,Power),RightAssoc),((Mult,Equal),LeftAssoc),((Mult,Leq),LeftAssoc),((Mult,Geq),LeftAssoc),((Mult,Less),LeftAssoc),((Mult,Greater),LeftAssoc),((Mult,Membership),LeftAssoc),((Mult,Union),LeftAssoc),((Mult,Overload),LeftAssoc),((Mult,DomSubt),LeftAssoc),((Mult,DomRest),LeftAssoc),((Mult,MkFunction),LeftAssoc),((Mult,TotalFunction),Ambiguous),((Mult,And),LeftAssoc),((Mult,Or),LeftAssoc),((Mult,Implies),LeftAssoc),((Mult,Follows),LeftAssoc),((Mult,Equiv),LeftAssoc),((Power,SetDiff),LeftAssoc),((Power,Apply),RightAssoc),((Power,Plus),LeftAssoc),((Power,Mult),LeftAssoc),((Power,Power),Ambiguous),((Power,Equal),LeftAssoc),((Power,Leq),LeftAssoc),((Power,Geq),LeftAssoc),((Power,Less),LeftAssoc),((Power,Greater),LeftAssoc),((Power,Membership),LeftAssoc),((Power,Union),LeftAssoc),((Power,Overload),LeftAssoc),((Power,DomSubt),LeftAssoc),((Power,DomRest),LeftAssoc),((Power,MkFunction),LeftAssoc),((Power,TotalFunction),Ambiguous),((Power,And),LeftAssoc),((Power,Or),LeftAssoc),((Power,Implies),LeftAssoc),((Power,Follows),LeftAssoc),((Power,Equiv),LeftAssoc),((Equal,SetDiff),RightAssoc),((Equal,Apply),RightAssoc),((Equal,Plus),RightAssoc),((Equal,Mult),RightAssoc),((Equal,Power),RightAssoc),((Equal,Equal),Ambiguous),((Equal,Leq),Ambiguous),((Equal,Geq),Ambiguous),((Equal,Less),Ambiguous),((Equal,Greater),Ambiguous),((Equal,Membership),Ambiguous),((Equal,Union),RightAssoc),((Equal,Overload),RightAssoc),((Equal,DomSubt),RightAssoc),((Equal,DomRest),RightAssoc),((Equal,MkFunction),RightAssoc),((Equal,TotalFunction),Ambiguous),((Equal,And),LeftAssoc),((Equal,Or),LeftAssoc),((Equal,Implies),LeftAssoc),((Equal,Follows),LeftAssoc),((Equal,Equiv),LeftAssoc),((Leq,SetDiff),Ambiguous),((Leq,Apply),RightAssoc),((Leq,Plus),RightAssoc),((Leq,Mult),RightAssoc),((Leq,Power),RightAssoc),((Leq,Equal),Ambiguous),((Leq,Leq),Ambiguous),((Leq,Geq),Ambiguous),((Leq,Less),Ambiguous),((Leq,Greater),Ambiguous),((Leq,Membership),Ambiguous),((Leq,Union),Ambiguous),((Leq,Overload),RightAssoc),((Leq,DomSubt),Ambiguous),((Leq,DomRest),Ambiguous),((Leq,MkFunction),RightAssoc),((Leq,TotalFunction),Ambiguous),((Leq,And),LeftAssoc),((Leq,Or),LeftAssoc),((Leq,Implies),LeftAssoc),((Leq,Follows),LeftAssoc),((Leq,Equiv),LeftAssoc),((Geq,SetDiff),Ambiguous),((Geq,Apply),RightAssoc),((Geq,Plus),RightAssoc),((Geq,Mult),RightAssoc),((Geq,Power),RightAssoc),((Geq,Equal),Ambiguous),((Geq,Leq),Ambiguous),((Geq,Geq),Ambiguous),((Geq,Less),Ambiguous),((Geq,Greater),Ambiguous),((Geq,Membership),Ambiguous),((Geq,Union),Ambiguous),((Geq,Overload),RightAssoc),((Geq,DomSubt),Ambiguous),((Geq,DomRest),Ambiguous),((Geq,MkFunction),RightAssoc),((Geq,TotalFunction),Ambiguous),((Geq,And),LeftAssoc),((Geq,Or),LeftAssoc),((Geq,Implies),LeftAssoc),((Geq,Follows),LeftAssoc),((Geq,Equiv),LeftAssoc),((Less,SetDiff),Ambiguous),((Less,Apply),RightAssoc),((Less,Plus),RightAssoc),((Less,Mult),RightAssoc),((Less,Power),RightAssoc),((Less,Equal),Ambiguous),((Less,Leq),Ambiguous),((Less,Geq),Ambiguous),((Less,Less),Ambiguous),((Less,Greater),Ambiguous),((Less,Membership),Ambiguous),((Less,Union),Ambiguous),((Less,Overload),RightAssoc),((Less,DomSubt),Ambiguous),((Less,DomRest),Ambiguous),((Less,MkFunction),RightAssoc),((Less,TotalFunction),Ambiguous),((Less,And),LeftAssoc),((Less,Or),LeftAssoc),((Less,Implies),LeftAssoc),((Less,Follows),LeftAssoc),((Less,Equiv),LeftAssoc),((Greater,SetDiff),Ambiguous),((Greater,Apply),RightAssoc),((Greater,Plus),RightAssoc),((Greater,Mult),RightAssoc),((Greater,Power),RightAssoc),((Greater,Equal),Ambiguous),((Greater,Leq),Ambiguous),((Greater,Geq),Ambiguous),((Greater,Less),Ambiguous),((Greater,Greater),Ambiguous),((Greater,Membership),Ambiguous),((Greater,Union),Ambiguous),((Greater,Overload),RightAssoc),((Greater,DomSubt),Ambiguous),((Greater,DomRest),Ambiguous),((Greater,MkFunction),RightAssoc),((Greater,TotalFunction),Ambiguous),((Greater,And),LeftAssoc),((Greater,Or),LeftAssoc),((Greater,Implies),LeftAssoc),((Greater,Follows),LeftAssoc),((Greater,Equiv),LeftAssoc),((Membership,SetDiff),RightAssoc),((Membership,Apply),RightAssoc),((Membership,Plus),RightAssoc),((Membership,Mult),RightAssoc),((Membership,Power),RightAssoc),((Membership,Equal),Ambiguous),((Membership,Leq),Ambiguous),((Membership,Geq),Ambiguous),((Membership,Less),Ambiguous),((Membership,Greater),Ambiguous),((Membership,Membership),Ambiguous),((Membership,Union),RightAssoc),((Membership,Overload),RightAssoc),((Membership,DomSubt),RightAssoc),((Membership,DomRest),RightAssoc),((Membership,MkFunction),RightAssoc),((Membership,TotalFunction),Ambiguous),((Membership,And),LeftAssoc),((Membership,Or),LeftAssoc),((Membership,Implies),LeftAssoc),((Membership,Follows),LeftAssoc),((Membership,Equiv),LeftAssoc),((Union,SetDiff),Ambiguous),((Union,Apply),RightAssoc),((Union,Plus),RightAssoc),((Union,Mult),RightAssoc),((Union,Power),RightAssoc),((Union,Equal),LeftAssoc),((Union,Leq),Ambiguous),((Union,Geq),Ambiguous),((Union,Less),Ambiguous),((Union,Greater),Ambiguous),((Union,Membership),LeftAssoc),((Union,Union),LeftAssoc),((Union,Overload),RightAssoc),((Union,DomSubt),LeftAssoc),((Union,DomRest),LeftAssoc),((Union,MkFunction),RightAssoc),((Union,TotalFunction),Ambiguous),((Union,And),LeftAssoc),((Union,Or),LeftAssoc),((Union,Implies),LeftAssoc),((Union,Follows),LeftAssoc),((Union,Equiv),LeftAssoc),((Overload,SetDiff),LeftAssoc),((Overload,Apply),RightAssoc),((Overload,Plus),RightAssoc),((Overload,Mult),RightAssoc),((Overload,Power),RightAssoc),((Overload,Equal),LeftAssoc),((Overload,Leq),LeftAssoc),((Overload,Geq),LeftAssoc),((Overload,Less),LeftAssoc),((Overload,Greater),LeftAssoc),((Overload,Membership),LeftAssoc),((Overload,Union),LeftAssoc),((Overload,Overload),LeftAssoc),((Overload,DomSubt),LeftAssoc),((Overload,DomRest),LeftAssoc),((Overload,MkFunction),RightAssoc),((Overload,TotalFunction),Ambiguous),((Overload,And),LeftAssoc),((Overload,Or),LeftAssoc),((Overload,Implies),LeftAssoc),((Overload,Follows),LeftAssoc),((Overload,Equiv),LeftAssoc),((DomSubt,SetDiff),RightAssoc),((DomSubt,Apply),RightAssoc),((DomSubt,Plus),RightAssoc),((DomSubt,Mult),RightAssoc),((DomSubt,Power),RightAssoc),((DomSubt,Equal),LeftAssoc),((DomSubt,Leq),Ambiguous),((DomSubt,Geq),Ambiguous),((DomSubt,Less),Ambiguous),((DomSubt,Greater),Ambiguous),((DomSubt,Membership),LeftAssoc),((DomSubt,Union),RightAssoc),((DomSubt,Overload),RightAssoc),((DomSubt,DomSubt),LeftAssoc),((DomSubt,DomRest),LeftAssoc),((DomSubt,MkFunction),RightAssoc),((DomSubt,TotalFunction),Ambiguous),((DomSubt,And),LeftAssoc),((DomSubt,Or),LeftAssoc),((DomSubt,Implies),LeftAssoc),((DomSubt,Follows),LeftAssoc),((DomSubt,Equiv),LeftAssoc),((DomRest,SetDiff),RightAssoc),((DomRest,Apply),RightAssoc),((DomRest,Plus),RightAssoc),((DomRest,Mult),RightAssoc),((DomRest,Power),RightAssoc),((DomRest,Equal),LeftAssoc),((DomRest,Leq),Ambiguous),((DomRest,Geq),Ambiguous),((DomRest,Less),Ambiguous),((DomRest,Greater),Ambiguous),((DomRest,Membership),LeftAssoc),((DomRest,Union),RightAssoc),((DomRest,Overload),RightAssoc),((DomRest,DomSubt),LeftAssoc),((DomRest,DomRest),LeftAssoc),((DomRest,MkFunction),RightAssoc),((DomRest,TotalFunction),Ambiguous),((DomRest,And),LeftAssoc),((DomRest,Or),LeftAssoc),((DomRest,Implies),LeftAssoc),((DomRest,Follows),LeftAssoc),((DomRest,Equiv),LeftAssoc),((MkFunction,SetDiff),LeftAssoc),((MkFunction,Apply),RightAssoc),((MkFunction,Plus),RightAssoc),((MkFunction,Mult),RightAssoc),((MkFunction,Power),RightAssoc),((MkFunction,Equal),LeftAssoc),((MkFunction,Leq),LeftAssoc),((MkFunction,Geq),LeftAssoc),((MkFunction,Less),LeftAssoc),((MkFunction,Greater),LeftAssoc),((MkFunction,Membership),LeftAssoc),((MkFunction,Union),LeftAssoc),((MkFunction,Overload),LeftAssoc),((MkFunction,DomSubt),LeftAssoc),((MkFunction,DomRest),LeftAssoc),((MkFunction,MkFunction),Ambiguous),((MkFunction,TotalFunction),Ambiguous),((MkFunction,And),LeftAssoc),((MkFunction,Or),LeftAssoc),((MkFunction,Implies),LeftAssoc),((MkFunction,Follows),LeftAssoc),((MkFunction,Equiv),LeftAssoc),((TotalFunction,SetDiff),Ambiguous),((TotalFunction,Apply),Ambiguous),((TotalFunction,Plus),Ambiguous),((TotalFunction,Mult),Ambiguous),((TotalFunction,Power),Ambiguous),((TotalFunction,Equal),Ambiguous),((TotalFunction,Leq),Ambiguous),((TotalFunction,Geq),Ambiguous),((TotalFunction,Less),Ambiguous),((TotalFunction,Greater),Ambiguous),((TotalFunction,Membership),Ambiguous),((TotalFunction,Union),Ambiguous),((TotalFunction,Overload),Ambiguous),((TotalFunction,DomSubt),Ambiguous),((TotalFunction,DomRest),Ambiguous),((TotalFunction,MkFunction),Ambiguous),((TotalFunction,TotalFunction),Ambiguous),((TotalFunction,And),Ambiguous),((TotalFunction,Or),Ambiguous),((TotalFunction,Implies),Ambiguous),((TotalFunction,Follows),Ambiguous),((TotalFunction,Equiv),Ambiguous),((And,SetDiff),RightAssoc),((And,Apply),RightAssoc),((And,Plus),RightAssoc),((And,Mult),RightAssoc),((And,Power),RightAssoc),((And,Equal),RightAssoc),((And,Leq),RightAssoc),((And,Geq),RightAssoc),((And,Less),RightAssoc),((And,Greater),RightAssoc),((And,Membership),RightAssoc),((And,Union),RightAssoc),((And,Overload),RightAssoc),((And,DomSubt),RightAssoc),((And,DomRest),RightAssoc),((And,MkFunction),RightAssoc),((And,TotalFunction),Ambiguous),((And,And),LeftAssoc),((And,Or),Ambiguous),((And,Implies),LeftAssoc),((And,Follows),LeftAssoc),((And,Equiv),LeftAssoc),((Or,SetDiff),RightAssoc),((Or,Apply),RightAssoc),((Or,Plus),RightAssoc),((Or,Mult),RightAssoc),((Or,Power),RightAssoc),((Or,Equal),RightAssoc),((Or,Leq),RightAssoc),((Or,Geq),RightAssoc),((Or,Less),RightAssoc),((Or,Greater),RightAssoc),((Or,Membership),RightAssoc),((Or,Union),RightAssoc),((Or,Overload),RightAssoc),((Or,DomSubt),RightAssoc),((Or,DomRest),RightAssoc),((Or,MkFunction),RightAssoc),((Or,TotalFunction),Ambiguous),((Or,And),Ambiguous),((Or,Or),LeftAssoc),((Or,Implies),LeftAssoc),((Or,Follows),LeftAssoc),((Or,Equiv),LeftAssoc),((Implies,SetDiff),RightAssoc),((Implies,Apply),RightAssoc),((Implies,Plus),RightAssoc),((Implies,Mult),RightAssoc),((Implies,Power),RightAssoc),((Implies,Equal),RightAssoc),((Implies,Leq),RightAssoc),((Implies,Geq),RightAssoc),((Implies,Less),RightAssoc),((Implies,Greater),RightAssoc),((Implies,Membership),RightAssoc),((Implies,Union),RightAssoc),((Implies,Overload),RightAssoc),((Implies,DomSubt),RightAssoc),((Implies,DomRest),RightAssoc),((Implies,MkFunction),RightAssoc),((Implies,TotalFunction),Ambiguous),((Implies,And),RightAssoc),((Implies,Or),RightAssoc),((Implies,Implies),Ambiguous),((Implies,Follows),Ambiguous),((Implies,Equiv),LeftAssoc),((Follows,SetDiff),RightAssoc),((Follows,Apply),RightAssoc),((Follows,Plus),RightAssoc),((Follows,Mult),RightAssoc),((Follows,Power),RightAssoc),((Follows,Equal),RightAssoc),((Follows,Leq),RightAssoc),((Follows,Geq),RightAssoc),((Follows,Less),RightAssoc),((Follows,Greater),RightAssoc),((Follows,Membership),RightAssoc),((Follows,Union),RightAssoc),((Follows,Overload),RightAssoc),((Follows,DomSubt),RightAssoc),((Follows,DomRest),RightAssoc),((Follows,MkFunction),RightAssoc),((Follows,TotalFunction),Ambiguous),((Follows,And),RightAssoc),((Follows,Or),RightAssoc),((Follows,Implies),Ambiguous),((Follows,Follows),Ambiguous),((Follows,Equiv),LeftAssoc),((Equiv,SetDiff),RightAssoc),((Equiv,Apply),RightAssoc),((Equiv,Plus),RightAssoc),((Equiv,Mult),RightAssoc),((Equiv,Power),RightAssoc),((Equiv,Equal),RightAssoc),((Equiv,Leq),RightAssoc),((Equiv,Geq),RightAssoc),((Equiv,Less),RightAssoc),((Equiv,Greater),RightAssoc),((Equiv,Membership),RightAssoc),((Equiv,Union),RightAssoc),((Equiv,Overload),RightAssoc),((Equiv,DomSubt),RightAssoc),((Equiv,DomRest),RightAssoc),((Equiv,MkFunction),RightAssoc),((Equiv,TotalFunction),Ambiguous),((Equiv,And),RightAssoc),((Equiv,Or),RightAssoc),((Equiv,Implies),RightAssoc),((Equiv,Follows),RightAssoc),((Equiv,Equiv),LeftAssoc)]

double (x,y) = ((x,x),(y,y))

assoc0 = array rs (zip xs $ L.map (pairs M.!) xs)
    where
        rs    = double bin_op_range
        xs    = range rs

binds :: UnaryOperator -> BinOperator -> Assoc
binds Negation x
    | logical x = LeftAssoc
    | otherwise = RightAssoc