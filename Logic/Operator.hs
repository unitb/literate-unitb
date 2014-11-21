{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE FlexibleInstances     #-}
module Logic.Operator 
    (   Notation (..)
    ,   BinOperator (..)
    ,   UnaryOperator (..)
    ,   Command (..)
    ,   Assoc (..)
    ,   Operator
    ,   Matrix
    ,   Input (..)
    ,   with_assoc
    ,   empty_notation
    ,   logic, functions
    ,   apply, equal, conj, disj
    ,   implies, follows, equiv
    ,   combine, precede
    ,   mk_expr, mk_unary
        )
where

    -- Modules
import Logic.Expr hiding ( pair )

    -- Libraries
import Control.DeepSeq

import Data.Either
import Data.Function
import Data.List as L
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

instance NFData Assoc where

data Notation = Notation
    { new_ops :: [Operator]
    , prec :: [[[Operator]]] 
    , left_assoc :: [[BinOperator]]
    , right_assoc :: [[BinOperator]]
    , relations :: [BinOperator]
    , chaining :: [((BinOperator,BinOperator),BinOperator)]
    , commands :: [Command]
    , struct :: Matrix Operator Assoc
    } deriving (Eq,Show)

instance NFData Notation where
    rnf (Notation a b c d e f g h) = rnf (a,b,c,d,e,f,g,h)

empty_notation :: Notation
empty_notation = Notation 
    { new_ops = []
    , prec = []
    , left_assoc = []
    , right_assoc = [] 
    , relations = []
    , chaining = []
    , commands = []
    , struct = undefined }

with_assoc :: Notation -> Notation
with_assoc n = n { struct = assoc_table n }
    
combine :: Notation -> Notation -> Notation
combine x y 
    | L.null (new_ops x `intersect` new_ops y)
        && L.null (commands x `intersect` commands y)
        = with_assoc empty_notation
        { new_ops      = new_ops x ++ new_ops y
        , prec         = prec x ++ prec y
        , left_assoc   = left_assoc x ++ left_assoc y
        , right_assoc  = right_assoc x ++ right_assoc y 
        , relations    = relations x ++ relations y
        , commands     = commands x ++ commands y
        , chaining     = chaining x ++ chaining y }
    | otherwise        = error $ format "Notation, combine: redundant operator names. {0}" common
    where
        f (Right (BinOperator x _ _))  = x
        f (Left (UnaryOperator x _ _)) = x
        intersect :: Input a => [a] -> [a] -> [a]
        intersect = intersectBy ((==) `on` token)
        common1 = L.map f $ new_ops x `intersect` new_ops y
        common2 = L.map token $ commands x `intersect` commands y
        common = common1 `union` common2

precede :: Notation -> Notation -> Notation
precede x y 
        | L.null $ new_ops x `intersect` new_ops y = 
        let z = (combine x y) in
            with_assoc z { 
                prec = prec z ++ [ xs ++ ys | xs <- prec x, ys <- prec y ] }
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

instance NFData UnaryOperator where
    rnf (UnaryOperator a b c) = rnf (a,b,c)

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

instance NFData BinOperator where
    rnf (BinOperator a b c) = rnf (a,b,c)

type Operator = Either UnaryOperator BinOperator

data Command = Command String String Int ([ExprP] -> ExprP)

instance Show Command where
    show (Command x y _ _) = show (x,y) -- format str x y

instance Eq Command where
    (==) (Command x0 y0 n0 _) (Command x1 y1 n1 _) =
        (x0,y0,n0) == (x1,y1,n1)
    
instance NFData Command where
    rnf (Command a b c d) = rnf (a,b,c,d)

class Input a where
    token :: a -> String

instance Input BinOperator where
    token (BinOperator tok _ _) = tok

instance Input UnaryOperator where
    token (UnaryOperator tok _ _) = tok

instance Input Command where
    token (Command tok _ _ _) = tok
    
instance Input Operator where
    token (Left x) = token x
    token (Right x) = token x
    
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

assoc_table :: Notation -> Matrix Operator Assoc
assoc_table ops 
--      | not $ L.null complete = error $ "assoc': all new operators are not declared: " ++ show complete
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
--        all_ops = nub $   concat (concat (prec ops) 
--                   ++ L.map (L.map Right) (left_assoc ops)
--                   ++ L.map (L.map Right) (right_assoc ops)
--                   ++ L.map (\((x,y),z) -> L.map Right [x,y,z]) (chaining ops))
--              ++ L.map Right (relations ops)
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
functions = with_assoc empty_notation
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
neg     = UnaryOperator "not" "\\neg"       mznot

logic :: Notation
logic = with_assoc empty_notation
    { new_ops     = Left neg : L.map Right [conj,disj,implies,follows,equiv]
    , prec = [    [Left neg] 
                : L.map (L.map Right)
                     [ [disj,conj]
                     , [implies,follows]
                     , [equiv] ]]
    , left_assoc  = [[equiv],[disj],[conj]]
    , right_assoc = []
    , relations   = [equiv,implies,follows]
    , commands    = 
        [ Command "\\true" "true" 0 $ const mztrue
        , Command "\\false" "false" 0 $ const mzfalse ]
    , chaining    = 
        [ ((equiv,implies),implies)
        , ((implies,equiv),implies)
        , ((implies,implies),implies)
        , ((equiv,equiv),equiv)
        , ((equiv,follows),follows)
        , ((follows,equiv),follows)
        , ((follows,follows),follows) ]  }
