{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE TypeFamilies          #-}
module Logic.Operator 
    ( Notation
    , BinOperator (..)
    , UnaryOperator (..)
    , Command (..)
    , Assoc (..)
    , Operator
    , Matrix
    , Input (..)
    , Flipping(..)
    -- , with_assoc
    , functionName
    , empty_notation
    , logical_notation
    , functional_notation
    , pair_op, make
    , apply, equal, conj, disj
    , implies, follows, equiv
    , combine, precede
    , mk_expr, mk_unary
        -- Lenses
    , new_ops 
    , prec 
    , left_assoc 
    , right_assoc 
    , relations 
    , quantifiers
    , chaining 
    , commands 
    , struct 
    )
where

    -- Modules
import Logic.Expr

    -- Libraries
import Control.DeepSeq
import qualified Control.Invariant as I
import Control.Lens
import Control.Monad
import Control.Precondition

import Data.Default
import Data.Either
import Data.Function
import Data.List as L
import Data.Semigroup
import Data.Serialize
import Data.Typeable

import GHC.Exts
import GHC.Generics.Instances

import Test.QuickCheck as QC
import Test.QuickCheck.ZoomEq

import Text.Printf.TH

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
mk_expr :: BinOperator -> Expr -> Expr -> Either [String] Expr
mk_expr (BinOperator _ _ Flipped f) x y = flip (typ_fun2 f) (Right x) (Right y)
mk_expr (BinOperator _ _ Direct f) x y  = typ_fun2 f (Right x) (Right y)

mk_unary :: UnaryOperator -> Expr -> Either [String] Expr
mk_unary (UnaryOperator _ _ f) x = typ_fun1 f $ Right x

data Assoc = LeftAssoc | RightAssoc | NoAssoc
    deriving (Show,Eq,Typeable,Generic)

data Flipping = Flipped | Direct
    deriving (Eq,Ord,Show,Generic,Typeable,Bounded,Enum)

data Notation = Notation
    { _new_ops :: [Operator]
    , _prec :: [[[Operator]]] 
    , _left_assoc :: [[BinOperator]]
    , _right_assoc :: [[BinOperator]]
    , _relations :: [BinOperator]
    , _chaining :: [((BinOperator,BinOperator),BinOperator)]
    , _commands :: [Command]
    , _quantifiers :: [(Name,HOQuantifier)]
    , _struct :: Matrix Operator Assoc
    } deriving (Eq,Generic,Show)

instance ZoomEq Notation where
    (.==) = (I.===)
instance PrettyPrintable Notation where
    pretty _ = "<notation>" 

instance Serialize Command where
instance Serialize UnaryOperator where
instance Serialize BinOperator where

instance Serialize Notation where
    put (Notation a b c d e f g h _) = do
            put a >> put b >> put c
            put d >> put e >> put f
            put g >> put h
    get = fmap with_assoc $ 
            Notation <$> get <*> get <*> get
                     <*> get <*> get <*> get
                     <*> get <*> get <*> pure undefined

empty_notation :: Notation
empty_notation = with_assoc $ Notation 
    { _new_ops = []
    , _prec = []
    , _left_assoc = []
    , _right_assoc = [] 
    , _relations = []
    , _chaining = []
    , _commands = []
    , _quantifiers = []
    , _struct = undefined' }

new_ops :: Lens' Notation [Operator]
new_ops = lens _new_ops (\n x -> with_assoc $ n { _new_ops = x })
prec :: Lens' Notation [[[Operator]]]
prec = lens _prec (\n x -> with_assoc $ n { _prec = x })
left_assoc :: Lens' Notation [[BinOperator]]
left_assoc = lens _left_assoc (\n x -> with_assoc $ n { _left_assoc = x })
right_assoc :: Lens' Notation [[BinOperator]]
right_assoc = lens _right_assoc (\n x -> with_assoc $ n { _right_assoc = x })
relations :: Lens' Notation [BinOperator]
relations = lens _relations (\n x -> with_assoc $ n { _relations = x })
chaining :: Lens' Notation [((BinOperator,BinOperator),BinOperator)]
chaining = lens _chaining (\n x -> with_assoc $ n { _chaining = x })
commands :: Lens' Notation [Command]
commands = lens _commands (\n x -> with_assoc $ n { _commands = x })
quantifiers :: Lens' Notation [(Name,HOQuantifier)]
quantifiers = lens _quantifiers (\n x -> with_assoc $ n { _quantifiers = x })
struct :: Getter Notation (Matrix Operator Assoc)
struct = to _struct

instance Default Notation where
    def = empty_notation

with_assoc :: Notation -> Notation
with_assoc n = n { _struct = assoc_table n }

instance Semigroup Notation where
    (<>) = combine

instance Monoid Notation where
    mempty = empty_notation
    mappend = combine

combine :: Notation -> Notation -> Notation
combine x y 
    | L.null (_new_ops x `intersect` _new_ops y)
        && L.null (_commands x `intersect` _commands y)
        = with_assoc empty_notation
        { _new_ops      = _new_ops x ++ _new_ops y
        , _prec         = _prec x ++ _prec y
        , _left_assoc   = _left_assoc x  ++ _left_assoc y
        , _right_assoc  = _right_assoc x ++ _right_assoc y 
        , _relations    = _relations x ++ _relations y
        , _commands     = _commands x  ++ _commands y
        , _quantifiers  = _quantifiers x ++ _quantifiers y
        , _chaining     = _chaining x  ++ _chaining y }
    | otherwise        = error $ [printf|Notation, combine: redundant operator names. %s|] (pretty common)
    where
        intersect :: Input a => [a] -> [a] -> [a]
        intersect = intersectBy ((==) `on` token)
        common1 = L.map token $ _new_ops x `intersect` _new_ops y
        common2 = L.map token $ _commands x `intersect` _commands y
        common = common1 `union` common2

precede :: Notation -> Notation -> Notation
precede x y 
        | L.null $ _new_ops x `intersect` _new_ops y = 
        let z = (combine x y) in
            with_assoc z { 
                _prec = _prec z ++ [ xs ++ ys | xs <- _prec x, ys <- _prec y ] }
        | otherwise        = error $ [printf|Notation, precede: redundant operator names. %s|] (show common)
    where
        f (Right x) = show x
        f (Left y)  = show y
        intersect = intersectBy ((==) `on` f)
        common = L.map f $ _new_ops x `intersect` _new_ops y

data UnaryOperator = UnaryOperator InternalName Name Fun
    deriving (Typeable,Generic,Eq,Ord,Show)




instance PrettyPrintable UnaryOperator where
    pretty (UnaryOperator x y _) = pretty (x,y) -- format str x y

instance HasName Operator Name where
    name = to $ \case 
        (Right (BinOperator _ xs _ _))  -> xs
        (Left (UnaryOperator _ xs _)) -> xs

instance Named Operator where
    type NameOf Operator = Name
    decorated_name' = adaptName . view name

functionName :: Operator -> Name
functionName (Right (BinOperator xs _ _ _)) = asName xs
functionName (Left (UnaryOperator xs _ _))  = asName xs

data BinOperator = BinOperator InternalName Name Flipping Fun
    deriving (Typeable,Generic,Eq,Ord,Show)

instance ZoomEq BinOperator where
    (.==) = (I.===)

instance PrettyPrintable BinOperator where
    pretty (BinOperator x y _ _) = pretty (x,y) -- format str x y

type Operator = Either UnaryOperator BinOperator

data Command = Command Name InternalName Int Fun
    deriving (Generic,Show,Eq)

instance PrettyPrintable Command where
    pretty (Command x y _ _) = pretty (x,y)


class Input a where
    token :: a -> Name

instance Input BinOperator where
    token (BinOperator _ tok _ _) = tok

instance Input UnaryOperator where
    token (UnaryOperator _ tok _) = tok

instance Input Command where
    token (Command tok _ _ _) = tok
    
instance Input Operator where
    token = either token token
    
precedence :: Notation -> Matrix Operator Bool
precedence ops = m_closure_with (_new_ops ops)
        $ concatMap g $ _prec ops
    where
        f (xs,ys) = [ (x,y) | x <- xs, y <- ys ]
        g xs = concatMap f $ zip xs (drop 1 xs)

left_assoc_graph :: Notation -> Matrix BinOperator Bool
left_assoc_graph ops  = assoc_graph (rights $ _new_ops ops) $ _left_assoc ops

right_assoc_graph :: Notation -> Matrix BinOperator Bool
right_assoc_graph ops = assoc_graph (rights $ _new_ops ops) $ _right_assoc ops

assoc_graph :: [BinOperator] -> [[BinOperator]] -> Matrix BinOperator Bool
assoc_graph rs xss = as_matrix_with rs ys
    where
        ys = concatMap (\xs -> [ (x,y) | x <- xs, y <- xs ]) xss

assoc_table :: Notation -> Matrix Operator Assoc
assoc_table ops 
--      | not $ L.null complete = error $ "assoc': all new operators are not declared: " ++ show complete
        | not $ L.null cycles   = error $ "assoc': cycles exist in the precedence graph" ++ show cycles
        | otherwise   = foldl' (G.unionWith join) (G.empty NoAssoc)
                  [ G.map (f LeftAssoc) pm :: Matrix Operator Assoc
                  , G.map (f RightAssoc) $ G.transpose pm
                  , G.map (f LeftAssoc) $ G.mapKeys g lm
                  , G.map (f RightAssoc) $ G.mapKeys g rm ]
    where
        cycles = L.filter (\x -> pm G.! (x,x)) (_new_ops ops)
        pm = precedence ops
        lm = left_assoc_graph ops
        rm = right_assoc_graph ops
        f a b 
            | b         = a
            | otherwise = NoAssoc
        g (x,y) = (Right x,Right y)
        join x NoAssoc = x
        join NoAssoc x = x
        join _ _ = error "operator parser: conflicting precedences"

    -- Basic functions
apply   :: BinOperator
equal   :: BinOperator
pair_op :: BinOperator

apply   = make BinOperator "apply" "."     Direct apply_fun
equal   = make BinOperator "equal" "="     Direct (zeq_fun gA)
pair_op = make BinOperator "pair"  "\\mapsto" Direct pair_fun

functional_notation :: Notation
functional_notation = with_assoc empty_notation
    { _new_ops     = L.map Right [equal,apply,pair_op]
    , _prec = [ L.map (L.map Right)
                     [ [apply]
                     , [pair_op]
                     , [equal] ]]
    , _commands    = [ Command [tex|\ifelse|] [smt|ite|] 3 ite_fun ]
    , _left_assoc  = [[apply],[pair_op]]
    , _right_assoc = []
    , _relations   = []
    , _quantifiers = [ (fromString'' "\\qforall", Forall)
                     , (fromString'' "\\qexists", Exists) ]
    , _chaining    = [] }

    -- logic
disj    :: BinOperator
conj    :: BinOperator
implies :: BinOperator
follows :: BinOperator
equiv   :: BinOperator
neg     :: UnaryOperator

disj    = make BinOperator "or" "\\lor"          Direct (or_fun 2)
conj    = make BinOperator "and" "\\land"        Direct (and_fun 2)
implies = make BinOperator "implies" "\\implies" Direct implies_fun
follows = make BinOperator "follows" "\\follows" Flipped implies_fun
equiv   = make BinOperator "equiv" "\\equiv"     Direct (zeq_fun gA)
neg     = make UnaryOperator "not" "\\neg"       not_fun

logical_notation :: Notation
logical_notation = with_assoc empty_notation
    { _new_ops     = Left neg : L.map Right [conj,disj,implies,follows,equiv]
    , _prec = [    [Left neg] 
                : L.map (L.map Right)
                     [ [disj,conj]
                     , [implies,follows]
                     , [equiv] ]]
    , _left_assoc  = [[equiv],[disj],[conj]]
    , _right_assoc = []
    , _relations   = [equiv,implies,follows]
    , _commands    = 
        [ make Command "\\true" "true" 0   true_fun
        , make Command "\\false" "false" 0 false_fun ]
    , _chaining    = 
        [ ((equiv,implies),implies)
        , ((implies,equiv),implies)
        , ((implies,implies),implies)
        , ((equiv,equiv),equiv)
        , ((equiv,follows),follows)
        , ((follows,equiv),follows)
        , ((follows,follows),follows) ]  }

instance NFData Notation
instance NFData UnaryOperator
instance NFData Command
instance NFData BinOperator
instance NFData Assoc
instance NFData Flipping

instance Arbitrary UnaryOperator where
    arbitrary = genericArbitrary
    shrink = genericShrink
instance Arbitrary BinOperator where
    arbitrary = genericArbitrary
    shrink = genericShrink
instance Arbitrary Command where
    arbitrary = genericArbitrary
    shrink = genericShrink
instance Arbitrary Notation where
    arbitrary = do
        xs <- listOf arbitrary
        new_ops (const $ return xs) empty_notation
            >>= prec (const arbitrary)
            >>= left_assoc  (const $ partitionOf <=< sublistOf $ rights xs)
            >>= right_assoc (const $ partitionOf <=< sublistOf $ rights xs)
            >>= quantifiers (const arbitrary)
            >>= commands (const arbitrary)
    -- , _relations = []
    -- , _chaining = []
    -- , _commands = []

partitionOf :: [a] -> Gen [[a]]
partitionOf xs = do
    n  <- choose (1,length xs)
    ys <- mapM (sequence . (,choose (1,n))) xs
    return $ groupWith snd ys & traverse.traverse %~ fst

instance Arbitrary Flipping where
    arbitrary = genericArbitrary

instance Serialize Flipping where
