module Theories.Notation where

    -- Modules
import Logic.Const
import Logic.Operator

import Theories.Arithmetic
import Theories.FunctionTheory
import Theories.SetTheory

    -- Libraries
import qualified Data.Array as A
import           Data.List as L ( map )
import           Data.Map as M hiding ( foldl )
import           Data.IORef

import Utilities.Format

import System.IO.Unsafe

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

notations = flip precede logic $ foldl combine empty_notation
    [ functions
    , arith
	, function_notation
    , set_notation ] 

assoc :: BinOperator -> BinOperator -> Assoc
assoc x y = unsafePerformIO $ do
    r <- readIORef assoc_table
    return $ r M.! (Right x,Right y)

assoc_table = unsafePerformIO $ newIORef (assoc' notations)

chain x y 
    | x == equal = y
    | y == equal = x
    | otherwise  = case M.lookup (x,y) $ fromList (chaining notations) of
                    Just z -> z
                    Nothing -> error $ format "chain: operators {0} and {1} don't chain" x y

binds :: UnaryOperator -> BinOperator -> Assoc
binds x y = unsafePerformIO $ do
    r <- readIORef assoc_table 
    return $ r M.! (Left x,Right y)

assoc0 :: Map (Operator, Operator) Assoc
assoc0 = fromList (zip (L.map xbin_to_bin xs) $ L.map (pairs M.!) xs)
    where
        rs    = double bin_op_range
        xs    = A.range rs

xbin_to_bin (x,y) = (m x, m y)
    where
        m Equal         = Right equal
        m SetDiff       = Right set_diff
        m Apply         = Right apply
        m Plus          = Right plus
        m Mult          = Right mult
        m Power         = Right power
        m Leq           = Right leq
        m Geq           = Right geq
        m Less          = Right less
        m Greater       = Right greater
        m Membership    = Right membership
        m Union         = Right set_union
        m Overload      = Right overload
        m DomSubt       = Right domsubt
        m DomRest       = Right domrest
        m MkFunction    = Right mk_fun
        m TotalFunction = Right total_fun
        m And           = Right conj
        m Or            = Right disj
        m Implies       = Right implies
        m Follows       = Right follows
        m Equiv         = Right equiv

