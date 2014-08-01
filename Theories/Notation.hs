module Theories.Notation where

    -- Modules
import Logic.Operator
import Logic.OldOperator

import Theories.Arithmetic
import Theories.FunctionTheory
import Theories.SetTheory

    -- Libraries
import qualified Data.Array as A
import           Data.List as L ( map )
import           Data.Map as M hiding ( foldl )
import           Data.IORef

import System.IO.Unsafe

import qualified Utilities.Graph as G ( (!) )

notations :: Notation
notations = flip precede logic $ foldl combine empty_notation
    [ functions
    , arith
    , function_notation
    , set_notation ] 

assoc :: BinOperator -> BinOperator -> Assoc
assoc x y = unsafePerformIO $ do
    r <- readIORef assoc_table'
    return $ r G.! (Right x,Right y)

assoc_table' :: IORef (Matrix Operator Assoc)
assoc_table' = unsafePerformIO $ newIORef (struct notations)

binds :: UnaryOperator -> BinOperator -> Assoc
binds x y = unsafePerformIO $ do
    r <- readIORef assoc_table' 
    return $ r G.! (Left x,Right y)

assoc0 :: Map (Operator, Operator) Assoc
assoc0 = fromList (zip (L.map xbin_to_bin xs) $ L.map (pairs M.!) xs)
    where
        rs    = double bin_op_range
        xs    = A.range rs

xbin_to_bin :: (XBinOperator,XBinOperator) -> (Operator,Operator)
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

double :: (a,b) -> ((a,a),(b,b))
double (x,y) = ((x,x),(y,y))
