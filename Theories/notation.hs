module Theories.Notation where

    -- Modules
import Logic.Const
import Logic.Operator

import Theories.FunctionTheory
import Theories.SetTheory

    -- Libraries
import qualified Data.Array as A
import           Data.List as L ( map )
import           Data.Map as M hiding ( foldl )
import           Data.IORef

import Utilities.Format

import System.IO.Unsafe


    -- Basic functions
apply = BinOperator "apply" "."     zapply
equal = BinOperator "equal" "="     mzeq

    -- logic
disj    = BinOperator "or" "\\lor"          mzor
conj    = BinOperator "and" "\\land"        mzand
implies = BinOperator "implies" "\\implies" mzimplies
follows = BinOperator "follows" "\\follows" (flip mzimplies)
equiv   = BinOperator "implies" "\\equiv"   mzeq
neg     = UnaryOperator "neg" "\\neg"       mznot

    -- set theory
set_union   = BinOperator "union" "\\bunion"        zunion
set_diff    = BinOperator "set-diff" "\\setminus"   zsetdiff
membership  = BinOperator "membership" "\\in"       zelem

    -- function theory
overload    = BinOperator "overload" "|"        zovl
mk_fun      = BinOperator "mk-fun" "\\tfun"     zmk_fun
total_fun   = BinOperator "total-fun" "\\tfun"  ztfun
domrest     = BinOperator "dom-rest" "\\domres" zdomrest
domsubt     = BinOperator "dom-subt" "\\domsub" zdomsubt

    -- arithmetic
power   = BinOperator "power" "^"       mzpow
mult    = BinOperator "mult" "\\cdot"   mztimes
plus    = BinOperator "plus" "+"        mzplus
less    = BinOperator "less" "<"        mzless
greater = BinOperator "greater" ">"     (flip mzless)
leq     = BinOperator "le" "\\le"       mzle
geq     = BinOperator "ge" "\\ge"       (flip mzle)

functions = Notation
    { new_ops     = L.map Right [equal,apply]
    , prec = [ L.map (L.map Right)
                     [ [apply]
                     , [equal] ]]
    , left_assoc  = [[apply]]
    , right_assoc = []
    , relations   = []
    , chaining    = [] }
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
set_notation = Notation
    { new_ops     = L.map Right [set_union,set_diff,membership]
    , prec = [ L.map (L.map Right)
                 [ [apply]
                 , [set_union,set_diff]
                 , [ equal
                   , membership] ]]
    , left_assoc  = [[set_union]]
    , right_assoc = []
    , relations   = []
    , chaining    = []  }
function_notation = Notation
    { new_ops     = L.map Right [overload,mk_fun,total_fun,domrest,domsubt]
    , prec = [ L.map (L.map Right) 
                 [ [apply]
                 , [mk_fun]
                 , [overload]
                 , [domrest,domsubt] 
                 , [ equal ] ]]
    , left_assoc  = [[overload]]
    , right_assoc = [[domrest,domsubt]]
    , relations   = []
    , chaining    = []  } 
arith = Notation
    { new_ops     = L.map Right [power,mult,plus,leq,geq,less,greater]
    , prec = [ L.map (L.map Right)
                     [ [apply]
                     , [power]
                     , [mult]
                     , [plus]
                     , [mk_fun]
                     , [ equal,leq
                       , less
                       , geq,greater]]]
    , left_assoc  = [[mult],[plus]]
    , right_assoc = []
    , relations   = [equal,leq,geq,less,greater]
    , chaining    = 
          [ ((leq,leq),leq)
          , ((leq,less),less)
          , ((less,leq),less)
          , ((less,less),less)
          , ((geq,geq),geq)
          , ((geq,greater),greater)
          , ((greater,geq),greater)
          , ((greater,greater),greater) ] }

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

