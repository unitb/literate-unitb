module Utilities.Test where

    -- Modules
import Logic.Operator
import Logic.OldOperator

import Theories.Arithmetic
import Theories.Notation
import Theories.SetTheory
import Theories.FunctionTheory

import Utilities.Graph

    -- Libraries
import Data.Array 
import Data.Function
import Data.List
import qualified Data.Map as M

import Tests.UnitTest

import System.IO.Unsafe

test_case :: (String, IO Bool, Bool) 
test_case = ("Graphs and operator grammars", test, True)

test :: IO Bool
test = test_cases  
    [ Case "case 0 - complete domain of matrices" case0 result0
    , Case "case 1 - operator grammar discrepancy" case1 result1
    , Case "case 2 - new ambiguities" case2 result2
    , Case "case 3 - transitive closures" case3 result3
    , Case "case 4 - transitive closures in linear time" case4 result4 ]

case0 :: IO (Array (Int,Int) Bool)
case0 = do
    let  rs         = range (1,4)
         xs         = [(0,5)]
         (m0,m1,ar) = matrix_of_with rs xs
         f (x,y)    = (m0 M.! x, m0 M.! y)
         g (i,j)    = (m1 ! i, m1 ! j) 
         (m,n)      = bounds ar
         r          = ixmap (g m, g n) f ar
    return r

result0 :: Array (Int,Int) Bool
result0 = array ((0,0),(5,5)) 
    [((0,0),False),((0,1),False),((0,2),False),((0,3),False),((0,4),False),((0,5),True)
    ,((1,0),False),((1,1),False),((1,2),False),((1,3),False),((1,4),False),((1,5),False)
    ,((2,0),False),((2,1),False),((2,2),False),((2,3),False),((2,4),False),((2,5),False)
    ,((3,0),False),((3,1),False),((3,2),False),((3,3),False),((3,4),False),((3,5),False)
    ,((4,0),False),((4,1),False),((4,2),False),((4,3),False),((4,4),False),((4,5),False)
    ,((5,0),False),((5,1),False),((5,2),False),((5,3),False),((5,4),False),((5,5),False)]

result1 :: [((Operator,Operator),Assoc,Assoc)]
result1 = sortBy (compare `on` fst3) $ zip3 (map xbin_to_bin xs) ys zs
    where
        (xs,ys,zs) = unzip3 $
            [ ((And,Or),Ambiguous,LeftAssoc)
            , ((And,TotalFunction),Ambiguous,RightAssoc)
            , ((Apply,TotalFunction),Ambiguous,LeftAssoc)
            , ((DomRest,DomRest),RightAssoc,LeftAssoc)
            , ((DomRest,DomSubt),RightAssoc,LeftAssoc)
            , ((DomRest,Geq),Ambiguous,LeftAssoc)
            , ((DomRest,Greater),Ambiguous,LeftAssoc)
            , ((DomRest,Leq),Ambiguous,LeftAssoc)
            , ((DomRest,Less),Ambiguous,LeftAssoc)
            , ((DomRest,Membership),Ambiguous,LeftAssoc)
            , ((DomRest,SetDiff),Ambiguous,RightAssoc)
            , ((DomRest,TotalFunction),Ambiguous,RightAssoc)
            , ((DomRest,Union),Ambiguous,RightAssoc)
            , ((DomSubt,DomRest),RightAssoc,LeftAssoc)
            , ((DomSubt,DomSubt),RightAssoc,LeftAssoc)
            , ((DomSubt,Geq),Ambiguous,LeftAssoc)
            , ((DomSubt,Greater),Ambiguous,LeftAssoc)
            , ((DomSubt,Leq),Ambiguous,LeftAssoc)
            , ((DomSubt,Less),Ambiguous,LeftAssoc)
            , ((DomSubt,Membership),Ambiguous,LeftAssoc)
            , ((DomSubt,SetDiff),Ambiguous,RightAssoc)
            , ((DomSubt,TotalFunction),Ambiguous,RightAssoc)
            , ((DomSubt,Union),Ambiguous,RightAssoc)
            , ((Equal,TotalFunction),Ambiguous,RightAssoc)
            , ((Follows,TotalFunction),Ambiguous,RightAssoc)
            , ((Geq,DomRest),Ambiguous,RightAssoc)
            , ((Geq,DomSubt),Ambiguous,RightAssoc)
            , ((Geq,Overload),Ambiguous,RightAssoc)
            , ((Geq,SetDiff),Ambiguous,RightAssoc)
            , ((Geq,TotalFunction),Ambiguous,RightAssoc)
            , ((Geq,Union),Ambiguous,RightAssoc)
            , ((Greater,DomRest),Ambiguous,RightAssoc)
            , ((Greater,DomSubt),Ambiguous,RightAssoc)
            , ((Greater,Overload),Ambiguous,RightAssoc)
            , ((Greater,SetDiff),Ambiguous,RightAssoc)
            , ((Greater,TotalFunction),Ambiguous,RightAssoc)
            , ((Greater,Union),Ambiguous,RightAssoc)
            , ((Implies,TotalFunction),Ambiguous,RightAssoc)
            , ((Implies,TotalFunction),Ambiguous,RightAssoc)
            , ((Leq,DomRest),Ambiguous,RightAssoc)
            , ((Leq,DomSubt),Ambiguous,RightAssoc)
            , ((Leq,Overload),Ambiguous,RightAssoc)
            , ((Leq,SetDiff),Ambiguous,RightAssoc)
            , ((Leq,TotalFunction),Ambiguous,RightAssoc)
            , ((Leq,Union),Ambiguous,RightAssoc)
            , ((Less,DomRest),Ambiguous,RightAssoc)
            , ((Less,DomSubt),Ambiguous,RightAssoc)
            , ((Less,Overload),Ambiguous,RightAssoc)
            , ((Less,SetDiff),Ambiguous,RightAssoc)
            , ((Less,TotalFunction),Ambiguous,RightAssoc)
            , ((Less,Union),Ambiguous,RightAssoc)
            , ((Membership,DomRest),Ambiguous,RightAssoc)
            , ((Membership,DomSubt),Ambiguous,RightAssoc)
            , ((Membership,MkFunction),Ambiguous,RightAssoc)
            , ((Membership,Mult),Ambiguous,RightAssoc)
            , ((Membership,Overload),Ambiguous,RightAssoc)
            , ((Membership,Plus),Ambiguous,RightAssoc)
            , ((Membership,Power),Ambiguous,RightAssoc)
            , ((Membership,TotalFunction),Ambiguous,RightAssoc)
            , ((MkFunction,Membership),Ambiguous,LeftAssoc)
            , ((MkFunction,SetDiff),Ambiguous,LeftAssoc)
            , ((MkFunction,TotalFunction),Ambiguous,LeftAssoc)
            , ((MkFunction,Union),Ambiguous,LeftAssoc)
            , ((Mult,Membership),Ambiguous,LeftAssoc)
            , ((Mult,SetDiff),Ambiguous,LeftAssoc)
            , ((Mult,TotalFunction),Ambiguous,LeftAssoc)
            , ((Mult,Union),Ambiguous,LeftAssoc)
            , ((Or,And),Ambiguous,RightAssoc)
            , ((Or,TotalFunction),Ambiguous,RightAssoc)
            , ((Overload,Geq),Ambiguous,LeftAssoc)
            , ((Overload,Greater),Ambiguous,LeftAssoc)
            , ((Overload,Leq),Ambiguous,LeftAssoc)
            , ((Overload,Less),Ambiguous,LeftAssoc)
            , ((Overload,Membership),Ambiguous,LeftAssoc)
            , ((Overload,SetDiff),Ambiguous,LeftAssoc)
            , ((Overload,TotalFunction),Ambiguous,LeftAssoc)
            , ((Overload,Union),Ambiguous,LeftAssoc)
            , ((Plus,Membership),Ambiguous,LeftAssoc)
            , ((Plus,SetDiff),Ambiguous,LeftAssoc)
            , ((Plus,TotalFunction),Ambiguous,LeftAssoc)
            , ((Plus,Union),Ambiguous,LeftAssoc)
            , ((Power,Membership),Ambiguous,LeftAssoc)
            , ((Power,SetDiff),Ambiguous,LeftAssoc)
            , ((Power,TotalFunction),Ambiguous,LeftAssoc)
            , ((Power,Union),Ambiguous,LeftAssoc)
            , ((SetDiff,DomRest),Ambiguous,LeftAssoc)
            , ((SetDiff,DomSubt),Ambiguous,LeftAssoc)
            , ((SetDiff,Geq),Ambiguous,LeftAssoc)
            , ((SetDiff,Greater),Ambiguous,LeftAssoc)
            , ((SetDiff,Leq),Ambiguous,LeftAssoc)
            , ((SetDiff,Less),Ambiguous,LeftAssoc)
            , ((SetDiff,MkFunction),Ambiguous,RightAssoc)
            , ((SetDiff,Mult),Ambiguous,RightAssoc)
            , ((SetDiff,Overload),Ambiguous,RightAssoc)
            , ((SetDiff,Plus),Ambiguous,RightAssoc)
            , ((SetDiff,Power),Ambiguous,RightAssoc)
            , ((SetDiff,TotalFunction),Ambiguous,LeftAssoc)
            , ((SetDiff,Union),Ambiguous,RightAssoc)
            , ((TotalFunction,And),Ambiguous,LeftAssoc)
            , ((TotalFunction,Apply),Ambiguous,RightAssoc)
            , ((TotalFunction,DomRest),Ambiguous,LeftAssoc)
            , ((TotalFunction,DomSubt),Ambiguous,LeftAssoc)
            , ((TotalFunction,Equal),Ambiguous,LeftAssoc)
            , ((TotalFunction,Follows),Ambiguous,LeftAssoc)
            , ((TotalFunction,Geq),Ambiguous,LeftAssoc)
            , ((TotalFunction,Greater),Ambiguous,LeftAssoc)
            , ((TotalFunction,Implies),Ambiguous,LeftAssoc)
            , ((TotalFunction,Implies),Ambiguous,LeftAssoc)
            , ((TotalFunction,Leq),Ambiguous,LeftAssoc)
            , ((TotalFunction,Less),Ambiguous,LeftAssoc)
            , ((TotalFunction,Membership),Ambiguous,LeftAssoc)
            , ((TotalFunction,MkFunction),Ambiguous,RightAssoc)
            , ((TotalFunction,Mult),Ambiguous,RightAssoc)
            , ((TotalFunction,Or),Ambiguous,LeftAssoc)
            , ((TotalFunction,Overload),Ambiguous,RightAssoc)
            , ((TotalFunction,Plus),Ambiguous,RightAssoc)
            , ((TotalFunction,Power),Ambiguous,RightAssoc)
            , ((TotalFunction,SetDiff),Ambiguous,RightAssoc)
            , ((TotalFunction,Union),Ambiguous,RightAssoc)
            , ((Union,DomRest),Ambiguous,LeftAssoc)
            , ((Union,DomSubt),Ambiguous,LeftAssoc)
            , ((Union,Geq),Ambiguous,LeftAssoc)
            , ((Union,Greater),Ambiguous,LeftAssoc)
            , ((Union,Leq),Ambiguous,LeftAssoc)
            , ((Union,Less),Ambiguous,LeftAssoc)
            , ((Union,MkFunction),Ambiguous,RightAssoc)
            , ((Union,Mult),Ambiguous,RightAssoc)
            , ((Union,Overload),Ambiguous,RightAssoc)
            , ((Union,Plus),Ambiguous,RightAssoc)
            , ((Union,Power),Ambiguous,RightAssoc)
            , ((Union,SetDiff),Ambiguous,LeftAssoc)
            , ((Union,TotalFunction),Ambiguous,LeftAssoc)]

result2 :: [((Operator,Operator),Assoc,Assoc)]
result2 = zip3 (map xbin_to_bin xs) ys zs
    where
        (xs,ys,zs) = unzip3
            [ ((And,Or),Ambiguous,LeftAssoc)
            , ((DomRest,DomRest),RightAssoc,LeftAssoc)
            , ((DomRest,DomSubt),RightAssoc,LeftAssoc)
            , ((DomRest,Membership),Ambiguous,LeftAssoc)
            , ((DomRest,SetDiff),Ambiguous,RightAssoc)
            , ((DomRest,Union),Ambiguous,RightAssoc)
            , ((DomSubt,DomRest),RightAssoc,LeftAssoc)
            , ((DomSubt,DomSubt),RightAssoc,LeftAssoc)
            , ((DomSubt,Membership),Ambiguous,LeftAssoc)
            , ((DomSubt,SetDiff),Ambiguous,RightAssoc)
            , ((DomSubt,Union),Ambiguous,RightAssoc)
            , ((Membership,DomRest),Ambiguous,RightAssoc)
            , ((Membership,DomSubt),Ambiguous,RightAssoc)
            , ((Membership,Mult),Ambiguous,RightAssoc)
            , ((Membership,Overload),Ambiguous,RightAssoc)
            , ((Membership,Plus),Ambiguous,RightAssoc)
            , ((Membership,Power),Ambiguous,RightAssoc)
            , ((Mult,Membership),Ambiguous,LeftAssoc)
            , ((Mult,SetDiff),Ambiguous,LeftAssoc)
            , ((Mult,Union),Ambiguous,LeftAssoc)
            , ((Or,And),Ambiguous,RightAssoc)
            , ((Overload,Membership),Ambiguous,LeftAssoc)
            , ((Overload,SetDiff),Ambiguous,LeftAssoc)
            , ((Overload,Union),Ambiguous,LeftAssoc)
            , ((Plus,Membership),Ambiguous,LeftAssoc)
            , ((Plus,SetDiff),Ambiguous,LeftAssoc)
            , ((Plus,Union),Ambiguous,LeftAssoc)
            , ((Power,Membership),Ambiguous,LeftAssoc)
            , ((Power,SetDiff),Ambiguous,LeftAssoc)
            , ((Power,Union),Ambiguous,LeftAssoc)
            , ((SetDiff,DomRest),Ambiguous,LeftAssoc)
            , ((SetDiff,DomSubt),Ambiguous,LeftAssoc)
            , ((SetDiff,Mult),Ambiguous,RightAssoc)
            , ((SetDiff,Overload),Ambiguous,RightAssoc)
            , ((SetDiff,Plus),Ambiguous,RightAssoc)
            , ((SetDiff,Power),Ambiguous,RightAssoc)
            , ((SetDiff,Union),Ambiguous,RightAssoc)
            , ((Union,DomRest),Ambiguous,LeftAssoc)
            , ((Union,DomSubt),Ambiguous,LeftAssoc)
            , ((Union,Mult),Ambiguous,RightAssoc)
            , ((Union,Overload),Ambiguous,RightAssoc)
            , ((Union,Plus),Ambiguous,RightAssoc)
            , ((Union,Power),Ambiguous,RightAssoc)
            , ((Union,SetDiff),Ambiguous,LeftAssoc)
            ]

fst3 :: (a,b,c) -> a
fst3 (x,_,_) = x
            
case1 :: IO [((Operator,Operator),Assoc,Assoc)]
case1 = do
--        mapM_ print $ new_ops notations
--        mapM_ print $ M.toList g1
--        print "checkpoint A"
        return $ result
    where
        result = sortBy (compare `on` fst3) $ zip3 xs (map (g0 M.!) xs) (map (g1 M.!) xs)
        g0   = assoc' notations
        g1   = assoc0
        rs   = M.keys assoc0
        eq x = g0 `lu` x /= g1 `lu` x
        xs   = filter eq rs
        lu x y = case M.lookup y x of
            Just z  -> z
            Nothing -> unsafePerformIO $ do
                print y
                return undefined

case2 :: IO [((Operator,Operator),Assoc,Assoc)]
case2 = do
        xs <- case1
        return $ filter h xs
    where
        f ((x,y),_,_) = null $ [x,y] `intersect` map Right [total_fun,mk_fun]
        g ((x,y),_,_) = not $ (x,y) `elem` combos
        h x = f x && g x
        combos = concat [ [(i,j),(j,i)] | i <- rel, j <- set ] 
        rel = map Right [ geq, leq, less, greater ]
        set = map Right [ set_union, domrest, domsubt, set_diff, membership, overload ]

case3 :: IO [(Int,Int)]
case3 = return $ sort (closure xs)
    where
        xs :: [(Int,Int)]
        xs = [ (0,1),(1,2),(2,3)
             , (1,4),(5,2) ]

result3 :: [(Int,Int)]
result3 = sort
    [ (0,1),(1,2),(2,3)
    , (1,3),(0,2),(0,3)
    , (0,4),(1,4),(5,2)
    , (5,3) ] 

case4 :: IO [(Int,Int)]
case4 = return $ sort (M.keys $ M.filter id $ m_closure_with [0..5] xs)
    where
        xs :: [(Int,Int)]
        xs = [ (0,1),(1,2),(2,3)
             , (1,4),(5,2) ]

result4 :: [(Int,Int)]
result4 = sort
    [ (0,1),(1,2),(2,3)
    , (1,3),(0,2),(0,3)
    , (0,4),(1,4),(5,2)
    , (5,3) ] 
