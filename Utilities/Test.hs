{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Utilities.Test where

    -- Modules
import Logic.Operator
import Logic.OldOperator

import Theories.Arithmetic
import Theories.Notation
import Theories.SetTheory
import Theories.FunctionTheory

import Utilities.Graph as G
        ( matrix_of_with, closure
        , m_closure_with, as_map
        , unions )
import Utilities.EditDistance
import qualified Utilities.GraphSpec as GSpec

    -- Libraries
import           Data.Array 
import           Data.Function
import           Data.List
import           Data.List.Ordered as OL
import qualified Data.Map as M
import           Data.Typeable

import Tests.UnitTest
import Test.QuickCheck

import Utilities.Format
import Utilities.Syntactic
import Utilities.Error

import System.IO.Unsafe

--as_map = id

test_case :: (String, IO Bool, Bool) 
test_case = ("Graphs and operator grammars", test, True)

test :: IO Bool
test = test_cases $
    [ Case "case 0 - complete domain of matrices" case0 result0
    --, Case "case 1 - operator grammar discrepancy" case1 result1
    , Case "case 2 - new ambiguities" case2 result2
    , Case "case 3 - transitive closures" case3 result3
    , Case "case 4 - transitive closures in linear time" case4 result4
    , Case "Formatting utilities" test' True
    , Case "case 5 - error monad" case5 result5
    , Case "case 6 - union of a list of {sorted} list" case6 result6
    , Case "case 7 - union of a list of {unsorted} list" case7 result7  
    , Case "case 8 - edit distance, random testing" case8 True
    , Case "case 9 - edit distance, regression test from random testing" case9 0
    ] ++ GSpec.test_cases

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

--result1 :: [((Operator,Operator),Assoc,Assoc)]
--result1 = sortBy (compare `on` fst3) $ zip3 (map xbin_to_bin xs) ys zs
--    where
--        (xs,ys,zs) = unzip3 $
--            [ ((And,Or),Ambiguous,LeftAssoc)
--            , ((And,TotalFunction),Ambiguous,RightAssoc)
--            , ((Apply,TotalFunction),Ambiguous,LeftAssoc)
--            , ((DomRest,DomRest),RightAssoc,LeftAssoc)
--            , ((DomRest,DomSubt),RightAssoc,LeftAssoc)
--            , ((DomRest,Geq),Ambiguous,LeftAssoc)
--            , ((DomRest,Greater),Ambiguous,LeftAssoc)
--            , ((DomRest,Leq),Ambiguous,LeftAssoc)
--            , ((DomRest,Less),Ambiguous,LeftAssoc)
--            , ((DomRest,Membership),Ambiguous,LeftAssoc)
--            , ((DomRest,SetDiff),Ambiguous,RightAssoc)
--            , ((DomRest,TotalFunction),Ambiguous,RightAssoc)
--            , ((DomRest,Union),Ambiguous,RightAssoc)
--            , ((DomSubt,DomRest),RightAssoc,LeftAssoc)
--            , ((DomSubt,DomSubt),RightAssoc,LeftAssoc)
--            , ((DomSubt,Geq),Ambiguous,LeftAssoc)
--            , ((DomSubt,Greater),Ambiguous,LeftAssoc)
--            , ((DomSubt,Leq),Ambiguous,LeftAssoc)
--            , ((DomSubt,Less),Ambiguous,LeftAssoc)
--            , ((DomSubt,Membership),Ambiguous,LeftAssoc)
--            , ((DomSubt,SetDiff),Ambiguous,RightAssoc)
--            , ((DomSubt,TotalFunction),Ambiguous,RightAssoc)
--            , ((DomSubt,Union),Ambiguous,RightAssoc)
--            , ((Equal,TotalFunction),Ambiguous,RightAssoc)
--            , ((Follows,TotalFunction),Ambiguous,RightAssoc)
--            , ((Geq,DomRest),Ambiguous,RightAssoc)
--            , ((Geq,DomSubt),Ambiguous,RightAssoc)
--            , ((Geq,Overload),Ambiguous,RightAssoc)
--            , ((Geq,SetDiff),Ambiguous,RightAssoc)
--            , ((Geq,TotalFunction),Ambiguous,RightAssoc)
--            , ((Geq,Union),Ambiguous,RightAssoc)
--            , ((Greater,DomRest),Ambiguous,RightAssoc)
--            , ((Greater,DomSubt),Ambiguous,RightAssoc)
--            , ((Greater,Overload),Ambiguous,RightAssoc)
--            , ((Greater,SetDiff),Ambiguous,RightAssoc)
--            , ((Greater,TotalFunction),Ambiguous,RightAssoc)
--            , ((Greater,Union),Ambiguous,RightAssoc)
--            , ((Equiv,TotalFunction),Ambiguous,RightAssoc)
--            , ((Implies,TotalFunction),Ambiguous,RightAssoc)
--            , ((Leq,DomRest),Ambiguous,RightAssoc)
--            , ((Leq,DomSubt),Ambiguous,RightAssoc)
--            , ((Leq,Overload),Ambiguous,RightAssoc)
--            , ((Leq,SetDiff),Ambiguous,RightAssoc)
--            , ((Leq,TotalFunction),Ambiguous,RightAssoc)
--            , ((Leq,Union),Ambiguous,RightAssoc)
--            , ((Less,DomRest),Ambiguous,RightAssoc)
--            , ((Less,DomSubt),Ambiguous,RightAssoc)
--            , ((Less,Overload),Ambiguous,RightAssoc)
--            , ((Less,SetDiff),Ambiguous,RightAssoc)
--            , ((Less,TotalFunction),Ambiguous,RightAssoc)
--            , ((Less,Union),Ambiguous,RightAssoc)
--            , ((Membership,DomRest),Ambiguous,RightAssoc)
--            , ((Membership,DomSubt),Ambiguous,RightAssoc)
--            , ((Membership,MkFunction),Ambiguous,RightAssoc)
--            , ((Membership,Mult),Ambiguous,RightAssoc)
--            , ((Membership,Overload),Ambiguous,RightAssoc)
--            , ((Membership,Plus),Ambiguous,RightAssoc)
--            , ((Membership,Power),Ambiguous,RightAssoc)
--            , ((Membership,TotalFunction),Ambiguous,RightAssoc)
--            , ((MkFunction,Membership),Ambiguous,LeftAssoc)
--            , ((MkFunction,SetDiff),Ambiguous,LeftAssoc)
--            , ((MkFunction,TotalFunction),Ambiguous,LeftAssoc)
--            , ((MkFunction,Union),Ambiguous,LeftAssoc)
--            , ((Mult,Membership),Ambiguous,LeftAssoc)
--            , ((Mult,SetDiff),Ambiguous,LeftAssoc)
--            , ((Mult,TotalFunction),Ambiguous,LeftAssoc)
--            , ((Mult,Union),Ambiguous,LeftAssoc)
--            , ((Or,And),Ambiguous,RightAssoc)
--            , ((Or,TotalFunction),Ambiguous,RightAssoc)
--            , ((Overload,Geq),Ambiguous,LeftAssoc)
--            , ((Overload,Greater),Ambiguous,LeftAssoc)
--            , ((Overload,Leq),Ambiguous,LeftAssoc)
--            , ((Overload,Less),Ambiguous,LeftAssoc)
--            , ((Overload,Membership),Ambiguous,LeftAssoc)
--            , ((Overload,SetDiff),Ambiguous,LeftAssoc)
--            , ((Overload,TotalFunction),Ambiguous,LeftAssoc)
--            , ((Overload,Union),Ambiguous,LeftAssoc)
--            , ((Plus,Membership),Ambiguous,LeftAssoc)
--            , ((Plus,SetDiff),Ambiguous,LeftAssoc)
--            , ((Plus,TotalFunction),Ambiguous,LeftAssoc)
--            , ((Plus,Union),Ambiguous,LeftAssoc)
--            , ((Power,Membership),Ambiguous,LeftAssoc)
--            , ((Power,SetDiff),Ambiguous,LeftAssoc)
--            , ((Power,TotalFunction),Ambiguous,LeftAssoc)
--            , ((Power,Union),Ambiguous,LeftAssoc)
--            , ((SetDiff,DomRest),Ambiguous,LeftAssoc)
--            , ((SetDiff,DomSubt),Ambiguous,LeftAssoc)
--            , ((SetDiff,Geq),Ambiguous,LeftAssoc)
--            , ((SetDiff,Greater),Ambiguous,LeftAssoc)
--            , ((SetDiff,Leq),Ambiguous,LeftAssoc)
--            , ((SetDiff,Less),Ambiguous,LeftAssoc)
--            , ((SetDiff,MkFunction),Ambiguous,RightAssoc)
--            , ((SetDiff,Mult),Ambiguous,RightAssoc)
--            , ((SetDiff,Overload),Ambiguous,RightAssoc)
--            , ((SetDiff,Plus),Ambiguous,RightAssoc)
--            , ((SetDiff,Power),Ambiguous,RightAssoc)
--            , ((SetDiff,TotalFunction),Ambiguous,LeftAssoc)
--            , ((SetDiff,Union),Ambiguous,RightAssoc)
--            , ((TotalFunction,And),Ambiguous,LeftAssoc)
--            , ((TotalFunction,Apply),Ambiguous,RightAssoc)
--            , ((TotalFunction,DomRest),Ambiguous,LeftAssoc)
--            , ((TotalFunction,DomSubt),Ambiguous,LeftAssoc)
--            , ((TotalFunction,Equal),Ambiguous,LeftAssoc)
--            , ((TotalFunction,Follows),Ambiguous,LeftAssoc)
--            , ((TotalFunction,Geq),Ambiguous,LeftAssoc)
--            , ((TotalFunction,Greater),Ambiguous,LeftAssoc)
--            , ((TotalFunction,Equiv),Ambiguous,LeftAssoc)
--            , ((TotalFunction,Implies),Ambiguous,LeftAssoc)
--            , ((TotalFunction,Leq),Ambiguous,LeftAssoc)
--            , ((TotalFunction,Less),Ambiguous,LeftAssoc)
--            , ((TotalFunction,Membership),Ambiguous,LeftAssoc)
--            , ((TotalFunction,MkFunction),Ambiguous,RightAssoc)
--            , ((TotalFunction,Mult),Ambiguous,RightAssoc)
--            , ((TotalFunction,Or),Ambiguous,LeftAssoc)
--            , ((TotalFunction,Overload),Ambiguous,RightAssoc)
--            , ((TotalFunction,Plus),Ambiguous,RightAssoc)
--            , ((TotalFunction,Power),Ambiguous,RightAssoc)
--            , ((TotalFunction,SetDiff),Ambiguous,RightAssoc)
--            , ((TotalFunction,Union),Ambiguous,RightAssoc)
--            , ((Union,DomRest),Ambiguous,LeftAssoc)
--            , ((Union,DomSubt),Ambiguous,LeftAssoc)
--            , ((Union,Geq),Ambiguous,LeftAssoc)
--            , ((Union,Greater),Ambiguous,LeftAssoc)
--            , ((Union,Leq),Ambiguous,LeftAssoc)
--            , ((Union,Less),Ambiguous,LeftAssoc)
--            , ((Union,MkFunction),Ambiguous,RightAssoc)
--            , ((Union,Mult),Ambiguous,RightAssoc)
--            , ((Union,Overload),Ambiguous,RightAssoc)
--            , ((Union,Plus),Ambiguous,RightAssoc)
--            , ((Union,Power),Ambiguous,RightAssoc)
--            , ((Union,SetDiff),Ambiguous,LeftAssoc)
--            , ((Union,TotalFunction),Ambiguous,LeftAssoc)]

result2 :: [((Operator,Operator),Assoc,Assoc)]
result2 = sortBy (compare `on` fst3) $ zip3 (map xbin_to_bin xs) ys zs
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
        g0   = as_map $ struct notations
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
case4 = return $ sort (M.keys $ M.filter id $ as_map $ m_closure_with [0..5] xs)
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

data Tree a = Node a (Tree a) (Tree a) | Leaf
    deriving Show

test' :: IO Bool
test' = test_cases
        [ StringCase "test 0" 
                    (return $ format "hello {0} name is {1} and I'm {2} years old" "my" "Simon" 28) 
                    ("hello my name is Simon and I'm 28 years old")
        , StringCase "test 1"
                    (return $ format "this is a tree {0}, its second leaf is {1}" t4 t2)
                    (   "this is a tree Node \"Candide+Paul-Henri\" (Node \"Yves+Sylvie\" Leaf Leaf) "
                     ++ "(Node \"Danielle+Louis\" (Node \"Francois+Elsa\" Leaf Leaf) "
                     ++       "(Node \"Emilie+Vincent\" Leaf Leaf)), its second leaf is "
                     ++       "Node \"Francois+Elsa\" Leaf Leaf")
        ]
    where
        t0 = Node "Yves+Sylvie" Leaf Leaf
        t1 = Node "Danielle+Louis" t2 t3
        t2 = Node "Francois+Elsa" Leaf Leaf
        t3 = Node "Emilie+Vincent" Leaf Leaf
        t4 = Node "Candide+Paul-Henri" t0 t1

case5   :: IO (Either [Error] ((), [Error]))
result5 :: Either [Error] ((), [Error])

(case5,result5) = (test,result)
    where
        test = runErrorT $ do
            soft_error [e0]
            make_soft () $ do
                soft_error [e2]
                hard_error [e0]
            li <- hard_error [e1]
            soft_error [Error "error d" li]
        result = Left [e0,e2,e0,e1]
        li = LI "file.ext" 1 2
        e0 = Error "error a" li
        e1 = Error "error b" li
        e2 = Error "error c" li

data SortedList a = SL { unSL :: [a] }
    deriving Show

deriving instance Typeable Result
--    typeRep (Result 

instance (Ord a, Arbitrary a) => Arbitrary (SortedList a) where
    arbitrary = do
        xs <- arbitrary
        return $ SL $ sort xs

case6 :: IO Result
case6 = prop_valueOnSorted

result6 :: Result
result6 = Success 100 [] "+++ OK, passed 100 tests.\n"

case7 :: IO Result
case7 = prop_value

result7 :: Result
result7 = Success 100 [] "+++ OK, passed 100 tests.\n"

prop_valueOnSorted :: IO Result
prop_valueOnSorted = quickCheckResult $ \xs -> 
    let ys = map unSL xs :: [[Int]] in 
        unions ys == OL.nub (foldl OL.union [] ys)

prop_value :: IO Result
prop_value = quickCheckResult $ \xs -> 
    let ys = map id xs :: [[Int]] in 
        unions ys == OL.nub (foldl OL.union [] ys)

case8 :: IO Bool
case8 = run_test

case9 :: IO Int
case9 = return $ length $ filter not
            [ prop_a [26,27,0,-23,43] [0,43,-23]
            , prop_a [0,5,-2] [0,-2,5]
            --, prop_d 
            --    ( [Replace 4 70,Swap 5,Swap 1,Insert 6 (-11)]
            --    , [-29,14,43,42,-78,45,-46]) 
            --, prop_d 
            --    ( [Swap 4,Delete 15,Swap 14,Insert 5 24,Insert 5 14,Delete 11,Delete 0]
            --    , [7,4,1,1,5,8,5,1,8,4,7,2,4,4,5,1,4,10,5,2,2])
            ]