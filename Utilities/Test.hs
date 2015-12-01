{-# LANGUAGE StandaloneDeriving #-}
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
import Utilities.Lines as Lines
import qualified Utilities.GraphSpec as GSpec
import qualified Utilities.Permutation as Perm
import qualified Utilities.Relation as Rel
import qualified Utilities.Tuple.Generics as Tup

    -- Libraries
import Control.Lens

import           Data.Array 
import           Data.Function
import           Data.List
import           Data.List.Ordered as OL
import qualified Data.Map as M
import           Data.Typeable

import Tests.UnitTest
import Test.QuickCheck

import Utilities.Brackets
import Utilities.Format
import Utilities.Syntactic
import Utilities.Error

import System.IO.Unsafe

--as_map = id

test_case :: TestCase
test_case = test

test :: TestCase
test = test_cases "Graphs and operator grammars" $
    [ Case "case 0 - complete domain of matrices" case0 result0
    --, Case "case 1 - operator grammar discrepancy" case1 result1
    , Case "case 2 - new ambiguities" case2 result2
    , Case "case 3 - transitive closures" case3 result3
    , Case "case 4 - transitive closures in linear time" case4 result4
    , test'
    , Case "case 5 - error monad" case5 result5
    , Case "case 6 - union of a list of {sorted} list" (show <$> case6) (show result6)
    , Case "case 7 - union of a list of {unsorted} list" (show <$> case7) (show result7)  
    , Case "case 8 - edit distance, random testing" case8 True
    , Case "case 9 - edit distance, regression test from random testing" case9 0
    ] ++ GSpec.test_cases ++
    [ Case "case 11 - Relations, quickcheck" Rel.run_spec True
    , Case "case 12 - New graphs, quickcheck" Perm.run_tests True  
    , Case "case 13 - Sane line breaks, quickcheck" Lines.run_tests True
    , Case "test 14 - quickcheck brackets" runSpec True
    , Tup.test_case ]

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

result2 :: [((Operator,Operator),Assoc,Assoc)]
result2 = sortBy (compare `on` fst3) $ zip3 (map xbin_to_bin xs) ys zs
    where
        (xs,ys,zs) = unzip3
            [ ((And,Or),NoAssoc,LeftAssoc)
            , ((DomRest,DomRest),RightAssoc,LeftAssoc)
            , ((DomRest,DomSubt),RightAssoc,LeftAssoc)
            , ((DomRest,Membership),NoAssoc,LeftAssoc)
            , ((DomRest,SetDiff),NoAssoc,RightAssoc)
            , ((DomRest,Union),NoAssoc,RightAssoc)
            , ((DomSubt,DomRest),RightAssoc,LeftAssoc)
            , ((DomSubt,DomSubt),RightAssoc,LeftAssoc)
            , ((DomSubt,Membership),NoAssoc,LeftAssoc)
            , ((DomSubt,SetDiff),NoAssoc,RightAssoc)
            , ((DomSubt,Union),NoAssoc,RightAssoc)
            , ((Membership,DomRest),NoAssoc,RightAssoc)
            , ((Membership,DomSubt),NoAssoc,RightAssoc)
            , ((Membership,Mult),NoAssoc,RightAssoc)
            , ((Membership,Overload),NoAssoc,RightAssoc)
            , ((Membership,Plus),NoAssoc,RightAssoc)
            , ((Membership,Power),NoAssoc,RightAssoc)
            , ((Mult,Membership),NoAssoc,LeftAssoc)
            , ((Mult,SetDiff),NoAssoc,LeftAssoc)
            , ((Mult,Union),NoAssoc,LeftAssoc)
            , ((Or,And),NoAssoc,RightAssoc)
            , ((Overload,Membership),NoAssoc,LeftAssoc)
            , ((Overload,SetDiff),NoAssoc,LeftAssoc)
            , ((Overload,Union),NoAssoc,LeftAssoc)
            , ((Plus,Membership),NoAssoc,LeftAssoc)
            , ((Plus,SetDiff),NoAssoc,LeftAssoc)
            , ((Plus,Union),NoAssoc,LeftAssoc)
            , ((Power,Membership),NoAssoc,LeftAssoc)
            , ((Power,SetDiff),NoAssoc,LeftAssoc)
            , ((Power,Union),NoAssoc,LeftAssoc)
            , ((SetDiff,DomRest),NoAssoc,LeftAssoc)
            , ((SetDiff,DomSubt),NoAssoc,LeftAssoc)
            , ((SetDiff,Mult),NoAssoc,RightAssoc)
            , ((SetDiff,Overload),NoAssoc,RightAssoc)
            , ((SetDiff,Plus),NoAssoc,RightAssoc)
            , ((SetDiff,Power),NoAssoc,RightAssoc)
            , ((SetDiff,Union),NoAssoc,RightAssoc)
            , ((Union,DomRest),NoAssoc,LeftAssoc)
            , ((Union,DomSubt),NoAssoc,LeftAssoc)
            , ((Union,Mult),NoAssoc,RightAssoc)
            , ((Union,Overload),NoAssoc,RightAssoc)
            , ((Union,Plus),NoAssoc,RightAssoc)
            , ((Union,Power),NoAssoc,RightAssoc)
            , ((Union,SetDiff),NoAssoc,LeftAssoc)
            ]

fst3 :: (a,b,c) -> a
fst3 (x,_,_) = x
            
case1 :: IO [((Operator,Operator),Assoc,Assoc)]
case1 = return $ result
    where
        result = sortBy (compare `on` fst3) $ zip3 xs (map (g0 M.!) xs) (map (g1 M.!) xs)
        g0   = as_map $ notations^.struct
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
        f ((x,y),_,_) = null $ [x,y] `intersect` map Right [total_fun,mk_fun_op]
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

test' :: TestCase
test' = test_cases
        "Formatting utilities"
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
prop_valueOnSorted = quickCheckWithResult stdArgs { chatty = False }
    $ \xs -> 
        let ys = map unSL xs :: [[Int]] in 
            unions ys == OL.nub (foldl OL.union [] ys)

prop_value :: IO Result
prop_value = quickCheckWithResult stdArgs { chatty = False } $ \xs -> 
    let ys = map id xs :: [[Int]] in 
        unions ys == OL.nub (foldl OL.union [] ys)

case8 :: IO Bool
case8 = run_test

case9 :: IO Int
case9 = return $ length $ filter not
            [ prop_a [26,27,0,-23,43] [0,43,-23]
            , prop_a [0,5,-2] [0,-2,5]
            ]
