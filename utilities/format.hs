{-# LANGUAGE FlexibleInstances, IncoherentInstances #-}
module Utilities.Format 
    ( format, Formatter, fargs, test_case, test ) 
where

{-# LANGUAGE OverlappingInstances, FlexibleInstances, IncoherentInstances #-}

import Tests.UnitTest

format :: Formatter a => String -> a
format xs = fargs xs 0

class Formatter a where
    fargs :: String -> Int -> a

instance Formatter [Char] where
    fargs xs _ = xs

instance (Show a, Formatter b) => Formatter (a -> b) where
    fargs xs n x = fargs (subst xs n $ show x) (n+1)
--        case cast x of
--            Just x -> fargs (subst xs n x) (n+1)
--            Nothing -> fargs (subst xs n $ show x) (n+1)

instance Formatter a => Formatter ([Char] -> a) where
    fargs xs n x = fargs (subst xs n x) (n+1)

subst :: String -> Int -> String -> String
subst [] _ _ = []
subst xs n z
        | take m xs == fn   = z ++ subst (drop m xs) n z
        | otherwise         = take 1 xs ++ subst (drop 1 xs) n z
    where
        fn = "{" ++ show n ++ "}"
        m = length fn

data Tree a = Node a (Tree a) (Tree a) | Leaf
    deriving Show

test_case = ("Formatting utilities", test, True)

test = test_cases
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