module Test.QuickCheck.Regression where

import Test.QuickCheck

regression :: (Show a, Testable b) => (a -> b) -> [a] -> Property
regression f xs = conjoin $ zipWith counterexample tags $ map f xs
    where
        tags = [ "counterexample " ++ show (i :: Int) ++ "\n" ++ show x | (i,x) <- zip [0..] xs ]

