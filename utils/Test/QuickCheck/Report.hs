module Test.QuickCheck.Report where

import Control.Monad

import Data.IORef
import Data.Map as M

import Test.QuickCheck

import Text.Printf

isSuccess :: Result -> Bool
isSuccess (Success {  }) = True
isSuccess _ = False

test_report :: Testable a
            => ((a -> IO Result) -> IO b) -> IO Bool
test_report tests = do 
    success <- newIORef (0 :: Int)
    total   <- newIORef (0 :: Int)
    let inc r = do
            when (isSuccess r) 
                $ modifyIORef success (+1)
            modifyIORef total (+1)
            return r
    (tests $ (>>= inc) . quickCheckWithResult stdArgs {chatty = False})
    x <- readIORef success
    y <- readIORef total
    printf "success: %d / %d\n[ %s ]\n" 
        x y
        (if x == y then "passed" else "failed")
    return $ x == y

instance (Ord k,Arbitrary k,Arbitrary a) => Arbitrary (Map k a) where
    arbitrary = M.fromList <$> arbitrary
