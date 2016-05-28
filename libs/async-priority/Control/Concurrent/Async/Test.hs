module Control.Concurrent.Async.Test where 

import Test.UnitTest

import Control.Concurrent
import Control.Concurrent.Async.Priority
import Control.Exception.Lens
import Control.Lens

import Control.Monad
import Control.Monad.Loops
import Control.Monad.Trans

import Data.Either
import Data.Tuple

test_case :: TestCase
test_case = test_cases
        "Control.Concurrent.Async.Priority"
        [ aCase "Fail in some, pass in some" case0 result0 
        , aCase "High priority complete first" case1 result1
        ]

wait' :: (Priority,Int,Async s a) -> Sched s (Either (Priority,Int) (Priority,a))
wait' (p,i,task) = trying id (wait task) & mapped %~ (_Left .~ (p,i)) . (_Right %~ (p,))

case0 :: IO [Either (Priority,Int) (Priority,Int)]
case0 = do
    withScheduler 2 $ do
        let task n = threadDelay 100000 >> return n
        xs <- sequence [ fmap (p,i,) $ async p $ task i | i <- [1..10], p <- [ High, Low ] ]
        mapM_ (cancel.view _3) $ take 10 xs
        mapM wait' xs

result0 :: [Either (Priority,Int) (Priority,Int)]
result0 = [ Left (p,i)  | i <- [1..5], p <- [ High, Low ]] ++ 
          [ Right (p,i) | i <- [6..10], p <- [ High, Low ]]

waitForOne :: [Async s a] -> SchedSTM s ([a],[Async s a])
waitForOne [] = return ([],[])
waitForOne xs = do
    ys <- partitionEithers <$> mapM (unfail' waitSTM) xs
    guard (not $ null $ snd ys)
    return $ swap ys

waitInOrder :: MonadIO m 
            => [Async s a] -> SchedT s m [a]
waitInOrder xs = concat <$> unfoldrM f xs
    where
        f [] = return Nothing
        f xs = Just <$> atomically' (waitForOne xs)

case1 :: IO [Int]
case1 = do
    withScheduler 2 $ do
        let task n = threadDelay 100000 >> return n
        xs <- sequence [ async p $ task i 
                | (i,p) <- zip [1..20] (cycle [High,Low]) ]
        waitInOrder xs

result1 :: [Int]
result1 = [1,3..20] ++ [2,4..20]