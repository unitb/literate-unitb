module Data.String.Brackets where

    -- Modules
import Control.Monad.State

import Test.QuickCheck
import Test.QuickCheck.Report

brackets :: String -> (Int,Int)
brackets ln = execState 
        (forM_ ln $ \c -> do
            (cl,op) <- get
            if c == '(' then
                put (cl,op+1)
            else if c == ')' then
                if op == 0 
                    then put (cl+1,op)
                    else put (cl,op-1)
            else return ()
        ) (0,0)

combine :: (Int,Int) -> (Int,Int) -> (Int,Int)
combine (o0,c0) (o1,c1) 
    | c0 <= o1  = (o0 + o1 - c0, c1)
    | otherwise = (o0, c1 + c0 - o1)

groupBrack :: [String] -> [String]
groupBrack [] = []
groupBrack [x] = [x]
groupBrack (x0:x1:xs)
        | op == 0    = x0 : groupBrack (x1:xs)
        | otherwise = groupBrack $ (x0 ++ "\n" ++ x1) : xs
    where
        (_,op) = brackets x0

prop_brackets :: BrackString -> BrackString -> Bool
prop_brackets (BrackString xs) (BrackString ys) = combine (brackets xs) (brackets ys) == brackets (xs ++ ys)

prop_open_brack :: Bool
prop_open_brack = brackets ")" == (1,0)

prop_close_brack :: Bool
prop_close_brack = brackets "(" == (0,1)

prop_open_close :: Bool
prop_open_close = brackets ")(" == (1,1)

prop_close_open :: Bool
prop_close_open = brackets "()" == (0,0)

prop_close_close :: Bool
prop_close_close = brackets "))" == (2,0)

prop_open_open :: Bool
prop_open_open = brackets "((" == (0,2)

data BrackString = BrackString String

instance Show BrackString where
    show (BrackString xs) = show xs

instance Arbitrary BrackString where
    arbitrary = do
        liftM BrackString $ listOf $ elements "(x)"

return []

runSpec :: (PropName -> Property -> IO (a, Result))
        -> IO ([a], Bool)
runSpec = $forAllProperties'
