module Utilities.EditDistance where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Control.Precondition

import Data.Array as A hiding ((!))
import Data.List as L

import Test.QuickCheck

dist :: Eq a => [a] -> [a] -> Int
dist xs ys = 
        --ar A.! (m-1, n-1)
        ar ! (m-1, n-1)
    where
        m = length xs
        n = length ys
        f (-1,j) = j+1
        f (i,-1) = i+1
        f (i,j)  = minimum $
                        [  (1 + ar ! (i,j-1))
                        ,  (1 + ar ! (i-1,j))
                        ,  (cost + ar ! (i-1,j-1)) ]
                        ++ swap
          where
            cost 
              | xs ! i == ys ! j  = 0
              | otherwise         = 1
            swap 
              |    0 < i && 0 < j  
                &&     (xs ! (i-1), xs ! i) 
                    == (ys ! j    , ys ! (j-1)) 
                = [ar ! (i-2,j-2) + cost]
              | otherwise       = []
        --bnds = ( ( -1, -1)
        --       , (m-1,n-1))
        --ar = A.listArray bnds (map f $ A.range bnds) 
        bnds = ( ( -1 , -1)
               , (m-1 ,n-1))
        ar = A.listArray bnds 
                         (map f $ A.range bnds)

diff :: Eq a => [a] -> [a] -> [Change a]
diff xs ys = 
        --ar A.! (m-1, n-1)
        ar ! (m-1, n-1)
    where
        m = length xs
        n = length ys
        f (-1,j) = map (uncurry Insert) $ zip [0..j] ys
        f (i,-1) = reverse $ map Delete [0..i]
        f (i,j)  = min_ $  swap ++ 
                           [ Insert (i+1) (ys ! j) : ar ! (i,j-1)
                           , Delete i : (ar ! (i-1,j))
                           , cost ++ ar ! (i-1,j-1) ]
          where
            cost 
              | xs ! i == ys ! j  = []
              | otherwise           = [Replace i (ys ! j)]
            swap 
              |    1 <= i && 1 <= j  
                &&     (xs ! (i-1), xs ! i) 
                    == (ys ! j    , ys ! (j-1)) 
                = [[Swap (i-1)] ++ ar ! (i-2,j-2)]
              | otherwise       = []
        min_ (x0:x1:xs) = x0 `_min_` min_ (x1:xs)
        min_ [x0]       = x0
        min_ []         = assertFalse' "diff"
        _min_ xs ys
            | length xs <= length ys = xs
            | otherwise              = ys
        --bnds = ( ( -1, -1)
        --       , (m-1,n-1))
        --ar = A.listArray bnds (map f $ A.range bnds) 
        bnds = ( ( -1, -1)
               , (m-1,n-1) )
        ar = A.listArray bnds 
                         (map f (A.range bnds))

instance (Enum a, Arbitrary a) => Arbitrary ([Change a], [a]) where
    arbitrary = do
            xs <- map toEnum `liftM` listOf (choose (1,10))
            --xs <- arbitrary
            n  <- arbitrary
            ys <- flip evalStateT xs $ replicateM n $ do
                    xs <- get
                    k  <- lift $ oneof
                        [ do 
                            i <- choose (0,length xs)
                            x <- arbitrary
                            return $ Insert i x
                        , do 
                            i <- choose (0,length xs-1)
                            return $ Delete i
                        , do 
                            i <- choose (0,length xs-1)
                            x <- arbitrary
                            return $ Replace i x
                        , do
                            i <- choose (0,length xs-2)
                            return $ Swap i
                        ]
                    put $ effect k xs
                    return k
            return (ys,xs)

data Change a = 
        Insert Int a 
        | Delete Int 
        | Replace Int a
        | Swap Int
    deriving Show

effect :: Change a -> [a] -> [a]
effect (Insert i x) xs  = take i xs ++ [x] ++ drop i xs
effect (Delete i) xs    = take i xs ++ drop (i+1) xs
effect (Replace i x) xs = take i xs ++ [x] ++ drop (i+1) xs
effect (Swap i) xs      = take i xs ++ ys ++ drop (i+2) xs 
    where
        ys = reverse $ take 2 $ drop i xs

effects :: Eq a => [Change a] -> [a] -> [a]
effects ks xs = L.foldl (flip effect) xs ks 

-- prop_d :: Eq a => ([Change a],[a]) -> Bool
-- prop_d (ks,xs) = dist xs (effects ks xs) <= length ks

prop_c :: Eq a => [Small a] -> [Small a] -> Bool
prop_c xs' ys' = abs (length xs - length ys) <= dist xs ys
    where
        xs = map getSmall xs'
        ys = map getSmall ys'

prop_b :: Eq a => [Small a] -> [Small a] -> Bool
prop_b xs' ys' = length (diff xs ys) == dist xs ys
    where
        xs = map getSmall xs'
        ys = map getSmall ys'

prop_a :: Eq a => [Small a] -> [Small a] -> Bool
prop_a xs' ys' = effects (diff xs ys) xs == ys
    where
        xs = map getSmall xs'
        ys = map getSmall ys'

prop_e :: Eq a => [Small a] -> [Small a] -> Bool
prop_e xs' ys' = dist xs ys == dist ys xs
    where
        xs = map getSmall xs'
        ys = map getSmall ys'

prop_f :: Eq a => [Small a] -> [Small a] -> Bool
prop_f xs' ys' = (dist xs ys == 0) == (xs == ys)
    where
        xs = map getSmall xs'
        ys = map getSmall ys'

prop_g :: Eq a => [Small a] -> [Small a] -> [Small a] -> Bool
prop_g xs' ys' zs' = dist xs zs <= dist xs ys + dist ys zs
    where
        xs = map getSmall xs'
        ys = map getSmall ys'
        zs = map getSmall zs'

return []
run_test :: IO Bool
run_test = $forAllProperties (quickCheckWithResult stdArgs { chatty = False })
