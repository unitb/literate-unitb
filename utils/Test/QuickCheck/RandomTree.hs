{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE UndecidableInstances   #-}

module Test.QuickCheck.RandomTree where

import Control.Monad
import Control.Monad.Fix
import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Reader

import Data.List

import Text.Printf

import Test.QuickCheck hiding (sized)
import qualified Test.QuickCheck as QC
import Test.QuickCheck.Report

import Utilities.Partial

data Tree a = Tree a [Tree a]
    deriving Eq

type Rec a = RecT Gen a

newtype RecT m a = RecT { runRecT :: ReaderT Int (MaybeT m) a }

instance Functor m => Functor (RecT m) where
    fmap f (RecT m) = RecT $ fmap f m

instance (Functor m, Monad m) => Applicative (RecT m) where
    (<*>)  = ap
    pure = return

instance Monad m => Monad (RecT m) where
    RecT m >>= f = RecT $ m >>= runRecT . f
    return = RecT . return
    fail = RecT . fail

instance MonadTrans RecT where
    lift m = RecT $ lift $ lift m

class Monad m => MonadGen m where 
    liftGen :: Gen a -> m a
    sized :: (Int -> m a) -> m a

instance MonadGen Gen where
    liftGen m = m
    sized = QC.sized

instance MonadGen m => MonadGen (ReaderT a m) where
    liftGen m = lift $ liftGen m
    sized f   = ReaderT $ \r -> sized $ \n -> runReaderT (f n) r

instance MonadGen m => MonadGen (MaybeT m) where
    liftGen m = lift $ liftGen m
    sized f   = MaybeT $ sized $ \n -> runMaybeT (f n)

instance MonadGen m => MonadGen (RecT m) where
    liftGen m = lift $ liftGen m
    sized f   = RecT $ sized $ \n -> runRecT (f n)

elements :: MonadGen m => [a] -> m a
elements = liftGen . QC.elements

-- recurse :: forall a b. TupleOf b a => Rec a -> Rec b
-- recurse cmd = do
--     n <- RecT ask
--     let m = tLength (error "nuts" :: b)
--     unless (m <= n) (fail "insufficient budget")
--     bs <- lift $ putInBins (n - m) m
--     flip evalStateT bs $ forAllM $ do
--         x <- gets head
--         modify tail
--         lift $ RecT $ local (const x) (runRecT cmd)

recForM :: MonadGen m => [a] -> (a -> RecT m b) -> RecT m [b]
recForM xs f = do
    let k = length xs
    n  <- RecT ask 
    unless (k <= n) (fail "insufficient budget")
    -- k  <- lift $ choose (p, n `min` q)
    bs <- liftGen $ putInBins (n - k) k
    let cmd b x = RecT $ local (const b) (runRecT (f x))
    zipWithM cmd bs xs
    -- forM bs $ \b -> do
    --     RecT $ local (const b) (runRecT cmd)

recListFrom :: Int -> Rec a -> Rec [a]
recListFrom m cmd = do
    n <- RecT ask
    recListFromTo m n cmd

recListFromTo :: Int -> Int -> Rec a -> Rec [a]
recListFromTo p q cmd = do
    n  <- RecT ask 
    unless (p <= n) (fail "insufficient budget")
    k  <- lift $ choose (p, n `min` q)
    bs <- lift $ putInBins (n - k) k
    forM bs $ \b -> do
        RecT $ local (const b) (runRecT cmd)

try :: Monad m => RecT m a -> RecT m (Maybe a)
try cmd = RecT $ ReaderT $ \n -> MaybeT $ do
    liftM Just $ runMaybeT $ runReaderT (runRecT cmd) n

consume :: Monad m => RecT m a -> RecT m a
consume cmd = do
    n <- RecT ask
    when (n == 0) (fail "")
    RecT $ local (-1+) (runRecT cmd)

choice :: MonadGen m => [RecT m a] -> RecT m a
choice [] = fail ""
choice xs = do
        i <- liftGen $ choose (0,length xs-1)
        x <- try $ xs ! i
        maybe (choice $ remove i xs) return x
    where
        remove i xs = take i xs ++ drop (i+1) xs

runRec :: MonadGen m => RecT m a -> m (Maybe a)
runRec cmd = sized $ \n -> do
    x <- runMaybeT $ runReaderT (runRecT cmd) n -- (n^ (2 :: Int))
    return x

data MyTree = MyLeaf | TwoSubtrees MyTree MyTree | SomeSubtress [MyTree]
    deriving Show

-- tree :: Gen MyTree
-- tree = fromJust `liftM` runRec f
--     where
--         f = choice 
--             [ return MyLeaf
--             , do
--                 t0 :+: t1 :+: () <- recurse f
--                 return $ TwoSubtrees t0 t1
--             , do 
--                 ts <- recListFromTo 3 7 f
--                 return $ SomeSubtress ts
--             ] 

-- class Tuple a => TupleOf a b where
--     forAllM :: Monad m => m b -> m a

-- instance TupleOf () a where
--     forAllM _ = return ()

-- instance TupleOf as a => TupleOf (a :+: as) a where
--     forAllM cmd = do
--         x  <- cmd
--         xs <- forAllM cmd
--         return (x :+: xs)

instance Show a => Show (Tree a) where
    show (Tree x []) = show x
    show (Tree x ys) = printf "(%s %s)" first rest
        where
            first = show x
            rest = intercalate margin $ concatMap (lines . show) ys
            margin = '\n' : replicate (length first + 2) ' '

putInBins :: Int       -- number of objects
          -> Int       -- number of bins
          -> Gen [Int] -- return the number of objects in each bin
putInBins n bins = do
    xs <- replicateM n $ choose (0,bins-1)
    return $ map ((+(-1)).length) $ group $ sort $ xs ++ [0..bins-1]

prop_bin_length :: NonNegative Int -> Positive Int -> Property
prop_bin_length (NonNegative n) (Positive bins) = 
        forAll (putInBins n bins) $ \xs -> length xs == bins

prop_bin_sum :: NonNegative Int -> Positive Int -> Property
prop_bin_sum (NonNegative n) (Positive bins) = 
        forAll (putInBins n bins) $ \xs -> sum xs == n

prop_rand_tree_size :: Property
prop_rand_tree_size = forAll gen $ \(t,sz) -> size t <= sz ^ (2 :: Int)
    -- where

prop_subtree_size :: NonNegative Int 
                  -> Positive Int 
                  -> Property
prop_subtree_size (NonNegative n) (Positive sz) = 
    n < sz ==> 
    forAll (subtree_size n sz) $ 
        \ts -> sum ts + 1 <= sz

gen :: Gen (Tree Int, Int)
gen = sized $ \sz -> do
    t <- arbitrary 
    return (t,sz+1)

size :: Tree a -> Int
size (Tree _ xs) = 1 + sum (map size xs)

subtree_size :: Int -> Int -> Gen [Int]
subtree_size n sz = do
    bins <- if n == 0 
        then return []
        else putInBins (sz - n - 1) n
    return $ map (1+) bins

make_node :: Int -> Gen (Int,Int)
make_node sz = do
    frequency $
        [ (1,return (0,0)) ] ++
        [ (5,return (1,5)) | (5 < sz) ]

make_struct :: Int -> [RecStruct] -> RecStruct
make_struct 0 [] = Leaf
make_struct 1 [a,b,c,d,e] = Node a b c d e
make_struct _ _ = error "make_struct: invalid tree shape"

tree_of :: Num a => RecStruct -> Tree a
tree_of Leaf = Tree 0 []
tree_of (Node a b c d e) = Tree 1 $ map tree_of [a,b,c,d,e]

prop_tree_shape :: Property
prop_tree_shape = forAll (tree_from make_node) $ 
        \t -> all p $ subtrees t
    where
        p t =  (root t == 0 && degree t == 0) 
            || (root t == 1 && degree t == 5)

subtrees :: Tree t -> [Tree t]
subtrees t@(Tree _ ts) = concatMap subtrees ts ++ [t]

degree :: Tree t -> Int
degree (Tree _ ts) = length ts

root :: Tree t -> t
root (Tree x _) = x

type NodeGen a b = (b -> Int -> Gen (a, [b]))

data RecStruct = Leaf | Node RecStruct RecStruct RecStruct RecStruct RecStruct

recursive_struct' :: NodeGen a b -> (a -> [c] -> c) -> b -> Gen c
recursive_struct' node tree x =
    tree_from' node x
    >>= fix (\rec (Tree y ts) -> do
            ys <- mapM rec ts
            return (tree y ys)
        )

recursive_struct :: (Int -> Gen (a, Int)) -> (a -> [c] -> c) -> Gen c
recursive_struct node tree = recursive_struct' (const $ (>>= f) . node) tree ()
    where
        f (x,n) = return (x,replicate n ())

tree_from' :: NodeGen a b -> b -> Gen (Tree a)
tree_from' node x = sized $ \sz -> 
    tree_from_aux node x $ sz ^ (2 :: Int) + 1

tree_from :: (Int -> Gen (a, Int)) -> Gen (Tree a)
tree_from node = tree_from' (const $ (>>= f) . node) ()
    where
        f (x,n) = return (x,replicate n ())

tree_from_aux :: NodeGen a b -> b -> Int -> Gen (Tree a)
tree_from_aux node x sz = do
    unless (1 <= sz) $ error "tree_from: 1 <= sz"
    (val,n') <- node x sz
    let n = (sz-1) `take` n'
    bins  <- subtree_size (length n) sz
    ts    <- zipWithM (tree_from_aux node) n bins
    return $ Tree val ts

instance Arbitrary a => Arbitrary (Tree a) where
    arbitrary = sized $ \sz -> aux $ sz ^ (2 :: Int) + 1
        where
            aux sz = do
                n    <- choose (0,sz-1)
                bins <- subtree_size n sz
                ts   <- mapM aux bins
                x    <- arbitrary
                return $ Tree x ts

return []
run_tests :: IO Bool
run_tests = test_report ($forAllProperties)

main' :: IO ()
main' = do
    run_tests
    -- t <- last `liftM` sample' arbitrary
    -- print (t :: Tree Int)
    putStrLn "hello world"
    -- run_tests
    return ()
