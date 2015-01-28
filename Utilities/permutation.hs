{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE StandaloneDeriving  #-}
module Utilities.Permutation 
    ( top_sort, closure, closure'
    , graph, graphWith, u_scc
    , GraphImp (..), run_tests 
    , main )
where

import Control.Loop
import Control.Monad
import Control.Monad.Fix
import Control.Monad.ST
import Control.Monad.State ( evalState )
import Control.Monad.State.Class -- (MonadState)

import Data.Array.IArray
import Data.Array.IO
import Data.Array.ST
import Data.Graph (SCC(..))
import Data.List
-- import Data.Ratio
import Data.STRef
import qualified Data.List.Ordered as OL
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Tuple as T

import System.Environment
import System.Random
import System.TimeIt

import Test.QuickCheck hiding (frequency,elements)
import qualified Test.QuickCheck as QC

import Text.Printf

class AllZero a where
    zeros :: a

instance AllZero () where
    zeros = ()

-- instance (AllZero xs, Num x) => AllZero (x :+: xs) where
--     zeros = 0 :+: zeros

-- allZero :: (IsTuple a, AllZero (TypeList a)) => a
-- allZero = fromTuple (zeros)

-- atRandom :: (MonadState StdGen m, Random a) => (a,a) -> m a
-- atRandom x = do
--     g <- get
--     let (r,g') = randomR x g
--     put g'
--     return r

-- permute :: [a] -> Rand [a]
-- permute xs = StateT $ Identity . permute_aux xs

-- permute_aux :: forall a. [a] -> StdGen -> ([a],StdGen)
-- permute_aux xs g = runST $ runStateT (do
--     let n = length xs
--     ar <- lift (newListArray (0,n-1) xs :: ST s (STArray s Int a))
--     forM [0..n-1] $ \i -> do
--         j <- atRandom (i,n-1)
--         lift $ swap i j ar >> readArray ar i
--     ) g

data Color = White | Grey | Black
    deriving (Eq)

closure :: forall v. Ord v => [v] -> [(v,v)] -> M.Map v [v]
closure vs es = closure' (graph vs es)

closure' :: forall v. Ord v => GraphImp v -> M.Map v [v]
closure' g = runST $ do
        ar <- newArray_ (V 0,V $ nn-1)
                :: ST s (STArray s Vertex (S.Set Vertex))
        forM_ top $ \xs -> do
            let ys  = S.fromList $ concatMap (i2e !) xs
            zs <- forM (S.toList $ ys S.\\ S.fromList xs) $ readArray ar
            let set = S.unions $ ys : zs
            forM_ xs $ \i -> writeArray ar i set
        liftM M.fromList $ forM [V 0..V $ nn-1] $ \v -> do
            vs <- readArray ar v
            let y  = i2v!v
                ys = map (i2v!) $ S.toList vs
            return (y,ys)
    where
        nn = vcount g
        i2v = int2v g
        i2e = int2e g
        top = reverse $ map component $ top_sort' g
 
component :: SCC v -> [v]
component (CyclicSCC vs) = vs
component (AcyclicSCC v) = [v]

top_sort :: forall v. Ord v => [v] -> [(v,v)] -> [SCC v]
top_sort vs es = map (fmap (i2v !)) $ top_sort' g
    where
        i2v = int2v g
        g   = graph vs es

    -- Possible optimization for dense graphs:
    -- store the eList array as an array of arrays
    -- allocating new arrays only when needed
    -- for n = |v|, we could allocate arrays of size n
    -- 
    -- Optional: when 2 (or other number) arrays are 
    -- completely unused, deallocate half.
top_sort' :: forall v. Ord v => GraphImp v -> [SCC Vertex]
top_sort' g = runST $ do
        -- res      <- newArray_ (0,n-1) 
        p       <- newPartition nn
                    :: ST s (Partition s Vertex)
        res     <- newSTRef []
                    :: ST s (STRef s [Vertex])
        path    <- newArray (0,nn-1) 
                    (error "undefined in path")
                    :: ST s (STArray s Int Vertex)
        -- edges   <- newArray (0,nn-1) 
        --             (error "undefined in edges")
        --             :: ST s (STArray s Int [Vertex])
        eStack  <- newArray (-1,nn-1) 0
                    :: ST s (STArray s Int Int)
        eList   <- newArray_ (0,mm-1) 
                    :: ST s (STArray s Int Vertex)
            -- next vertex
        rM      <- newSTRef $ V 0
            -- stack top
        rN      <- newSTRef 0
        visited <- newArray (V 0,V $ nn-1) White
                    :: ST s (STArray s Vertex Color)
        cycles  <- newArray (V 0,V $ nn-1) False
                    :: ST s (STArray s Vertex Bool)
        let top = do
                n <- readSTRef rN
                readArray path (n-1)
        let push i = do
                writeArray visited i Grey
                n  <- readSTRef rN
                writeArray path  n i
                -- writeArray edges n $ reverse (i2e ! i)
                k <- readArray eStack (n-1)
                let es = (i2e ! i)
                zipWithM (writeArray eList) [k..] es
                writeArray eStack n (k + length es)
                modifySTRef rN (+1)
        let pop = do
                t  <- top
                n  <- readSTRef rN
                r  <- root p t
                writeArray visited r Black
                when (n == 0) $ error "n == 0"
                -- writeArray edges (n-1) []
                modifySTRef rN (+ (-1))
                modifySTRef res (r:)       
        -- let check_var str cmd = do
        --         let var = do
        --             r <- length `liftM` readSTRef res
        --             V m <- readSTRef rM
        --             n <- readSTRef rN
        --             xs <- forM [0..nn-1] $ readArray visited . V
        --             -- ys <- forM [0..n-1] $ readArray edges
        --             let w = length $ filter (== White) xs
        --                 e = length $ concat ys
        --             return (nn - r, w, n, e, nn - m)
        --         v <- var
        --         cmd
        --         v' <- var
        --         unless (v' < v)
        --             $ error $ printf "variant does not decrease (%s)" (str :: String)
        --         unless (allZero <= v')
        --             $ error $ printf "variant goes below zero (%s)" (str)
        -- let check_inv str = do
        --         n <- readSTRef rN
        --         xs <- liftM concat $ forM [0..n-1] $ \i -> do
        --             k   <- readArray eStack (i-1)
        --             k'  <- readArray eStack i
        --             es  <- readArray edges  i
        --             es' <- forM [k..k'-1] $ readArray eList
        --             if reverse es == es' 
        --                 then return []
        --                 else return [(i,es,es')]
        --         unless (null xs) $ error $ str ++ ": invalid stacks: " 
        --             ++ intercalate ", " (map show xs)
        fix $ \rec -> do
            n  <- readSTRef rN
            m  <- readSTRef rM
            if n == 0 && m == V nn then 
                return ()
            else if n == 0 then do
                r <- root p m
                c <- readArray visited r
                when (c == White) 
                    $ push m
                writeSTRef rM $ succ m
            else do
                v  <- readArray path  (n-1)
                k  <- readArray eStack (n-2)
                k' <- readArray eStack (n-1)
                -- es <- readArray edges (n-1)
                if k == k' then pop
                else do
                    x  <- readArray eList (k'-1)
                    r <- root p x 
                    c <- readArray visited r
                    case c of
                      White -> do
                        writeArray eStack (n-1) (k' - 1)
                        -- writeArray edges (n-1) (tail es)
                        push x
                      Grey  -> do
                        r' <- root p v
                        when (r /= r') $ do
                                -- merge
                            y <- readArray path (n-2)
                            merge p y v
                            writeArray path (n-1) (V $ -1)
                            -- es' <- readArray edges (n-2)
                            -- writeArray edges (n-2) (es++es')
                            writeArray eStack (n-2) k'
                            writeArray eStack (n-1) 0
                            modifySTRef rN (+ (-1))
                            -- check_inv "D"
                        when (r == r') $ do
                            -- writeArray edges (n-1) (tail es)
                            writeArray eStack (n-1) (k'-1)
                            writeArray cycles r True
                            -- check_inv "C"
                      Black -> do
                        -- writeArray edges (n-1) (tail es)
                        writeArray eStack (n-1) (k'-1)
                        -- check_inv "B"
                -- es <- readArray edges (n-1)
                -- k  <- readArray eStack (n-2)
                -- k' <- readArray eStack (n-1)
                -- case es of
                --   [] -> do 
                --     pop
                --   x:xs -> do
                --     x' <- readArray eList (k'-1)
                --     r  <- root p x 
                --     c  <- readArray visited r
                --     case c of
                --       White -> do
                --         push x
                --         writeArray edges (n-1) xs
                --       Grey  -> do
                --         r' <- root p v
                --         when (r /= r') $ do
                --                 -- merge
                --             y <- readArray path (n-2)
                --             merge p y v
                --             writeArray path (n-1) (V $ -1)
                --             es' <- readArray edges (n-2)
                --             writeArray edges (n-2) (es++es')
                --             modifySTRef rN (+ (-1))
                --         when (r == r') $ do
                --             writeArray edges (n-1) xs
                --             writeArray eStack (n-1) (k'-1)
                --             writeArray cycles r True
                --       Black -> do
                --         writeArray edges (n-1) xs
                --         writeArray eStack (n-1) (k'-1)
            unless (m == V nn && n == 0) rec
        m  <- getSets p
        r  <- readSTRef res
        rs <- forM r $ readArray cycles 
        return $ zipWith (\r b -> if b 
                then CyclicSCC (m M.! r) 
                else AcyclicSCC (head $ m M.! r)
                ) r rs
    where
        nn  = vcount g
        mm  = ecount g
        i2e = int2e g

data GraphImp v = GraphImp 
    { vertices :: [v]
    , edges :: [(v,v)]
    , int2e :: Array Vertex [Vertex]
    , int2v :: Array Vertex v
    , v2int :: M.Map v Vertex
    , forward  :: M.Map v [v]
    , backward :: M.Map v [v]
    , rel     :: v -> v -> Bool
    , reli    :: Vertex -> Vertex -> Bool
    , vcount  :: Int
    , ecount  :: Int
    } 

deriving instance Show v => Show (SCC v)

graphWith :: forall v. Ord v => [v] -> (v -> v -> Bool) -> GraphImp v
graphWith vs f = g { rel = f, reli = f' }
    where
        g      = graph vs' es
        f' i j = f (int2v g ! i) (int2v g ! j)
        vs' = OL.nubSort vs
        es  = [ (u,v) | u <- vs', v <- vs', f u v ]

graph :: forall v. Ord v => [v] -> [(v,v)] -> GraphImp v
graph vs es = GraphImp vs' es i2e i2v v2i fwd bwd f f' nn mm
    where
        f' i j = j `S.member` (mi2e ! i)
        f  u v = f' (v2i M.! u) (v2i M.! v)
        mi2e = amap S.fromList i2e
        vs'  = OL.nubSort vs
        nn   = length vs'
        mm   = length es
        i2v :: Array Vertex v
        i2v = array (V 0,V $ nn-1) $ zip [V 0..] vs'
        i2e :: Array Vertex [Vertex]
        i2e = runSTArray $ do
                ar <- newArray (V 0,V $ nn-1) []
                forM_ es $ \(u,v) -> do
                    let i = v2i M.! u
                        j = v2i M.! v
                    js <- readArray ar i
                    writeArray ar i (j:js)
                return ar
        v2i = M.fromList $ zip vs' [V 0..]
        fwd = alist es
        bwd = alist $ map T.swap es
        alist xs = M.fromListWith (++) $
                [ (v,[]) | v <- vs' ] ++
                [ (u,[v]) | (u,v) <- xs ]



newtype Partition s v = Partition (STArray s v v)

newtype Vertex = V Int
    deriving (Eq, Ord, Ix, Enum, Show)



newPartition :: (Enum v, Ix v) => Int -> ST s (Partition s v)
newPartition n = Partition `liftM` newListArray (toEnum 0,toEnum $ n-1) [toEnum 0..]

root :: Ix v => Partition s v -> v -> ST s v
root part@(Partition ar) i = do
    p <- readArray ar i
    if p == i 
        then return i
        else do
            j <- root part p
            writeArray ar i j
            return j

merge :: Ix v => Partition s v -> v -> v -> ST s ()
merge part@(Partition ar) i j = do
        pI <- root part i
        pJ <- root part j
        if pI <= pJ
            then writeArray ar pJ pI
            else writeArray ar pI pJ

getSets :: forall s v. (Enum v, Ix v) => Partition s v -> ST s (M.Map v [v])
getSets part@(Partition ar) = do
            (_,n) <- getBounds ar
            res <- newArray (toEnum 0,n) []
                    :: ST s (STArray s v [v])
            ref <- newSTRef []
            forLoop (toEnum 0) (<= n) succ (void . root part)
            forLoop (toEnum 0) (<= n) succ $ \i -> do
                j <- readArray ar i
                xs <- readArray res j
                writeArray res j $ i:xs
                modifySTRef ref (j:)
            xs <- OL.nubSort `liftM` readSTRef ref
            ys <- forM xs (readArray res)
            return $ M.fromList $ zip xs ys


u_scc :: forall v. Ord v => [v] -> (v -> v -> Bool) -> [[v]]
u_scc xs e = runST $ do
        p <- newPartition n
        forLoop 0 (< n) (+1) $ \i ->
            forLoop (i+1) (< n) (+1) $ \j -> do
                if e (i2v ! i) (i2v ! j) 
                    then merge p i j
                    else return ()
        (map (map (i2v!)) . M.elems) `liftM` getSets p
    where
        n = length xs
        i2v :: Array Int v
        i2v = array (0,n-1) xs'
        xs' = zip [0..] xs

-- factorial :: (Integral n) => n -> n
-- factorial n = product [1..n]

choose_n :: forall a. Int -> [a] -> IO [a]
choose_n n xs = do
        let m = length xs
        unless (n <= m) $ fail "choose_n: n bigger than list size"
        ar <- newListArray (0,m-1) xs :: IO (IOArray Int a)
        forM [0..n-1] $ \i -> do
            j <- randomRIO (i,m-1)
            swap i j ar
            readArray ar i
        -- take n `liftM` getElems ar

swap :: (MArray a e m) 
     => Int -> Int -> a Int e -> m ()
swap i j ar = do
    x <- readArray ar i
    y <- readArray ar j
    writeArray ar i y
    writeArray ar j x

permIO :: [a] -> IO [a]
permIO xs = choose_n (length xs) xs

-- choose_n' :: Int -> [a] -> IO [a]
-- choose_n' n xs = do
--         let m = length xs
--         unless (n <= m) $ fail "choose_n: n "
--         (xs,_) <- foldM (\(rs,xs) i -> do
--             j <- randomRIO (0,m-i-1)
--             let x = xs !! j
--             return (x:rs,take i xs ++ drop (i+1) xs)
--             ) ([],xs) [0..n-1] 
--         return xs

-- collapse :: Ord a => Probabilistic a -> Probabilistic a
-- collapse (Prob m) = Prob $ M.toList $ M.fromListWith (+) m

-- perms :: Ord a => [a] -> Probabilistic [a]
-- perms xs = 
--         fix (\rec xs -> do
--             if null xs 
--             then return []
--             else collapse $ do
--                     (xs,y,zs) <- elements $ zip3 
--                         (inits xs) 
--                         xs 
--                         (drop 1 $ tails xs)
--                     rs <- rec (xs ++ zs)
--                     return $ y:rs
--             ) xs

-- elements :: [a] -> Probabilistic a
-- elements xs = oneOf $ map return xs

-- oneOf :: [Probabilistic a] -> Probabilistic a
-- oneOf xs = frequency $ zip (repeat 1) xs

-- frequency :: [(Int,Probabilistic a)] -> Probabilistic a
-- frequency xs = join $ Prob (filter p $ zip zs (map frac ys))
--     where
--         xs' = filter (\(n,_) -> 0 < n) xs
--         d = sum ys
--         frac n = n % d
--         ys = map (toInteger . fst) xs'
--         zs = map snd xs'
--         p (_,x) = 0 < x

-- instance Functor Cell where
--  func = 

-- newtype Probabilistic a = Prob { runProb :: [(a, Rational)] }
--     deriving Show

-- instance Functor Probabilistic where
--     fmap f (Prob m) = Prob $ mapKeys f m

-- instance Applicative Probabilistic where
--     f <*> m = ap f m
--     pure x  = return x

-- mapValues :: (b -> c) -> [(a,b)] -> [(a,c)]
-- mapValues f xs = zip ys (map f zs)
--     where
--         (ys,zs) = unzip xs

-- mapKeys :: (a -> c) -> [(a,b)] -> [(c,b)]
-- mapKeys f xs = zip (map f ys) zs
--     where
--         (ys,zs) = unzip xs

-- instance Monad Probabilistic where
--     Prob m >>= f = Prob $ concat [ mapValues (*y) (runProb $ f x) | (x,y) <- m ]
--     return x = Prob [(x,1)]

-- runProbabilistic :: Ord a => Probabilistic a -> [(Rational,a)]
-- runProbabilistic (Prob m) = zip ys xs
--     where
--         (xs,ys) = unzip $ M.toList $ M.fromList m

evalList :: [a] -> [a]
evalList xs = foldr seq xs xs

prop_evalList_is_identity :: (Eq a, Arbitrary a) => [a] -> Bool
prop_evalList_is_identity xs = xs == evalList xs

-- prop_permutations_eq_prob :: Property
-- prop_permutations_eq_prob = forAll (choose (0,7)) $ \n -> f n == g n
--     where
--         f n = sort $ let n_fact = factorial n in 
--                     [ (1%n_fact,x) | x <- permutations [1..n] ]
--         g n = sort $ runProbabilistic $ perms [1..n]

-- instance Arbitrary a => Arbitrary (Probabilistic a) where
--     arbitrary = do
--         xs <- suchThat arbitrary
--                 (\xs -> not $ null xs)
--         m' <- getNonNegative `liftM` arbitrary
--         let n = length xs ;
--             m = toInteger $ n + m'
--         ys <- map (\x -> (toInteger $ x+1) % m) `liftM` putInBins m' n
--         return $ Prob $ zip xs ys

-- prop_bind_preserves_invariant :: Probabilistic a -> Fun a (Probabilistic b) -> Bool
-- prop_bind_preserves_invariant m (Fun _ f) = prob_invariant (m >>= f)

-- prop_arb_prob_sat_invariant :: Probabilistic a -> Bool
-- prop_arb_prob_sat_invariant p = prob_invariant p

-- prob_invariant :: Probabilistic a -> Bool
-- prob_invariant (Prob xs) = sum (map snd xs) == 1 && all (> 0) (map snd xs) 

-- prop_frequency_sat_invariant :: NonEmptyList (Positive Int, Probabilistic a) 
--                              -> [(NonNegative Int, Probabilistic a)]
--                              -> Bool
-- prop_frequency_sat_invariant (NonEmpty xs) ys = prob_invariant (frequency zs)
--     where
--         (xs0,xs1) = unzip xs
--         (ys0,ys1) = unzip ys
--         zs0 = map getPositive xs0 ++ map getNonNegative ys0
--         zs = zip zs0 (xs1 ++ ys1)

-- prop_oneOf_sat_invariant :: NonEmptyList (Probabilistic a) -> Bool
-- prop_oneOf_sat_invariant (NonEmpty xs) = prob_invariant (oneOf xs)

-- prop_elements_sat_invariant :: NonEmptyList a -> Bool
-- prop_elements_sat_invariant (NonEmpty xs) = prob_invariant (elements xs)

prop_u_scc_complete :: Ord a => Graph a -> Bool
prop_u_scc_complete (Graph vs es) = sort vs == sort (concat $ u_scc vs f)
    where
        f x y = (x,y) `elem` es || (y,x) `elem` es

prop_u_scc_disconnected :: Ord a => Graph a -> Bool
prop_u_scc_disconnected (Graph vs es) = 
        and [ not $ f u v 
            | (us,ys) <- zip xs (drop 1 $ tails xs)  
            , u  <- us
            , vs <- ys
            , v  <- vs ]
    where
        xs = u_scc vs f
        f x y = (x,y) `elem` es || (y,x) `elem` es

prop_u_scc_valid_components :: Ord a => Graph a -> Bool
prop_u_scc_valid_components (Graph vs es) =
        and [    u == v 
              || connected g u v 
            | vs <- xs
            , u  <- vs
            , v  <- vs ]
    where
        g  = graph vs (es ++ map T.swap es)
        xs = u_scc vs f
        f x y = (x,y) `elem` es || (y,x) `elem` es

prop_top_sort_complete :: Ord a => Graph a -> Bool
prop_top_sort_complete (Graph vs es) = OL.nubSort vs == sort (concat $ map component $ top_sort vs es)

is_cycle :: SCC v -> Bool
is_cycle (CyclicSCC _)  = True
is_cycle (AcyclicSCC _) = False

prop_top_sort_cycles :: Ord a => Graph a -> Bool
prop_top_sort_cycles (Graph vs es) = all (\xs -> and [ connected g x y | x <- xs, y <- xs ]) top
    where
        top = map component $ filter is_cycle $ top_sort vs es
        g = graph vs es

prop_top_sort_singles :: Ord a => Graph a -> Bool
prop_top_sort_singles (Graph vs es) = all (\xs -> and [ not $ (x,y) `elem` es | x <- xs, y <- xs ]) top
    where
        top = map component $ filter (not . is_cycle) $ top_sort vs es

prop_top_sort_order :: Ord v => Graph v -> Bool 
prop_top_sort_order (Graph vs es) = and [ not $ (u,v) `elem` es 
                                        | (vs,xs) <- zip top (drop 1 $ tails top)
                                        , v  <- vs
                                        , us <- xs
                                        , u  <- us ]
    where
        top = map component $ top_sort vs es

-- data Reachable v = Reach 
--         { visited :: M.Map v Color
--         , stack :: [v]
--         , eList :: [[v]]
--         }

connected :: Ord v => GraphImp v -> v -> v -> Bool
connected g u v = evalState (aux u v) (S.singleton u)
    -- aux [] (vcount g) u v
    where
        aux u v = do
            s <- get
            let xs = filter (`S.notMember` s) $ tab M.! u
            if v `elem` tab M.! u
                then return True
                else 
                    fix (\rec xs -> 
                        case xs of
                            [] -> return False
                            x:xs -> do
                                modify (S.insert x)
                                b <- aux x v
                                if b 
                                    then return True
                                    else rec xs
                        ) xs
        tab = forward g

prop_closure_complete :: Ord a => Graph a -> Bool
prop_closure_complete (Graph vs es) = OL.nubSort vs == M.keys (closure vs es)

prop_closure_contain_all_edges :: Ord a => Graph a -> Bool
prop_closure_contain_all_edges (Graph vs es) = all (\(u,v) -> v `elem` cl M.! u) es
    where
        cl = closure vs es

prop_closure_closed :: Ord a => Graph a -> Bool
prop_closure_closed (Graph vs es) = all (\(u,v) -> v `elem` cl M.! u) edge_pairs
    where
        cl = closure vs es
        edge_pairs = [ (u,w) | u <- M.keys cl, v <- cl M.! u, w <- cl M.! v ]

prop_closure_minimal :: Ord a => Graph a -> Bool
prop_closure_minimal (Graph vs es) = all (\(u,v) -> connected g u v) all_edges
    where
        g  = graph vs es
        cl = closure vs es
        all_edges = [ (u,v) | (u,us) <- M.toList cl, v <- us ]

-- choice :: [(Rational,a)] -> IO a
-- choice xs = do
--         unless (sum (map fst xs) == 1) $ error "expected probablities adding to one"
--         unless (all (>= 0) $ map fst xs) $ error "expecting non negative probablities"
--         n <- randomRIO (1,d)
--         print n
--         print ws
--         return $ snd $ head $ dropWhile (\x -> fst x < n) $ zip ws (map snd xs)
--     where
--         f x = (numerator x,denominator x)
--         g x = numerator x * (d `div` denominator x)
--         ys = map (f . fst) xs
--         zs = map (g . fst) xs
--         ws = map sum (drop 1 $ inits zs)
--         -- zs = 
--         d = foldl lcm 1 $ map snd ys

data Graph a = Graph [a] [(a,a)]
    deriving Show

instance (Arbitrary a, Eq a) => Arbitrary (Graph a) where
    arbitrary = do
        xs <- arbitrary
        n  <- if null xs 
                then return 0 
                else arbitrary
        ys <- replicateM n $ do
            x <- QC.elements xs
            y <- QC.elements xs
            return (x,y)
        return $ Graph xs ys

-- newtype Pointer = Ptr Int

-- data LList s a = LList Pointer Pointer

-- data Heap s a = Heap 
--         { item  :: STArray s Pointer a
--         , right :: STArray s Pointer Pointer }

return []

run_tests :: IO Bool
run_tests = $forAllProperties (quickCheckWithResult stdArgs { chatty = False })

    -- TODO:
    -- Mutable linked lists in top_sort 
    --      to concatenate edge lists in constant time
    -- Mutable arrays to compile the subset structure
    -- factor out the mutable operations of top_sort to reduce conversions
    --      in closure
    -- finish up the minimality property of closures
main :: IO ()
main = do
    xs <- map read `liftM` getArgs
    let n  = head xs
        m  = 1000 :: Int
        us = [0..m] 
    vs <- replicateM n (permIO us)
    let 
        divides x y = y /= 0 && x `mod` y == 0 ;
        -- edge = const $ const True
        edge = divides
        !es = evalList [(v0,v1) | v0 <- us, v1 <- us, edge v0 v1 ] ;
    timeIt $ do
        forM_ vs $ \vs -> do
            let !_x = evalList $ map evalList $ u_scc vs
                    (\x y -> x `edge` y || y `edge` x)
            -- print $ last $ last _x
            return ()
    printf "expecting  %.2f\n" (0.57 / 20 * fromIntegral n :: Double)
    -- let r = map head $ top_sort us es
    -- mapM_ print r
    -- print $ or [ y `edge` x | (x,xs) <- zip r (drop 1 $ tails r), y <- xs ]
    -- print $ sort r == us
    timeIt $ forM_ vs $ \vs -> do
        let !_x = evalList $ map (evalList . component) $ top_sort vs es
        return ()
    printf "expecting  %.2f\n" (23.95 / 20 * fromIntegral n :: Double)
    timeIt $ forM_ vs $ \vs -> do
        let !_x = evalList $ M.toList $ M.map evalList $ closure vs es
        return ()
    printf "expecting  %.2f\n" (36.45 / 20 * fromIntegral n :: Double)
    -- $quickCheckAll
    -- replicateM_ 10 $ do
    --  choice [(1%10,"hello"),(3%10,"world"),(6%10,"hoho")] >>= putStrLn

    return ()
    -- timeIt $ 
    --  replicateM_ 100 $ do
    --      !_x <- evalList `liftM` choose_n 5000 [1..10000 :: Int]
            -- return ()
