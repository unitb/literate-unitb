{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE StandaloneDeriving  #-}
module Data.Graph.Array 
    ( top_sort, closure, closure'
    , graph, graphWith, u_scc
    , GraphImp (..), run_tests 
    , from_map, cycles, acyclic
    , topological_sort )
where

import Control.Loop
import Control.Monad
import Control.Monad.Fix
import Control.Monad.ST
import Control.Monad.State ( evalState )
import Control.Monad.State.Class -- (MonadState)
import Control.Precondition

import Data.Array.IArray hiding ((!))
import Data.Array.IO
import Data.Array.ST
import Data.Graph (SCC(..))
import Data.List
import Data.STRef
import qualified Data.List.Ordered as OL
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Tuple as T

import Test.QuickCheck hiding (frequency,elements)
import qualified Test.QuickCheck as QC
import Test.QuickCheck.Report as QC

class AllZero a where
    zeros :: a

instance AllZero () where
    zeros = ()

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
            zs <- forM (S.toList $ ys S.\\ S.fromList xs) $ 
                readArray ar
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

cycles :: Ord v => GraphImp v -> [[v]]
cycles g = mapMaybe f $ topological_sort g
    where 
        f (AcyclicSCC _) = Nothing
        f (CyclicSCC xs) = Just xs

topological_sort :: forall v. Ord v => GraphImp v -> [SCC v]
topological_sort g = map (fmap (i2v !)) $ top_sort' g
    where
        i2v = int2v g

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
                modifySTRef rN (+ (-1))
                modifySTRef res (r:)       
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
                if k == k' then pop
                else do
                    x  <- readArray eList (k'-1)
                    r <- root p x 
                    c <- readArray visited r
                    case c of
                      White -> do
                        writeArray eStack (n-1) (k' - 1)
                        push x
                      Grey  -> do
                        r' <- root p v
                        when (r /= r') $ do
                                -- merge
                            y <- readArray path (n-2)
                            merge p y v
                            writeArray path (n-1) (V $ -1)
                            writeArray eStack (n-2) k'
                            writeArray eStack (n-1) 0
                            modifySTRef rN (+ (-1))
                        when (r == r') $ do
                            writeArray eStack (n-1) (k'-1)
                            writeArray cycles r True
                      Black -> do
                        writeArray eStack (n-1) (k'-1)
            unless (m == V nn && n == 0) rec
        m  <- getSets p
        r  <- readSTRef res
        rs <- forM r $ readArray cycles 
        return $ zipWith (\r b -> if b 
                then CyclicSCC (m ! r) 
                else AcyclicSCC (head $ m ! r)
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

from_map :: forall v. Ord v => [v] -> (M.Map v [v]) -> GraphImp v
from_map vs es = GraphImp vs es' i2e i2v v2i fwd bwd f f' nn mm
    where
        g = graph vs es'
        f x y = y `elem` M.findWithDefault [] x es
        f' i j = f (int2v g ! i) (int2v g ! j)
        es' = [ (u,v) | (u,vs) <- M.toList es, v <- vs ]
        vs'  = OL.nubSort vs
        nn   = length vs'
        mm   = sum $ M.elems $ M.map length es
        fwd  = es `M.union` M.fromSet (const []) (S.fromList vs')
        bwd  = M.fromListWith (++) (concat $ M.elems $ M.mapWithKey (\k vs -> map (,[k]) vs) es) 
                `M.union` M.fromSet (const []) (S.fromList vs')
        i2v :: Array Vertex v
        i2v = array (V 0,V $ nn-1) $ zip [V 0..] vs'
        i2e :: Array Vertex [Vertex]
        i2e = runSTArray $ do
                ar <- newArray (V 0,V $ nn-1) []
                forM_ (M.toList es) $ \(u,vs) -> do
                    let i  = v2i ! u
                        js = map (v2i !) vs
                    writeArray ar i js
                return ar
        v2i = M.fromList $ zip vs' [V 0..]

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
        f  u v = f' (v2i ! u) (v2i ! v)
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
                    let i = v2i ! u
                        j = v2i ! v
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
                j  <- readArray ar i
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

        -- take n `liftM` getElems ar




evalList :: [a] -> [a]
evalList xs = foldr seq xs xs

prop_evalList_is_identity :: (Eq a, Arbitrary a) => [a] -> Bool
prop_evalList_is_identity xs = xs == evalList xs


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

acyclic :: Pre => SCC v -> v
acyclic (AcyclicSCC v) = v
acyclic (CyclicSCC _)  = undefined'

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


connected :: Ord v => GraphImp v -> v -> v -> Bool
connected g u v = evalState (aux u v) (S.singleton u)
    -- aux [] (vcount g) u v
    where
        aux u v = do
            s <- get
            let xs = filter (`S.notMember` s) $ tab ! u
            if v `elem` tab ! u
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
prop_closure_contain_all_edges (Graph vs es) = all (\(u,v) -> v `elem` cl ! u) es
    where
        cl = closure vs es

prop_closure_closed :: Ord a => Graph a -> Bool
prop_closure_closed (Graph vs es) = all (\(u,v) -> v `elem` cl ! u) edge_pairs
    where
        cl = closure vs es
        edge_pairs = [ (u,w) | u <- M.keys cl, v <- cl ! u, w <- cl ! v ]

prop_closure_minimal :: Ord a => Graph a -> Bool
prop_closure_minimal (Graph vs es) = all (\(u,v) -> connected g u v) all_edges
    where
        g  = graph vs es
        cl = closure vs es
        all_edges = [ (u,v) | (u,us) <- M.toList cl, v <- us ]


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

return []

run_tests :: (PropName -> Property -> IO (a, QC.Result))
          -> IO ([a], Bool)
run_tests = $forAllProperties'

    -- TODO:
    -- Mutable linked lists in top_sort 
    --      to concatenate edge lists in constant time
    -- Mutable arrays to compile the subset structure
    -- factor out the mutable operations of top_sort to reduce conversions
    --      in closure
    -- finish up the minimality property of closures
