% !TEX root = ../design.tex
\subsection{Feasibility}

Since the feasibility of an event is proved existential with a list of conjuncts, we can identify partitions of the set of assignments of an event based on whether or not they reference the same primed variables.

It can be done with the following strategy:
\begin{itemize}
\item for each assignments, calculate the set of primed variables that it contains
\item create an undirected graph where the assignments are the vertices and draw an edge between two vertices if their set of primed variables intersect.
\item take the transitive closure of the graph. It should create a set of partitions
\end{itemize}

We implement it in \emph{partition\_expr} with a disjoint set data structure.

\begin{code}
module Logic.Expr.Existential
    ( partition_expr
    , get_partition )
where

    -- Modules
import Logic.Expr hiding (merge)

    -- Libraries
import           Control.Lens
import           Control.Monad 
import           Control.Monad.State as ST

import           Data.IntMap 
            ( (!), fromListWith
            , assocs, insert, elems
            , IntMap, fromList, Key 
            , mapMaybe )
import           Data.List.NonEmpty (nonEmpty)
import qualified Data.Map as M
import qualified Data.Set as S

get_partition :: [Var] -> [Expr] -> ([(Key, Int)], [(Var, Int)], [(Expr, Int)])
get_partition vs es = do -- error "UnitB.Feasibility.partition_expr: not implemented"
        runPartitionWith [0..m+n-1] $ do
            forM_ (M.assocs me) $ \(e,i) -> 
                forM_ (S.elems $ used_var e) $ \v ->
                    case M.lookup v mv of
                        Just j  -> merge i j
                        Nothing -> return ()
            compress
                -- At this point, i and j are in the same partition  ==  parent i = parent j
            xs <- gets $ assocs . getMap
            return (xs, M.toList mv, M.toList me)
    where
        m = length vs
        n = length cs
        cs = concatMap conjuncts es
        mv = M.fromList $ zip vs [0..]
            -- map variable
        me = M.fromList $ zip cs [m..]
            -- map expressions


partition_expr :: (TypeSystem t,IsName n,IsQuantifier q)
               => [AbsVar n t] 
               -> [AbsExpr n t q] 
               -> [([AbsVar n t],NonEmpty (AbsExpr n t q))]
partition_expr vs es' = do 
        runPartitionWith [0..m+n-1] $ do
            forM_ (M.assocs me) $ \(e,i) -> 
                forM_ (S.elems $ used_var e) $ \v ->
                    case M.lookup v mv of
                        Just j  -> merge i j
                        Nothing -> return ()
            compress
                -- At this point, i and j are in the same partition  ==  parent i = parent j
            xs <- forM (M.assocs me) $ \(e,i) -> do
                j <- parent i
                return (j,([],[e]))
            ys <- forM (M.assocs mv) $ \(v,i) -> do
                j <- parent i
                return (j,([v],[]))
            let m = fromListWith mappend $ xs ++ ys
            return $ elems $ mapMaybe (_2 nonEmpty) m 
    where
        es = filter (ztrue /=) es'
        m = length vs
        n = length cs
        cs = concatMap conjuncts es
        mv = M.fromList $ zip vs [0..]
            -- map variable
        me = M.fromList $ zip cs [m..]
            -- map expressions

data Partition = Partition { getMap :: IntMap Int }
    -- invariant for every edge x -> y, y ≤ x so that traversing the forest
    -- in increasing order of vertex number traverses each trees starting
    -- from the root.

type PartitionT = ST.State Partition

p_fromList :: [Key] -> Partition
p_fromList xs = Partition $ fromList $ zip xs xs

runPartitionWith :: [Int] -> PartitionT a -> a
runPartitionWith xs m = ST.evalState m $ p_fromList xs

merge :: Int -> Int -> PartitionT ()
merge x y = do
            ry <- root y
            rx <- root x
            if ry <= rx 
                then f ry rx
                else f rx ry
    where
        f x y = modify $ Partition . insert y x . getMap

root :: Int -> PartitionT Int
root x = do
        y <- parent x
        if x == y 
        then return x
        else do
            z <- root y
            modify $ Partition . (insert x z) . getMap
            return z

parent :: MonadState Partition m
       => Key -> m Int
parent x = gets ((!x) . getMap)

set_parent :: MonadState Partition m 
           => Key -> Int -> m ()
set_parent x y = modify (Partition . insert x y . getMap)

compress :: PartitionT ()
compress = do
        xs <- gets $ assocs . getMap
        forM_ xs $ \(x,i) -> do
            j <- parent i
            set_parent x j
            
\end{code}
