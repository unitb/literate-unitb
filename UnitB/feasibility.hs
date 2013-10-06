{-# LANGUAGE FlexibleContexts #-}
module UnitB.Feasibility 
    ( partition_expr )
where

    -- Modules
import Z3.Def 
            ( Expr(..), Var, used_var 
            , Fun (..) )
import Z3.Const

    -- Libraries
import           Control.Monad 
import           Control.Monad.State.Class
import qualified Control.Monad.Trans.State as ST

import           Data.IntMap 
            ( (!), fromListWith, keys
            , assocs, insert, elems
            , IntMap, fromList, empty )
import qualified Data.Map as M
import           Data.Monoid ( mappend )
import qualified Data.Set as S

conjuncts :: [Expr] -> [Expr]
conjuncts xs = --error "UnitB.Feasibility.conjuncts: not implemented"
     case zall xs of 
          FunApp (Fun _ "and" _ _) xs -> xs
          _ -> xs

partition_expr :: [Var] -> [Expr] -> [([Var],[Expr])]
partition_expr vs es = do -- error "UnitB.Feasibility.partition_expr: not implemented"
        runPartitionWith [0..m+n-1] $ do
            forM_ (M.assocs me) $ \(e,i) -> 
                forM_ (S.elems $ used_var e) $ \v ->
                    case M.lookup v mv of
                        Just j  -> merge i j
                        Nothing -> return ()
            compress
            xs <- forM (M.assocs me) $ \(e,i) -> do
                j <- parent i
                return (j,([],[e]))
            ys <- forM (M.assocs mv) $ \(v,i) -> do
                j <- parent i
                return (j,([v],[]))
            let m = fromListWith mappend $ (xs ++ ys :: [(Int,([Var],[Expr]))])
            return $ elems m 
    where
        m = length vs
        n = length cs
        cs = conjuncts es
        mv = M.fromList $ zip vs [0..]
            -- map variable
        me = M.fromList $ zip cs [m..]
            -- map expressions

data Partition = Partition { getMap :: IntMap Int }

type PartitionT = ST.State Partition

empty_p = Partition empty

p_fromList xs = Partition $ fromList $ zip xs xs

runPartition m = ST.evalStateT m empty_p

runPartitionWith :: [Int] -> PartitionT a -> a
runPartitionWith xs m = ST.evalState m $ p_fromList xs

add :: (Monad m, MonadState Partition m) => Int -> m ()
add x = modify $ \(Partition m) -> Partition $ insert x x m

merge :: (Monad m, MonadState Partition m) => Int -> Int -> m ()
merge x y
        | x <= y    = modify $ f x y
        | y <= x    = modify $ f y x
    where
        f x y (Partition m) = Partition $ insert y (m ! x) m

parent x = gets ((!x) . getMap)

set_parent x y = modify (Partition . insert x y . getMap)

compress :: (Monad m, MonadState Partition m) => m ()
compress = do
        xs <- gets $ keys . getMap
        forM_ xs $ \x -> do
            i <- parent x
            j <- parent i
            set_parent x j
            
classes :: (Monad m, MonadState Partition m) => m [[Int]]
classes = do
        compress
        xs <- gets $ assocs . getMap
        let ys = fromListWith (++) $ flip map xs $ \(x,y) -> (y,[x])
        return $ elems ys