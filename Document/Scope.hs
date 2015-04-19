{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes,TupleSections  #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE DefaultSignatures         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE FlexibleContexts          #-}
module Document.Scope 
    ( Scope(..)
    , HasDeclSource (..)
    , HasLineInfo (..)
    , make_table
    , make_all_tables 
    , make_all_tables'
    , all_errors
    , all_errors'
    , is_inherited, is_local
    , DeclSource(..)  )
where

    -- Libraries
import Control.Lens
import Control.Monad.Identity
import Control.Parallel.Strategies

import Data.Either
import Data.Either.Combinators
import Data.List as L
import Data.Map as M

import Utilities.Syntactic
import Utilities.Permutation

    -- clashes is a symmetric, reflexive relation
class Ord a => Scope a where
    error_item :: a -> (String,LineInfo)

    keep_from :: DeclSource -> a -> Maybe a
    default keep_from :: (HasDeclSource a DeclSource) => DeclSource -> a -> Maybe a
    keep_from s x = guard (x ^. declSource == s) >> return x

    make_inherited :: a -> Maybe a
    default make_inherited :: (HasDeclSource a DeclSource) => a -> Maybe a
    make_inherited x = Just $ x & declSource .~ Inherited

    clashes :: a -> a -> Bool
    clashes _ _ = True

    merge_scopes :: a -> a -> a
    merge_scopes _ _ = error "Scope.merge_scopes"

class HasDeclSource a b where
    declSource :: Lens' a b

class HasLineInfo a b where
    lineInfo :: Lens' a b

is_inherited :: Scope s => s -> Maybe s
is_inherited = keep_from Inherited

is_local :: Scope s => s -> Maybe s
is_local = keep_from Local

data DeclSource = Inherited | Local
    deriving (Eq,Ord,Show)

all_errors' :: [Either [e] a] -> Either [e] [a]
all_errors' xs = do
    let es = lefts xs
    unless (L.null es)
        $ Left $ concat es
    return $ L.map fromRight' xs

all_errors :: Ord k => Map k (Either [e] a) -> Either [e] (Map k a)
all_errors m = do
        let es = lefts $ M.elems m
        unless (L.null es)
            $ Left $ concat es
        return $ M.map fromRight' m

make_table :: (Ord a, Show a) 
           => (a -> String) 
           -> [(a,b,LineInfo)] 
           -> Either [Error] (Map a (b,LineInfo))
make_table f xs = returnOrFail $ fromListWith add $ L.map mkCell xs
    where
        mkCell (x,y,z) = (x,Right (y,z))
        sepError (x,y) = case y of
                 Left z -> Left (x,z)
                 Right (z,li) -> Right (x,(z,li))
        returnOrFail m = failIf $ L.map sepError $ M.toList m
        failIf xs 
            | L.null ys = return $ M.fromList $ rights xs
            | otherwise = Left $ L.map (uncurry err) ys
            where
                ys = lefts xs
        err x li = MLError (f x) (L.map (show x,) li)
        lis (Left xs)     = xs
        lis (Right (_,z)) = [z]
        add x y = Left $ lis x ++ lis y

make_all_tables' :: (Scope b, Show a, Ord a, Ord k) 
                 => (a -> String) 
                 -> Map k [(a,b)] 
                 -> Either [Error] (Map k (Map a b))
make_all_tables' f xs = all_errors (M.map (make_table' f) xs) `using` parTraversable rseq

make_all_tables :: (Show a, Ord a, Ord k) 
                => (a -> String)
                -> Map k [(a, b, LineInfo)] 
                -> Either [Error] (Map k (Map a (b,LineInfo)))
make_all_tables f xs = all_errors (M.map (make_table f) xs) `using` parTraversable rseq

make_table' :: forall a b.
               (Ord a, Show a, Scope b) 
            => (a -> String) 
            -> [(a,b)] 
            -> Either [Error] (Map a b)
make_table' f xs = all_errors $ M.mapWithKey g ws
    where
        g k ws
                | all (\xs -> length xs <= 1) ws 
                            = Right $ L.foldl merge_scopes (head xs) (tail xs)
                | otherwise = Left $ L.map (\xs -> MLError (f k) $ L.map error_item xs) 
                                    $ L.filter (\xs -> length xs > 1) ws
            where
                xs = concat ws             
        zs = fromListWith (++) $ L.map (\(x,y) -> (x,[y])) xs
        ws :: Map a [[b]]
        ws = M.map (flip u_scc clashes) zs 