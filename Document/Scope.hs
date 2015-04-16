{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes,TupleSections  #-}
{-# LANGUAGE ScopedTypeVariables       #-}
module Document.Scope where

    -- Modules
import Logic.Expr hiding (Const)

import UnitB.AST

    -- Libraries
import Control.Monad.Identity
import Control.Parallel.Strategies

import Data.Either
import Data.Either.Combinators
import Data.List as L
import Data.Map as M

import Utilities.Format
import Utilities.Syntactic
import Utilities.Permutation

    -- clashes is a symmetric, reflexive relation
class Ord a => Scope a where
    make_inherited :: a -> Maybe a
    keep_from :: DeclSource -> a -> Maybe a
    error_item :: a -> (String,LineInfo)
    clashes :: a -> a -> Bool
    merge_scopes :: a -> a -> a

is_inherited :: Scope s => s -> Maybe s
is_inherited = keep_from Inherited

is_local :: Scope s => s -> Maybe s
is_local = keep_from Local

instance Scope VarScope where
    keep_from s (Evt m) = Just $ Evt $ M.mapMaybe f m
        where
            f x@(_,_,s',_)
                | s == s'   = Just x
                | otherwise = Nothing
    keep_from s x
            | f x == s  = Just x
            | otherwise = Nothing
        where
            f (TheoryDef _ s _) = s
            f (TheoryConst _ s _) = s
            f (Machine _ s _) = s
            f (DelMch _ s _) = s
            f (Evt _) = error "is_inherited Scope VarScope"
    make_inherited (TheoryDef x _ y) = Just $ TheoryDef x Inherited y
    make_inherited (TheoryConst x _ y) = Just $ TheoryConst x Inherited y
    make_inherited (Machine x _ y) = Just $ Machine x Inherited y
    make_inherited (DelMch x _ y)  = Just $ DelMch x Inherited y
    make_inherited (Evt m) = Just $ Evt $ M.map f m
        where
            f (x,y,_,z) = (x,y,Inherited,z)
    clashes (Evt m0) (Evt m1) = not $ M.null $ m0 `M.intersection` m1
    clashes (DelMch _ _ _) (Machine _ Inherited _) = False
    clashes (Machine _ Inherited _) (DelMch _ _ _) = False
    clashes _ _ = True
    error_item (Evt m) = head' $ elems $ mapWithKey msg m
        where
            head' [x] = x
            head' _ = error "VarScope Scope VarScope: head'"
            msg (Just k) (_v,sc,_,li) = (format "{1} (event {0})" k sc :: String, li)
            msg Nothing (_v,_,_,li) = (format "dummy", li)
    error_item (Machine _ _ li)   = ("state variable", li)
    error_item (TheoryDef _ _ li) = ("constant", li)
    error_item (TheoryConst _ _ li) = ("constant", li)
    error_item (DelMch _ _ li)   = ("deleted variable", li)
    merge_scopes (Evt m0) (Evt m1) = Evt $ unionWith (error "VarScope Scope.merge_scopes: Evt, Evt") m0 m1
    merge_scopes (DelMch _ s _) (Machine v Inherited li) = DelMch (Just v) s li
    merge_scopes (Machine v Inherited li) (DelMch _ s _) = DelMch (Just v) s li
    merge_scopes _ _ = error "VarScope Scope.merge_scopes: _, _"

data VarScope =
        TheoryConst Var DeclSource LineInfo
        | TheoryDef Def DeclSource LineInfo
        | Machine Var DeclSource LineInfo
        | DelMch (Maybe Var) DeclSource LineInfo
        | Evt (Map (Maybe EventId) (Var,EvtScope,DeclSource,LineInfo))
            -- in Evt, 'Nothing' stands for a dummy
    deriving (Eq,Ord,Show)

-- instance NFData VarScope where

data EvtScope = Param | Index
    deriving (Eq,Ord)

instance Show EvtScope where
    show Param = "parameter"
    show Index = "index"

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