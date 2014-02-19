{-# LANGUAGE BangPatterns #-}
module Logic.Genericity where

    -- Modules
import Logic.Expr
import Logic.Classes

    -- Libraries
import Control.Monad

import qualified Data.Graph as G
import           Data.List as L hiding ( (\\), union )
import           Data.Map as M 
                    hiding ( foldl, map, union, unions, (\\) )
import qualified Data.Map as M
import           Data.Set as S ( (\\) )
import qualified Data.Set as S 
                    hiding ( map, fromList, insert, foldl )

import Prelude as L

import Utilities.Format

instance Show a => Show (G.SCC a) where
    show (G.AcyclicSCC v) = "AcyclicSCC " ++ show v
    show (G.CyclicSCC vs) = "CyclicSCC " ++ show vs 

data Unification = Uni
    { l_to_r :: Map String Type
    , edges  :: [(String,String)]
    }

empty_u :: Unification
empty_u = Uni empty []

zcast :: Type -> Either String Expr -> Either String Expr
zcast t me = do
        e <- me
        let { err_msg = format (unlines
            [ "expression has type incompatible with its type annotation:"
            , "  expression: {0}"
            , "  type: {1}"
            , "  type annotation: {2} "
            ]) e (type_of e) t :: String }
        u <- maybe (Left err_msg) Right $ unify t $ type_of e
        return $ specialize_right u e

suffix_generics :: String -> Type -> Type
suffix_generics _  v@(VARIABLE _)      = v
suffix_generics xs (GENERIC x)         = GENERIC (x ++ "@" ++ xs)
suffix_generics xs (USER_DEFINED s ts) = USER_DEFINED s $ map (suffix_generics xs) ts
suffix_generics xs (ARRAY t0 t1)       = ARRAY (suffix_generics xs t0) (suffix_generics xs t1)

rewrite_types :: String -> Expr -> Expr
rewrite_types xs (Word (Var name t))        = rewrite fe $ Word (Var name $ ft u)
    where
        fe          = rewrite_types xs
        ft          = suffix_generics xs
        u           = ft t
rewrite_types xs (Const gs v t)             = rewrite fe $ Const gs2 v u
    where
        fe          = rewrite_types xs
        ft          = suffix_generics xs
        u           = ft t
        gs2         = map ft gs
rewrite_types xs (FunApp (Fun gs f ts t) args) = FunApp (Fun gs2 f us u) new_args
    where
        fe          = rewrite_types xs
        ft          = suffix_generics xs
        us          = map ft ts
        u           = ft t
        gs2         = map ft gs
        new_args    = map fe args
rewrite_types xs e@(Binder _ _ _ _)            = rewrite (rewrite_types xs) e

check_args :: [Expr] -> Fun -> Maybe (Expr) 
check_args xp (Fun gs name ts t) = do
            guard (length xp == length ts)
            let n       = length ts
            let xs      = zip (L.map show [1..n]) xp
            let args    = L.map (uncurry rewrite_types) xs
            let targs   = L.map type_of args
            let rt      = GENERIC ("a@" ++ show (n+1))
                -- t0 and t1 are type tuples for the sake of unification
            let t0      = USER_DEFINED IntSort (t:ts) 
            let t1      = USER_DEFINED IntSort (rt:targs)
            uni <- unify t0 t1
            let fe x   = specialize uni . rewrite_types x
            let ft x   = instantiate uni . suffix_generics x
            let gs2   = map (ft "1") gs
            let us    = L.map (ft "1") ts
            let u     = ft "1" t
            -- let !args1 = map (rewrite_types "2") args
            let args2 = map (fe "2") args
            let expr = FunApp (Fun gs2 name us u) $ args2 
            return expr

check_type :: Fun -> [Either String Expr] -> Either String Expr
check_type f@(Fun _ n ts t) mxs = do
        xs <- forM mxs id
        let args = unlines $ map (\(i,x) -> format (unlines
                            [ "   argument {0}:  {1}"
                            , "   type:          {2}" ] )
                            i x (type_of x))
                        (zip [0..] xs) 
        let err_msg = format (unlines 
                    [  "arguments of '{0}' do not match its signature:"
                    ,  "   signature: {1} -> {2}"
                    ,  "{3}"
                    ] )
                    n ts t args :: String
        maybe (Left err_msg) Right $ check_args xs f

typ_fun1 :: Fun -> ExprP -> ExprP
typ_fun1 f@(Fun _ n ts t) mx        = do
        x <- mx
        let err_msg = format (unlines 
                    [  "argument of '{0}' do not match its signature:"
                    ,  "   signature: {1} -> {2}"
                    ,  "   argument: {3}"
                    ,  "     type {4}"
                    ] )
                    n ts t 
                    x (type_of x) :: String
        maybe (Left err_msg) Right $ check_args [x] f

typ_fun2 :: Fun -> ExprP -> ExprP -> ExprP
typ_fun2 f@(Fun _ n ts t) mx my     = do
        x <- mx
        y <- my
        let err_msg = format (unlines 
                    [  "arguments of '{0}' do not match its signature:"
                    ,  "   signature: {1} -> {2}"
                    ,  "   left argument: {3}"
                    ,  "     type {4}"
                    ,  "   right argument: {5}"
                    ,  "     type {6}"
                    ] )
                    n ts t 
                    x (type_of x) 
                    y (type_of y) :: String
        maybe (Left err_msg) Right $ check_args [x,y] f

typ_fun3 :: Fun -> ExprP -> ExprP -> ExprP -> ExprP
typ_fun3 f@(Fun _ n ts t) mx my mz  = do
        x <- mx
        y <- my
        z <- mz
        let err_msg = format (unlines 
                    [  "arguments of '{0}' do not match its signature:"
                    ,  "   signature: {1} -> {2}"
                    ,  "   first argument: {3}"
                    ,  "     type {4}"
                    ,  "   second argument: {5}"
                    ,  "     type {6}"
                    ,  "   third argument: {7}"
                    ,  "     type {8}"
                    ] )
                    n ts t 
                    x (type_of x) 
                    y (type_of y) 
                    z (type_of z) :: String
        maybe (Left err_msg) Right $ check_args [x,y,z] f

unify_aux :: Type -> Type -> Unification -> Maybe Unification
unify_aux (GENERIC x) t1 u
        | not (x `member` l_to_r u)   = Just u 
                { l_to_r = M.insert x t1 $ l_to_r u
                , edges = [ (x,y) | y <- fv ] ++ edges u
                }
        | x `member` l_to_r u         = do
            new_u <- unify_aux t1 (l_to_r u ! x) u
            let new_t = instantiate (l_to_r new_u) t1
            return new_u 
                { l_to_r = M.insert x new_t $ l_to_r $ new_u 
                , edges = [ (x,y) | y <- fv ] ++ edges u
                }
    where
        fv = S.toList $ generics t1
unify_aux t0 t1@(GENERIC _) u = unify_aux t1 t0 u
unify_aux (VARIABLE x) (VARIABLE y) u
        | x == y                = Just u
        | otherwise             = Nothing
unify_aux (USER_DEFINED x xs) (USER_DEFINED y ys) u
        | x == y && length xs == length ys = foldM f u (zip xs ys)
        | otherwise                        = Nothing
    where
        f u (x, y) = unify_aux x y u
unify_aux (ARRAY t0 t1) (ARRAY t2 t3) u = do
        u <- unify_aux t0 t2 u
        unify_aux t1 t3 u
unify_aux _ _ _               = Nothing


unify :: Type -> Type -> Maybe (Map String Type)
unify t0 t1 = do
        u <- unify_aux (suffix_generics "1" t0) (suffix_generics "2" t1) empty_u
        let es = edges u
        let vs = L.nub $ L.concat [ [x,y] | (x,y) <- es ]
        let adj_list = toAdjList es
            -- build an adjacency list. Excludes vertices with no neighbors

        let compl    = map final $ toAdjList (adj_list ++ map g vs) -- :: [(String,String,[String])]
            -- add the vertices with no neighbors

        let m = l_to_r u
        let top_order = reverse $ G.stronglyConnComp compl
        
            -- this is a loop that makes sure that a type
            -- instantiation map can be applied in any 
            -- order equivalently. If the result of unify_aux
            -- gives a, b := f.X, g.a, with a,b type variables,
            -- g and f type constructors and X a constant type,
            -- the loop above replaces it with a, b := f.X, g.(f.X)
            -- so that the application of the substitution 
            -- eliminate a and b completely from a type.
            --
            -- the data structure is a graph with type
            -- variables as vertices. There is an edge from a
            -- to b if `m` maps a to a type that contains 
            -- variable b.
            --
            -- the loop below traverses the graph in topological
            -- order and modify `m', the result of unify_aux
            -- so that, for each visited type variable, there is
            -- no reference to it left in any of the types in `m'
        foldM (\m cc -> 
                case cc of
                    G.AcyclicSCC v ->
                        if v `member` m
                            then return $ M.map (instantiate $ singleton v (m ! v)) m
                            else return m
                    _ -> Nothing
            ) m top_order
    where
        final (x,xs) = (x, x, L.concat xs)
        toAdjList xs = map f $ groupBy same_soure $ sort xs
            -- from a list of edges, form a list of vertex adjacency

        same_soure (x,_) (y,_) = x == y 
        f ( (x,y):xs ) = (x,y:map snd xs)
        f [] 		   = error "Genericity.unify.f: expecting non empty argument"
        g x = (x,[])

    -- merge type instances
merge_inst :: Map String Type -> Map String Type -> Maybe (Map String Type)
merge_inst r0 r1 = foldWithKey h (Just M.empty) (M.map Just r0 `union` M.map Just r1)
    where
        union xs ys = unionWith g xs ys
        g mx my = do
                x <- mx
                y <- my
                guard (x == y)
                return x
        h k (Just x) (Just m) = Just $ M.insert k x m
        h _ _ _               = Nothing

class Generic a where
    generics :: a -> S.Set String
    substitute_types :: (Type -> Type) -> a -> a
    instantiate :: Map String Type -> a -> a
    substitute_type_vars :: Map String Type -> a -> a

    instantiate m x = substitute_types (instantiate m) x
    substitute_type_vars m x = substitute_types (substitute_type_vars m) x
    
instance Generic Type where
    generics (GENERIC s)         = S.singleton s
    generics (ARRAY t0 t1)       = generics t0 `S.union` generics t1
    generics (VARIABLE _)        = S.empty
    generics (USER_DEFINED _ ts) = S.unions $ map generics ts
    substitute_types f t = rewrite (substitute_types f) t
    instantiate m t = f t
        where
            f t0@(GENERIC x) = 
                case M.lookup x m of
                    Just t1  -> t1
                    Nothing  -> t0
            f t           = rewrite f t
    substitute_type_vars m t = f t
        where
            f t0@(VARIABLE x) = 
                case M.lookup x m of
                    Just t1  -> t1
                    Nothing  -> t0
            f t           = rewrite f t


instance Generic Fun where
    generics (Fun _ _ ts t) = S.unions (generics t : map generics ts)
    substitute_types f (Fun gs n ts t) = Fun (map f gs) n (map f ts) $ f t

instance Generic Var where
    generics (Var _ t)  = generics t
    substitute_types f (Var x t) = Var x $ f t

instance Generic Expr where
    generics (Word (Var _ t)) = generics t
    generics (Const ts _ t)   = S.unions $ map generics (t : ts)
    generics (FunApp f xp)    = S.unions (generics f : map generics xp)
    generics (Binder _ vs r xp) = S.unions (generics r : generics xp : map generics vs)
    substitute_types g x = f x
      where
        f (Const gs x t)    = Const (map g gs) x $ g t
        f (Word x)          = Word $ h x
        f (FunApp fun args) 
                = rewrite f $ FunApp (substitute_types g fun) (map (substitute_types g) args)
        f (Binder q vs r e) 
                = rewrite f $ Binder q (map h vs) r e
        h (Var x t) = Var x $ g t

ambiguities :: Expr -> [Expr]
ambiguities e@(Word (Var _ t))
        | S.null $ generics t = []
        | otherwise           = [e]
ambiguities e@(Const _ _ t)    
        | S.null $ generics t = []
        | otherwise           = [e]
ambiguities e@(FunApp f xp)    
        | not $ L.null children     = children
        | not $ S.null $ generics f = [e]
        | otherwise                 = []
    where
        children = L.concatMap ambiguities xp
ambiguities (Binder _ _ r xp) = ambiguities r ++ ambiguities xp


    -- Change the name of generic parameters
    -- to follow alphabetical order: 
    -- a .. z ; aa .. az ; ba .. bz ...
normalize_generics :: Expr -> Expr
normalize_generics expr = specialize renaming expr
    where
        letters = map (:[]) [ 'a' .. 'z' ]
        gen = (letters ++ [ x ++ y | x <- gen, y <- letters ])
        f (m,names) e = (M.union renaming m, drop n names)
            where
                free_gen = generics e \\ keysSet m
                renaming = fromList $ zip (S.toList free_gen) names
                n        = S.size free_gen
        renaming = fst $ visit f (empty, map GENERIC gen) expr

instantiate_left :: Map String Type -> Type -> Type
instantiate_left m t = instantiate m (suffix_generics "1" t)

instantiate_right :: Map String Type -> Type -> Type
instantiate_right m t = instantiate m (suffix_generics "2" t)

    -- apply a type substitution to an expression
specialize :: Map String Type -> Expr -> Expr
specialize = instantiate

specialize_left :: Map String Type -> Expr -> Expr
specialize_left m e  = specialize m (rewrite_types "1" e)

specialize_right :: Map String Type -> Expr -> Expr
specialize_right m e = specialize m (rewrite_types "2" e)
