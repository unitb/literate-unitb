{-# LANGUAGE BangPatterns #-}
module UnitB.Genericity where

    -- Modules
import Z3.Def -- hiding ( type_of )

    -- Libraries
import Control.Monad

import Data.Foldable as F
    hiding ( foldl, forM_, mapM_ )
import Data.List as L
import Data.Map as M 
    hiding ( foldl, map, union, unions )
import qualified Data.Map as M
import qualified Data.Set as S 
    hiding ( map, fromList, insert, foldl )

import qualified Data.Graph as G

import Prelude as L

import Utilities.Format

import qualified System.IO.Unsafe as Unsafe

instance Show a => Show (G.SCC a) where
    show (G.AcyclicSCC v) = "AcyclicSCC " ++ show v
    show (G.CyclicSCC vs) = "CyclicSCC " ++ show vs 

data Unification = Uni
    { l_to_r :: Map String Type
    , edges  :: [(String,String)]
--    , right_to_left :: Map String Type
--    , vertices :: Map String Vertex
--    , dependencies :: Graph 
    }

unsafePerformIO x = ()
--unsafePerformIO = Unsafe.unsafePerformIO

empty_u = Uni empty []

suffix_generics :: String -> Type -> Type
suffix_generics _ BOOL = BOOL
suffix_generics _ INT = INT
suffix_generics _ REAL = REAL
suffix_generics xs (GENERIC x) = GENERIC (x ++ "@" ++ xs)
suffix_generics xs (USER_DEFINED s ts) = USER_DEFINED s $ map (suffix_generics xs) ts
suffix_generics xs (ARRAY t0 t1)       = ARRAY (suffix_generics xs t0) (suffix_generics xs t1)
suffix_generics xs (SET t)             = SET (suffix_generics xs t) 

rewrite_types :: String -> Expr -> Expr
rewrite_types xs (Word (Var name t))        = rewrite fe $ Word (Var name $ ft u)
    where
        fe          = rewrite_types xs
        ft          = suffix_generics xs
        u           = ft t
rewrite_types xs (Const gs v t)             = rewrite fe $ Const (map ft gs) v u
    where
        fe          = rewrite_types xs
        ft          = suffix_generics xs
        u           = ft t
rewrite_types xs (FunApp (Fun gs f ts t) args) = rewrite fe $ FunApp (Fun (map ft gs) f us u) new_args
    where
        fe          = rewrite_types xs
        ft          = suffix_generics xs
        us          = map ft ts
        u           = ft t
        new_args    = map fe args
rewrite_types xs e@(Binder _ _ _)           = rewrite (rewrite_types xs) e

--set_type t (Word (Var xs _))       = Word (Var xs t)
--set_type t (Const v _)             = Const v t
--set_type t 
--set_type t 

check_args :: [Expr] -> Fun -> Maybe (Expr) --, Map String Type)
check_args xp f@(Fun gs name ts t) = do
            let !()     = unsafePerformIO (putStrLn "> step 0")
            guard (length xp == length ts)
            let !()     = unsafePerformIO (putStrLn "> step 1")
            let n       = length ts
            let xs      = zip (L.map show [1..n]) xp
            let args    = L.map (uncurry rewrite_types) xs
            let targs   = L.map type_of args
            let rt      = GENERIC ("a@" ++ show (n+1))
            let t0      = USER_DEFINED IntSort (t:ts) 
            let t1      = USER_DEFINED IntSort (rt:targs)
            let !()     = unsafePerformIO (putStrLn "> step 2")
            let !()     = unsafePerformIO (print gs)
            let !()     = unsafePerformIO (putStrLn "> signature")
            let !()     = unsafePerformIO (forM_ (ts++[t]) (\x -> print $ suffix_generics "1" x))
            let !()     = unsafePerformIO (putStrLn "> argument type")
            let !()     = unsafePerformIO (forM_ (targs++[rt]) (\x -> print $ suffix_generics "2" x))
            let !()     = unsafePerformIO (putStrLn "> args:")
            let !()     = unsafePerformIO (print args)
            uni <- unify t0 t1
            let !()    = unsafePerformIO (print $ instantiate_left uni t0)
            let !()    = unsafePerformIO (putStrLn "> step 3")
            let fe x   = specialize uni . rewrite_types x
            let ft x   = instantiate uni . suffix_generics x
            let gs2   = map (ft "1") gs
            let us    = L.map (ft "1") ts
            let u     = ft "1" t
            let !args1 = map (rewrite_types "2") args
            let !args2 = map (fe "2") args
            let expr = FunApp (Fun gs2 name us u) $ args2 
            let !()    = unsafePerformIO (putStrLn "> mapping")
            let !()     = unsafePerformIO (mapM_ print $ M.toList uni)
--            let !()     = unsafePerformIO (print $ map (suffix_generics "1") gs)
            let !()    = unsafePerformIO (putStrLn "> actual generic parameters")
            let !()     = unsafePerformIO (print gs2)
            let !()    = unsafePerformIO (putStrLn "> name")
            let !()     = unsafePerformIO (print name)
            let !()    = unsafePerformIO (putStrLn "> argument types")
            let !()     = unsafePerformIO (mapM_ print us)
            let !()    = unsafePerformIO (putStrLn "> return type")
            let !()     = unsafePerformIO (print u)
            let !()    = unsafePerformIO (putStrLn "> actual arguments")
            let !()     = unsafePerformIO (print args1)
            let !()     = unsafePerformIO (print args2)
            let !()     = unsafePerformIO (putStrLn "> step 4")
            return (expr) --,uni)

typ_fun1 f mx        = do
        x <- mx
        maybe (Left "bad type") Right $ check_args [x] f
typ_fun2 f@(Fun gs n ts t) mx my     = do
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
                    n ts t x (type_of x) y (type_of y) :: String
        let !() = unsafePerformIO (putStrLn ("x: " ++ show x))
        let !() = unsafePerformIO (putStrLn ("y: " ++ show y))
        maybe (Left err_msg) Right $ check_args [x,y] f
typ_fun3 f mx my mz  = do
        x <- mx
        y <- my
        z <- mz
        maybe (Left "bad type") Right $ check_args [x,y,z] f

    -- A
unify_aux :: Type -> Type -> Unification -> Maybe Unification
unify_aux BOOL BOOL u = Just u
unify_aux INT INT u   = Just u
unify_aux REAL REAL u = Just u
unify_aux t0@(GENERIC x) t1 u
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
        !() = unsafePerformIO (do
                putStrLn ("> matching: " ++ if (x `member` l_to_r u) then "already mapped" else "new mapping")
                print (t0,t1))
--unify_aux (GENERIC x) t u
--        | S.null $ generics t = Just $ M.singleton x t
--        | otherwise           = Nothing
unify_aux t0 t1@(GENERIC x) u = unify_aux t1 t0 u
--        | S.null $ generics t = Just $ M.singleton x t
--        | otherwise           = Nothing
unify_aux (USER_DEFINED x xs) (USER_DEFINED y ys) u
        | x == y && length xs == length ys = foldM f u (zip xs ys)
        | otherwise                        = Nothing
    where
        f u (x, y) = unify_aux x y u
unify_aux (SET t0) (SET t1) u = unify_aux t0 t1 u
unify_aux (ARRAY t0 t1) (ARRAY t2 t3) u = do
        u <- unify_aux t0 t2 u
        unify_aux t1 t3 u
unify_aux _ _ u               = Nothing

unify t0 t1 = do
        u <- unify_aux (suffix_generics "1" t0) (suffix_generics "2" t1) empty_u
        let es = edges u
        let vs = L.nub $ L.concat [ [x,y] | (x,y) <- es ]
--        let toVertex   = fromList $ zip vs [1..]
--        let fromVertex = fromList $ zip [1..] vs
--        let bounds = (1,length vs)
--        let ibes = [ (toVertex ! x, toVertex ! y) | (x,y) <- es ]
            -- integer based edges
--        let g = G.buildG bounds ibes
        let adj_list = toAdjList es
            -- build an adjacency list. Excludes vertices with no neighbors

        let compl    = map final $ toAdjList (adj_list ++ map g vs) -- :: [(String,String,[String])]
            -- add the vertices with no neighbors

        let m = l_to_r u
        let top_order = reverse $ G.stronglyConnComp compl
        let !() = unsafePerformIO (putStrLn "> > partial mapping")
        let !() = unsafePerformIO (mapM_ print $ M.toList $ l_to_r u)
        let !() = unsafePerformIO (putStrLn "> > symbolic dependencies")
        let !() = unsafePerformIO (mapM_ print compl)
        
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
--        let !() = unsafePerformIO (print top_order)
        foldM (\m cc -> 
                case cc of
                    G.AcyclicSCC v ->
                        let !() = unsafePerformIO (putStrLn "hello")
                        in
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
        g x = (x,[])
        h (x,y) = (x,x,y)

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
    
instance Generic Type where
    generics BOOL = S.empty
    generics INT  = S.empty
    generics REAL = S.empty
    generics (GENERIC s)        = S.singleton s
    generics (ARRAY t0 t1)      = generics t0 `S.union` generics t1
    generics (USER_DEFINED s ts)= S.unions $ map generics ts
    generics (SET t)            = generics t  

--instance Generic Expr where
--    d

instance Generic Fun where
    generics (Fun _ _ ts t) = S.unions (generics t : map generics ts)

--map_type f t@INT                 = t
--map_type f t@REAL                = t
--map_type f t@BOOL                = t
--map_type f t@(ARRAY t0 t1)       = ARRAY (f t0) (f t1)
--map_type f t@(GENERIC _)         = t
--map_type f t@(USER_DEFINED s ts) = USER_DEFINED s $ map f ts
--map_type f (SET t)               = SET $ f t

--fold_type

instantiate :: Map String Type -> Type -> Type
instantiate m t = f t
    where
        f t0@(GENERIC x) = 
            case M.lookup x m of
                Just t1  -> t1
                Nothing  -> t0
        f t           = rewrite f t

instantiate_left m t = instantiate m (suffix_generics "1" t)

instantiate_right m t = instantiate m (suffix_generics "2" t)

specialize :: Map String Type -> Expr -> Expr
specialize m e = f e
    where
        f (Const gs x t)    = Const (map g gs) x $ g t
        f (Word x)          = Word $ h x
        f x@(FunApp (Fun gs n ts t) args) 
                = rewrite f $ FunApp (Fun (map g gs) n (map g ts) $ g t) args
        f x@(Binder q vs e) 
                = rewrite f $ Binder q (map h vs) e
        g t     = instantiate m t
        h (Var x t) = Var x $ g t

-- is_type_correct

--data TypeInfo = TI Expr (Map String Type)
--
--type_of :: Expr -> Maybe (Type, Map String Type)
----type_of = error "not implemented"
--type_of (Const _ t)      = Just (t, M.empty)
--type_of (Word (Var _ t)) = Just (t, M.empty)
--type_of (Binder _ _ e)   = type_of e
--type_of (FunApp (Fun n ts r) args) 
--        | length ts == length args = do
--                m <- foldM f (zip ts args)
--                let r0 = instantiate m r
--                return (r0,m)
--        | otherwise = Nothing
--    where
--        f m2 (t1, x) = do
--            (t0, m0) <- type_of x
--            m1 <- unify t0 t1
----            m2 <- mm
--            m2 <- merge_inst m1 m2
--            merge_inst m2 m3

--generic_fun_count e = f 0 e
--    where
--        f n e = h e + visit f n e
--        h (Word v) = g v
--        h (Const _ t) = S.size $ generics t
--        h (FunApp (Fun _ ts t) xs) = S.size $ generics t + L.sum (map (S.size . generics) ts)
--        h (Binder q vs x) = L.sum $ map g vs
--        g (Var _ t) = S.size $ generics t

make_gen_param_unique e = f 0 e
    where
        f e = rewrite f e

