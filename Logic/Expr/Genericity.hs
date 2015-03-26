{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE BangPatterns         #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE RankNTypes           #-}
module Logic.Expr.Genericity 
    ( TypeSystem2(..)
    , typ_fun1, typ_fun2, typ_fun3
    , common, check_type
    , unify, normalize_generics
    , ambiguities, suffix_generics
    , specialize
    , Generic(..)
    , strip_generics, var_strip_generics
    , fun_strip_generics, def_strip_generics
    , ctx_strip_generics, type_strip_generics
    , OneExprP, TwoExprP, ThreeExprP, FourExprP )
where

    -- Modules
import Logic.Expr.Expr
import Logic.Expr.Classes
import Logic.Expr.Type

    -- Libraries
import Control.Arrow
import Control.Monad

import           Data.Either
import qualified Data.Graph as G
import           Data.List as L hiding ( union )
import           Data.Map as M 
                    hiding ( foldl, map, union, unions, (\\) )
import qualified Data.Map as M
import qualified Data.Set as S 

import Prelude as L

import Utilities.Format

instance Show a => Show (G.SCC a) where
    show (G.AcyclicSCC v) = "AcyclicSCC " ++ show v
    show (G.CyclicSCC vs) = "CyclicSCC " ++ show vs 

suffix_generics :: String -> GenericType -> GenericType
suffix_generics _  v@(VARIABLE _)      = v
suffix_generics xs (GENERIC x)         = GENERIC (x ++ "@" ++ xs)
suffix_generics xs (Gen (USER_DEFINED s ts)) = Gen $ USER_DEFINED s $ map (suffix_generics xs) ts

rewrite_types :: IsQuantifier q
              => String 
              -> AbsExpr Type q -> AbsExpr Type q
rewrite_types xs e = 
    case e of
        Word (Var name t) -> rewrite fe $ Word (Var name u)
          where
            u           = ft t
        Const v t         -> rewrite fe $ Const v t'
          where
            t'          = ft t
        Cast e t -> Cast (rewrite_types xs e) (suffix_generics xs t)
        Lift e t -> Lift (rewrite_types xs e) (suffix_generics xs t)
        FunApp (Fun gs f ts t) args -> FunApp (Fun gs2 f us u) new_args
          where
            gs2         = map ft gs
            us          = map ft ts
            u           = ft t
            new_args    = map fe args
        Binder q vs r term t -> rewrite (rewrite_types xs) (Binder q vs r term (ft t))
    where
        fe          = rewrite_types xs
        ft          = suffix_generics xs

class TypeSystem t => TypeSystem2 t where
    check_args :: IsQuantifier q
               => [AbsExpr t q] 
               -> AbsFun t 
               -> Maybe (AbsExpr t q) 
    zcast :: IsQuantifier q 
          => t -> ExprPG t q
          -> ExprPG t q

instance TypeSystem2 FOType where
    check_args xp f@(Fun _ _ ts _) = do
            guard (map type_of xp == ts)
            return $ FunApp f xp
    zcast t me = do
            e <- me
            let { err_msg = format (unlines
                [ "expression has type incompatible with its expected type:"
                , "  expression: {0}"
                , "  actual type: {1}"
                , "  expected type: {2} "
                ]) e (type_of e) t :: String }
            unless (type_of e == t)
                $  Left [err_msg]
            return e

instance TypeSystem2 GenericType where
    check_args xp (Fun gs name ts t) = do
            let n       = length ts
            guard (n == length ts)
            let args    = zipWith rewrite_types (L.map show [1..n]) xp
            let targs   = L.map type_of args
            let rt      = GENERIC ("a@" ++ show (n+1))
                -- t0 and t1 are type tuples for the sake of unification
            let t0      = Gen $ USER_DEFINED IntSort (t:ts) 
            let t1      = Gen $ USER_DEFINED IntSort (rt:targs)
            uni <- unify t0 t1
            let fe x   = specialize uni . rewrite_types x
            let ft x   = instantiate uni . suffix_generics x
            let gs2   = map (ft "1") gs
            let us    = L.map (ft "1") ts
            let u     = ft "1" t
            let args2 = map (fe "2") args
            let expr = FunApp (Fun gs2 name us u) $ args2 
            return expr
    zcast t me = do
            e <- me
            let { err_msg = format (unlines
                [ "expression has type incompatible with its expected type:"
                , "  expression: {0}"
                , "  actual type: {1}"
                , "  expected type: {2} "
                ]) e (type_of e) t :: String }
            u <- maybe (Left [err_msg]) Right $ 
                unify t $ type_of e
            return $ specialize_right u e

check_all :: [Either [String] a] -> Either [String] [a]
check_all xs 
    | all isRight xs = Right $ rights xs
    | otherwise      = Left $ concat $ lefts xs

check_type :: IsQuantifier q => Fun 
           -> [ExprPG Type q] -> ExprPG Type q
check_type f@(Fun _ n ts t) mxs = do
        xs <- check_all mxs
        let args = unlines $ map (\(i,x) -> format (unlines
                            [ "   argument {0}:  {1}"
                            , "   type:          {2}" ] )
                            (i :: Int) x (type_of x))
                        (zip [0..] xs) 
            err_msg = format (unlines 
                    [  "arguments of '{0}' do not match its signature:"
                    ,  "   signature: {1} -> {2}"
                    ,  "{3}"
                    ] )
                    n ts t args :: String
        maybe (Left [err_msg]) Right $ check_args xs f

type OneExprP t q   = IsQuantifier q => ExprPG t q -> ExprPG t q
type TwoExprP t q   = IsQuantifier q => ExprPG t q -> ExprPG t q -> ExprPG t q
type ThreeExprP t q = IsQuantifier q => ExprPG t q -> ExprPG t q -> ExprPG t q -> ExprPG t q
type FourExprP t q  = IsQuantifier q => ExprPG t q -> ExprPG t q -> ExprPG t q -> ExprPG t q -> ExprPG t q


typ_fun1 :: ( TypeSystem2 t )
         => AbsFun t
         -> OneExprP t q
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
        maybe (Left [err_msg]) Right $ check_args [x] f

typ_fun2 :: ( TypeSystem2 t
            )
         => AbsFun t  -> TwoExprP t q
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
        maybe (Left [err_msg]) Right $ check_args [x,y] f

typ_fun3 :: ( TypeSystem2 t )
         => AbsFun t
         -> ThreeExprP t q
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
        maybe (Left [err_msg]) Right $ check_args [x,y,z] f

unify_aux :: [(GenericType,GenericType)] -> Maybe (Map String Type)
unify_aux ( (GENERIC x, t1) : xs ) 
        | t1 == GENERIC x = unify_aux xs
        | x `S.member` generics t1 = Nothing
        | otherwise       = do
            let s = singleton x t1
            r <- unify_aux $ map (instantiate s *** instantiate s) xs
            -- let s' = singleton x $ instantiate r t1
            return $ M.insert x (instantiate r t1) r
unify_aux ( (t0, t1@(GENERIC _)) : xs ) = unify_aux $ (t1,t0) : xs
unify_aux ( (VARIABLE x, VARIABLE y) : xs ) = do
    guard (x == y)
    unify_aux xs
unify_aux ( (Gen (USER_DEFINED x xs), Gen (USER_DEFINED y ys)) : zs ) = do
    guard $ x == y &&
        length xs == length ys
    unify_aux $ zip xs ys ++ zs
unify_aux [] = return empty
unify_aux _  = Nothing

unify :: GenericType -> GenericType -> Maybe (Map String GenericType)
unify t0 t1 = unify_aux [(suffix_generics "1" t0, suffix_generics "2" t1)]

strip_generics :: AbsExpr Type q -> Maybe (AbsExpr FOType q)
strip_generics (Word v)    = do
    v <- var_strip_generics v
    return (Word v)
strip_generics (Const m t) = do
    t  <- type_strip_generics t
    return (Const m t)
strip_generics (Cast e t) = do
    e <- strip_generics e
    t <- type_strip_generics t
    return (Cast e t)
strip_generics (Lift e t) = do
    e <- strip_generics e
    t <- type_strip_generics t
    return (Lift e t)
strip_generics (FunApp f xs) = do
    f  <- fun_strip_generics f
    xs <- mapM strip_generics xs
    return (FunApp f xs)
strip_generics (Binder q vs r t et) = do
    vs <- mapM var_strip_generics vs
    r  <- strip_generics r
    t  <- strip_generics t
    et' <- type_strip_generics et
    return (Binder q vs r t et')

type_strip_generics :: Type -> Maybe FOType
type_strip_generics (Gen (USER_DEFINED s ts)) = do
    ts <- mapM type_strip_generics ts
    return (FOT $ USER_DEFINED s ts)
type_strip_generics _       = Nothing

fun_strip_generics :: Fun -> Maybe FOFun
fun_strip_generics (Fun ts n ps rt) = do
    ts <- mapM type_strip_generics ts
    ps <- mapM type_strip_generics ps
    rt <- type_strip_generics rt
    return (Fun ts n ps rt)

def_strip_generics :: AbsDef Type q -> Maybe (AbsDef FOType q)
def_strip_generics (Def ts n ps rt val) = do
    ts  <- mapM type_strip_generics ts
    ps  <- mapM var_strip_generics ps
    rt  <- type_strip_generics rt
    val <- strip_generics val
    return (Def ts n ps rt val)

var_strip_generics :: Var -> Maybe FOVar
var_strip_generics (Var n t) = do
    t <- type_strip_generics t
    return (Var n t)

ctx_strip_generics :: Context -> Maybe (AbsContext FOType HOQuantifier)
ctx_strip_generics (Context a b c d e) = do
    bs <- mapM var_strip_generics $ M.elems b
    cs <- mapM fun_strip_generics $ M.elems c
    ds <- mapM def_strip_generics $ M.elems d
    es <- mapM var_strip_generics $ M.elems e
    return $ Context
        a 
        (fromList $ zip (keys b) bs)
        (fromList $ zip (keys c) cs)
        (fromList $ zip (keys d) ds)
        (fromList $ zip (keys e) es)

class Generic a where
    generics    :: a -> S.Set String
    variables   :: a -> S.Set String
    substitute_types     :: (Type -> Type) -> a -> a
    instantiate :: Map String Type -> a -> a
    substitute_type_vars :: Map String Type -> a -> a
    types_of    :: a -> S.Set Type
    genericsList :: a -> [String]
 
    generics x  = S.fromList $ genericsList x
    genericsList x  = concatMap genericsList $ S.toList $ types_of x
    variables x = S.unions $ map variables $ S.toList $ types_of x
    instantiate m x = substitute_types (instantiate m) x
    substitute_type_vars m x = 
        substitute_types (substitute_type_vars m) x
    
instance Generic GenericType where
    genericsList (GENERIC s)     = [s]
    genericsList (VARIABLE _)    = []
    genericsList (Gen (USER_DEFINED _ ts)) = concatMap genericsList ts
    variables (VARIABLE s)       = S.singleton s
    variables (GENERIC _)        = S.empty
    variables (Gen (USER_DEFINED _ ts)) = S.unions $ map variables ts
    types_of t = S.singleton t
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
    types_of (Fun _ _ ts t) = S.fromList $ t : ts
    substitute_types f (Fun gs n ts t) = Fun (map f gs) n (map f ts) $ f t

instance IsQuantifier q => Generic (AbsDef Type q) where
    types_of (Def _ _ ts t e) = S.unions $ S.singleton t : types_of e : map types_of ts
    substitute_types f (Def gs n ts t e) = 
            Def (map f gs) n 
                (map (substitute_types f) ts) 
                (f t) 
                (substitute_types f e)
 
instance Generic Var where
    types_of (Var _ t)  = S.singleton t
    substitute_types f (Var x t) = Var x $ f t
 
instance IsQuantifier q => Generic (AbsExpr Type q) where
    types_of (Word (Var _ t)) = S.singleton t
    types_of (Const _ t)   = S.singleton t
    types_of (Cast e t)     = S.insert t $ types_of e
    types_of (Lift e t)     = S.insert t $ types_of e
    types_of (FunApp f xp)    = S.unions $ types_of f : map types_of xp
    types_of (Binder _ vs r xp t) = S.unions $ S.insert t (types_of r) : types_of xp : map types_of vs
    substitute_types g x = f x
      where
        f (Const x t)    = Const x $ g t
        f (Word x)          = Word $ h x
        f (Cast e t)     = Cast (f e) (g t) 
        f (Lift e t)     = Lift (f e) (g t) 
        f (FunApp fun args) 
                = rewrite f $ FunApp (substitute_types g fun) (map (substitute_types g) args)
        f (Binder q vs r e t) 
                = rewrite f $ Binder q (map h vs) r e (g t)
        h (Var x t) = Var x $ g t

ambiguities :: Expr -> [Expr]
ambiguities e@(Word (Var _ t))
        | S.null $ generics t = []
        | otherwise           = [e]
ambiguities e@(Const _ t)    
        | S.null $ generics t = []
        | otherwise           = [e]
ambiguities e@(Cast e' t)
        | not $ S.null $ generics t = [e]
        | otherwise                 = ambiguities e'
ambiguities e@(Lift e' t)
        | not $ S.null $ generics t = [e]
        | otherwise                 = ambiguities e'
ambiguities e@(FunApp f xp)    
        | not $ L.null children     = children
        | not $ S.null $ generics f = [e]
        | otherwise                 = []
    where
        children = L.concatMap ambiguities xp
ambiguities e@(Binder _ vs r xp t) = x ++ y ++ ambiguities r ++ ambiguities xp
    where
        vs' = L.filter (not . S.null . generics . var_type) vs
        x 
            | not $ L.null vs' = map Word vs'
            | otherwise        = []
        y 
            | not $ S.null (generics t) = [e]
            | otherwise                 = []

common :: GenericType -> GenericType -> Maybe GenericType
common t1 t2 = do
        m <- unify t1 t2 
        return $ normalize_generics $ instantiate_left m t1

    -- Change the name of generic parameters
    -- to follow alphabetical order: 
    -- a .. z ; aa .. az ; ba .. bz ...
normalize_generics :: (Tree t, Generic t) => t -> t
normalize_generics expr = instantiate renaming expr
    where
        letters = map (:[]) [ 'a' .. 'z' ]
        gen = (letters ++ [ x ++ y | x <- gen, y <- letters ])
        f (m,names) e = visit f (M.union renaming m, drop n names) e
            where
                free_gen = nub (genericsList e) L.\\ keys m
                renaming = fromList $ zip free_gen names
                n        = length free_gen
        renaming = fst $ f (empty, map GENERIC gen) expr

instantiate_left :: Map String GenericType -> GenericType -> GenericType
instantiate_left m t = instantiate m (suffix_generics "1" t)

_instantiate_right :: Map String GenericType -> GenericType -> GenericType
_instantiate_right m t = instantiate m (suffix_generics "2" t)

    -- apply a type substitution to an expression
specialize :: IsQuantifier q
           => Map String GenericType 
           -> AbsExpr Type q -> AbsExpr Type q
specialize = instantiate

_specialize_left :: IsQuantifier q 
                 => Map String GenericType 
                 -> AbsExpr Type q -> AbsExpr Type q
_specialize_left m e  = specialize m (rewrite_types "1" e)

specialize_right :: IsQuantifier q
                 => Map String GenericType 
                 -> AbsExpr Type q -> AbsExpr Type q
specialize_right m e = specialize m (rewrite_types "2" e)
