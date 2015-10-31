{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
module Logic.Expr.Genericity 
    ( TypeSystem2(..)
    , typ_fun1, typ_fun2, typ_fun3
    , common, check_type
    , unify, normalize_generics
    , ambiguities, suffix_generics
    , specialize
    , Generic(..)
    , instantiate, substitute_types
    , substitute_type_vars
    , HasGenerics(..)
    , strip_generics, var_strip_generics
    , fun_strip_generics, def_strip_generics
    , ctx_strip_generics, type_strip_generics
    , OneExprP, TwoExprP, ThreeExprP, FourExprP
    , patterns, vars_to_sorts
    , gen_to_fol, to_fol_ctx
    , match_some, mk_error
    , match_all )
where

    -- Modules
import Logic.Expr.Expr
import Logic.Expr.Classes
import Logic.Expr.Label
import Logic.Expr.PrettyPrint
import Logic.Expr.Type

    -- Libraries
import Control.Applicative hiding (empty, Const)
import Control.Arrow
import Control.Monad
import Control.Monad.State

import           Data.Either
import           Data.List as L hiding ( union )
import           Data.List.Ordered hiding (nub)
import           Data.Map as M 
                    hiding ( foldl, map, union, unions, (\\) )
import qualified Data.Map as M
import qualified Data.Maybe as MM
import qualified Data.Set as S 

import Prelude as L

import Utilities.Error
import Utilities.Format


suffix_generics :: String -> GenericType -> GenericType
suffix_generics _  v@(VARIABLE _)      = v
suffix_generics xs (GENERIC x)         = GENERIC (x ++ "@" ++ xs)
suffix_generics xs (Gen s ts) = Gen s $ map (suffix_generics xs) ts

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
        FunApp f args -> FunApp f' new_args
          where
            f'          = substitute_types ft f
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
    check_args xp f@(Fun _ _ _ ts _) = do
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
    check_args xp (Fun gs name lf ts t) = do
            let n       = length ts
            guard (n == length ts)
            let args    = zipWith rewrite_types (L.map show [1..n]) xp
                targs   = L.map type_of args
                rt      = GENERIC ("a@" ++ show (n+1))
                -- t0 and t1 are type tuples for the sake of unification
                t0      = Gen IntSort (t:ts) 
                t1      = Gen IntSort (rt:targs)
            uni <- unify t0 t1
            let fe x   = specialize uni . rewrite_types x
                ft x   = instantiate uni . suffix_generics x
                gs2   = map (ft "1") gs
                us    = L.map (ft "1") ts
                u     = ft "1" t
                args2 = map (fe "2") args
                expr = FunApp (Fun gs2 name lf us u) $ args2 
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
check_type f@(Fun _ n _ ts t) mxs = do
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
typ_fun1 f@(Fun _ n _ ts t) mx        = do
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
typ_fun2 f@(Fun _ n _ ts t) mx my     = do
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
typ_fun3 f@(Fun _ n _ ts t) mx my mz  = do
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

unify_aux :: [(Type,Type)] -> Maybe (Map String Type)
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
unify_aux ( (Gen x xs, Gen y ys) : zs ) = do
    guard $ x == y &&
        length xs == length ys
    unify_aux $ zip xs ys ++ zs
unify_aux [] = return empty
unify_aux _  = Nothing

unify :: GenericType -> GenericType -> Maybe (Map String GenericType)
unify t0 t1 = 
    unify_aux [(suffix_generics "1" t0, suffix_generics "2" t1)]

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
type_strip_generics (Gen s ts) = do
    ts <- mapM type_strip_generics ts
    return (FOT s ts)
type_strip_generics _       = Nothing

fun_strip_generics :: Fun -> Maybe FOFun
fun_strip_generics (Fun ts n lf ps rt) = do
    ts <- mapM type_strip_generics ts
    ps <- mapM type_strip_generics ps
    rt <- type_strip_generics rt
    return (Fun ts n lf ps rt)

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

class Typed a => HasGenerics a where
    generics    :: a -> S.Set String
    variables   :: a -> S.Set String
    types_of    :: a -> S.Set Type
    genericsList :: a -> [String]
    generics x  = S.fromList $ genericsList x
    genericsList x  = concatMap genericsList $ S.toList $ types_of x
    variables x = S.unions $ map variables $ S.toList $ types_of x

class (HasGenerics a, TypeOf a ~ Type, TypeSystem (TypeOf b)) 
        => Generic a b where
    substitute_types'    :: (TypeOf a -> TypeOf b) -> a -> b
    instantiate' :: Map String (TypeOf b) -> a -> b
    substitute_type_vars' :: Map String (TypeOf b) -> a -> b

substitute_types :: Generic a a => (Type -> Type) -> a -> a
substitute_types = substitute_types'

instantiate :: Generic a a => Map String Type -> a -> a
instantiate = instantiate'

substitute_type_vars :: Generic a a => Map String Type -> a -> a
substitute_type_vars = substitute_type_vars'

instance HasGenerics GenericType where
    genericsList (GENERIC s)     = [s]
    genericsList (VARIABLE _)    = []
    genericsList (Gen _ ts) = concatMap genericsList ts
    variables (VARIABLE s)       = S.singleton s
    variables (GENERIC _)        = S.empty
    variables (Gen _ ts) = S.unions $ map variables ts
    types_of t = S.singleton t

instance Generic GenericType GenericType where
    substitute_types' f t = rewrite (substitute_types' f) t
    instantiate' m t = f t
        where
            f t0@(GENERIC x) = 
                case M.lookup x m of
                    Just t1  -> t1
                    Nothing  -> t0
            f t           = rewrite f t
    substitute_type_vars' m t = f t
        where
            f t0@(VARIABLE x) = 
                case M.lookup x m of
                    Just t1  -> t1
                    Nothing  -> t0
            f t           = rewrite f t

instance (HasGenerics t, TypeSystem t) => HasGenerics (AbsFun t) where
    types_of (Fun _ _ _ ts t) = S.unions $ L.map types_of $ t : ts

instance (TypeSystem t', Generic Type t') => Generic (AbsFun Type) (AbsFun t') where
    substitute_types' f (Fun gs n lf ts t) = Fun (map f gs) n lf (map f ts) $ f t
    instantiate' m x = substitute_types' (instantiate' m) x
    substitute_type_vars' m x = substitute_types' (substitute_type_vars' m) x

instance (TypeSystem t, HasGenerics t) => HasGenerics (AbsDef t q) where
    types_of (Def _ _ ts t e) = S.unions $ types_of e : types_of t : map types_of ts

instance (IsQuantifier q, Generic Type t', TypeSystem t') 
        => Generic (AbsDef Type q) (AbsDef t' q) where
    substitute_types' f (Def gs n ts t e) = 
            Def (map f gs) n 
                (map (substitute_types' f) ts) 
                (f t) 
                (substitute_types' f e)
    instantiate' m x = substitute_types' (instantiate' m) x
    substitute_type_vars' m x = substitute_types' (substitute_type_vars' m) x

instance (TypeSystem t, HasGenerics t) => HasGenerics (AbsVar t) where
    types_of (Var _ t)  = types_of t

instance (TypeSystem t', Generic Type t') => Generic Var (AbsVar t') where
    substitute_types' f (Var x t) = Var x $ f t
    instantiate' m x = substitute_types' (instantiate' m) x
    substitute_type_vars' m x = substitute_types' (substitute_type_vars' m) x
 
instance (TypeSystem t, HasGenerics t) => HasGenerics (AbsExpr t q) where
    types_of (Word v)      = types_of v
    types_of (Const _ t)   = types_of t
    types_of (Cast e t)     = S.union (types_of t) (types_of e)
    types_of (Lift e t)     = S.union (types_of t) (types_of e)
    types_of (FunApp f xp)    = S.unions $ types_of f : map types_of xp
    types_of (Binder _ vs r xp t) = S.unions $ types_of t : types_of r : types_of xp : map types_of vs

instance (IsQuantifier q, Generic Type t', TypeSystem t') 
        => Generic (AbsExpr Type q) (AbsExpr t' q) where
    substitute_types' g = rewriteExpr g id (substitute_types' g)
    instantiate' m x = substitute_types' (instantiate' m) x
    substitute_type_vars' m x = substitute_types' (substitute_type_vars' m) x

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
normalize_generics :: (Tree t, Generic t t) => t -> t
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

    -- instantiation patterns
    -- patterns ts is the list of all the types occurring in
    -- ts that has generic parameters and type variables 
    -- and convert all to generic parameters in preparation
    -- for unification
patterns :: Generic a a => a -> [Type]
patterns ts = map maybe_pattern pat
    where
        pat  = L.filter hg types
        types = L.map gen $ S.elems $ types_of ts
        hg x = not $ S.null $ generics x
            -- has generics
        -- gen = M.fromSet GENERIC $ S.unions $ L.map variables types
        
        gen (VARIABLE s) = (GENERIC s)
        gen t = rewrite gen t

        -- ungen (GENERIC s) = VARIABLE s
        -- ungen t = rewrite ungen t

    -- generic to first order
gen_to_fol :: IsQuantifier q 
           => S.Set FOType 
           -> Label 
           -> AbsExpr Type q 
           -> [(Label,AbsExpr FOType q)]
gen_to_fol types lbl e = map (f &&& inst) xs
    where
        inst m = mk_error ("gen_to_fol", types_of $ e' m)
                    strip_generics $ e' m
        e' m   = substitute_type_vars (M.map as_generic m) e
        xs     = match_all pat (S.elems types)
        f xs   = composite_label [lbl, label $ concatMap z3_decoration $ M.elems xs]
        pat    = patterns e

to_fol_ctx :: forall q. IsQuantifier q 
           => S.Set FOType 
           -> AbsContext Type q 
           -> AbsContext FOType q
to_fol_ctx types (Context s vars funs defs dums) = 
        Context s vars' funs' defs' dums'
    where
        vars' = M.map fv  vars
        funs' = decorated_table $ concatMap ff $ M.elems funs
        defs' = decorated_table $ concatMap fdf $ M.elems defs
        dums' = M.map fdm dums
        fv    = mk_error () var_strip_generics
        ff fun = map inst xs
            where
                pat    = patterns fun
                xs     = L.map (M.map as_generic) 
                            $ match_all pat (S.elems types)
                inst :: Map String Type -> FOFun
                inst m = mk_error m fun_strip_generics $ substitute_type_vars m fun'

                fun' :: Fun
                fun' = substitute_types f fun
                f (GENERIC s) = VARIABLE s
                f t = rewrite f t
        fdf def = map inst xs -- M.fromJust . def_strip_generics
            where 
                pat    = patterns def
                xs     = L.map (M.map as_generic) 
                            $ match_all pat (S.elems types)
                
                inst :: Map String Type -> AbsDef FOType q
                inst m = mk_error m def_strip_generics $ substitute_type_vars m def'

                def' :: AbsDef Type q               
                def' = substitute_types f def
                f (GENERIC s) = VARIABLE s
                f t = rewrite f t
        fdm = MM.fromJust . var_strip_generics

match_all :: [Type] -> [FOType] -> [Map String FOType]
match_all pat types = 
        foldM (\x p -> do
                t  <- types'
                m  <- MM.maybeToList $ unify p t
                ms <- MM.maybeToList $ mapM type_strip_generics (M.elems m) 
                let m'  = M.fromList $ zip (M.keys m) ms
                    m'' = M.mapKeys (reverse . drop 2 . reverse) m'
                guard $ consistent m'' x
                return (m'' `M.union` x)
            ) M.empty pat'
    where
        pat' = L.map f pat
        f (VARIABLE s) = GENERIC s
        f t = rewrite f t
        types' = map as_generic types

match_some :: [Type] -> [FOType] -> [Map String FOType]
match_some pat types = nubSort $ do -- map (M.map head) ms -- do
        ms <- foldM (\x (_,xs) -> do
                m <- xs
                guard $ consistent m x
                return (m `M.union` x)
            ) M.empty (M.toList ms')
--        ms <- forM (toList ms') $ \(k,xs) -> do
--            x <- xs
--            return (k,x)
--        let ms' = fromList ms
        guard $ M.keysSet ms == vars
        return ms
    where
        pat' = L.map f pat
        f (VARIABLE s) = GENERIC s
        f t = rewrite f t
        types' = map as_generic types
        vars = S.unions $ map generics pat'
        ms' = M.unionsWith (++) ms
--        ms :: [Map String [FOType]]
        ms :: [Map String [Map String FOType]]
        ms = do
            p  <- pat'
            t  <- types'
            m  <- MM.maybeToList $ unify p t
            ms <- MM.maybeToList $ mapM type_strip_generics (M.elems m) 
            let ms' = M.fromList $ zip (map (reverse . drop 2 . reverse) $ M.keys m) ms
            return $ M.map (const [ms']) ms' 

--mk_error :: (Expr -> Maybe FOExpr) -> Expr -> Maybe FOExpr
mk_error :: (Show a, Show c, Tree a) => c -> (a -> Maybe b) -> a -> b
mk_error z f x = 
        case f x of
            Just y -> y
            Nothing -> $myError $ format "failed to strip type variables: \n{0}\n{1}" (pretty_print' x) z

consistent :: (Eq b, Ord k) 
           => Map k b -> Map k b -> Bool
consistent x y = x `M.intersection` y == y `M.intersection` x

maybe_pattern :: Type -> Type
maybe_pattern t = MM.fromMaybe t $ do
        m <- unify (maybe_type gA) t'
        return $ instantiate m $ fun_type gB2 gA2
    where
        t' = g2v t
        g2v (GENERIC x) = VARIABLE x
        g2v t = rewrite g2v t
        
        -- v2g (VARIABLE x) = GENERIC x
        -- v2g t = rewrite v2g t

        gA = GENERIC "a"
        gB2 = GENERIC "b@1"
        gA2 = GENERIC "a@1"

-- is_maybe :: Type -> Bool
-- is_maybe t = MM.isJust (unify t (maybe_type gA))
--     where
--         gA = GENERIC "a"

type_vars_to_sorts :: Type -> State ([FOType],Map String FOType) FOType
type_vars_to_sorts t = 
        case t of
          VARIABLE n -> do
            m <- gets snd
            case n `M.lookup` m of
              Just t -> return t
              Nothing -> do
                t <- gets $ head . fst
                modify $ tail *** M.insert n t
                return t
          GENERIC _ -> fail "expecting no more generic parameters"
          Gen s ts  -> make_type s <$> mapM type_vars_to_sorts ts

vars_to_sorts_aux :: AbsExpr Type q  -> State ([FOType],Map String FOType) (AbsExpr FOType q)
vars_to_sorts_aux = rewriteExprM type_vars_to_sorts return vars_to_sorts_aux

vars_to_sorts :: Map String Sort -> AbsExpr Type q -> AbsExpr FOType q
vars_to_sorts sorts e = evalState (vars_to_sorts_aux e) (new_sorts, empty)
    where
        new_sorts = map as_type $ map (("G" ++) . show) [0 :: Int ..] `minus` keys sorts
        as_type n = make_type (Sort n n 0) []
