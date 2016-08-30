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
import Logic.Expr.Context
import Logic.Expr.Label
import Logic.Expr.PrettyPrint
import Logic.Expr.Type
import Logic.Names

    -- Libraries
import Control.Applicative hiding (empty)
import Control.Arrow
import Control.Lens hiding (rewrite,Context)
import Control.Monad
import Control.Monad.State
import Control.Precondition

import           Data.Either
import           Data.List as L hiding ( union )
import           Data.List.Ordered hiding (nub)
import           Data.Map.Class as M 
                    hiding ( map, union, unions, (\\) )
import qualified Data.Map.Class as M
import qualified Data.Maybe as MM
import qualified Data.Set as S 

import Prelude as L

import Text.Printf.TH

import Utilities.Table

suffix_generics :: String -> GenericType -> GenericType
suffix_generics _  v@(VARIABLE _)      = v
suffix_generics xs (GENERIC x)         = GENERIC (('@':xs) `addSuffix` x)
suffix_generics xs (Gen s ts) = Gen s $ map (suffix_generics xs) ts
--suffix_generics = fmap

rewrite_types :: (IsQuantifier q,IsName n)
              => String
              -> AbsExpr n Type q -> AbsExpr n Type q
rewrite_types xs e = -- typesOf %~ suffix_generics tag
    case e of
        Word (Var name t) -> Word (Var name u)
          where
            u           = ft t
        Lit v t         -> Lit v t'
          where
            t'          = ft t
        Cast e t -> Cast (rewrite_types xs e) (suffix_generics xs t)
        Lift e t -> Lift (rewrite_types xs e) (suffix_generics xs t)
        FunApp f args -> funApp f' new_args
          where
            f'          = substitute_types ft f
            new_args    = map fe args
        Binder q vs r term t -> rewrite (rewrite_types xs) (Binder q vs r term (ft t))
        Record e -> Record $ e & traverseRecExpr %~ rewrite_types xs
    where
        fe          = rewrite_types xs
        ft          = suffix_generics xs

class TypeSystem t => TypeSystem2 t where
    check_args :: (IsQuantifier q,IsName n)
               => [AbsExpr n t q] 
               -> AbsFun n t 
               -> Maybe (AbsExpr n t q) 
    zcast :: (IsQuantifier q,IsName n)
          => t -> ExprPG n t q
          -> ExprPG n t q

instance TypeSystem2 FOType where
    check_args xp f@(Fun _ _ _ ts _ _) = do
            guard (map type_of xp == ts)
            return $! funApp f xp
    zcast t me = do
            e <- me
            let { err_msg = intercalate "\n"
                            [ [printf|expression has type incompatible with its expected type:|]
                            , [printf|  expression: %s|]        (pretty e)
                            , [printf|  actual type: %s|]       (pretty $ type_of e)
                            , [printf|  expected type: %s |]    (pretty t)
                            ] }
            unless (type_of e == t)
                $  Left [err_msg]
            return e

instance TypeSystem2 GenericType where
    check_args xp (Fun gs name lf ts t wd) = do
            let n       = length ts
            guard (n == length ts)
            let args    = zipWith rewrite_types (map show [1..n]) xp
                targs   = L.map type_of args
                rt      = GENERIC (reserved "a" (n+1))
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
                expr = funApp (Fun gs2 name lf us u wd) $ args2 
            return expr
    zcast t me = do
            e <- me
            let { err_msg = intercalate "\n"
                            [ [printf|expression has type incompatible with its expected type:|]
                            , [printf|  expression: %s|]        (pretty e)
                            , [printf|  actual type: %s|]       (pretty $ type_of e)
                            , [printf|  expected type: %s |]    (pretty t)
                            ] }
            u <- maybe (Left [err_msg]) Right $ 
                unify t $ type_of e
            return $ specialize_right u e

check_all :: [Either [String] a] -> Either [String] [a]
check_all xs 
    | all isRight xs = Right $ rights xs
    | otherwise      = Left $ concat $ lefts xs

check_type :: (IsQuantifier q,IsName n)
           => AbsFun n Type 
           -> [ExprPG n Type q] 
           -> ExprPG n Type q
check_type f@(Fun _ n _ ts t _) mxs = do
        xs <- check_all mxs
        let args = unlines $ map (\(i,x) -> unlines 
                                    [ [printf|   argument %d:  %s|] i (pretty x)
                                    , [printf|   type:          %s|] (pretty $ type_of x) ])
                        (zip [0..] xs) 
            err_msg = unlines 
                        [ [printf|arguments of '%s' do not match its signature:|] (render n)
                        , [printf|   signature: %s -> %s|] (pretty ts) (pretty t)
                        , [printf|%s|] args ]
        maybe (Left [err_msg]) Right $ check_args xs f

type OneExprP n t q   = IsQuantifier q => ExprPG n t q -> ExprPG n t q
type TwoExprP n t q   = IsQuantifier q => ExprPG n t q -> ExprPG n t q -> ExprPG n t q
type ThreeExprP n t q = IsQuantifier q => ExprPG n t q -> ExprPG n t q -> ExprPG n t q -> ExprPG n t q
type FourExprP n t q  = IsQuantifier q => ExprPG n t q -> ExprPG n t q -> ExprPG n t q -> ExprPG n t q -> ExprPG n t q


typ_fun1 :: ( TypeSystem2 t,IsName n )
         => AbsFun n t
         -> OneExprP n t q
typ_fun1 f@(Fun _ n _ ts t _) mx        = do
        x <- mx
        let err_msg = unlines
                    [ [printf|argument of '%s' do not match its signature:|] (render n)
                    , [printf|   signature: %s -> %s|] (pretty ts) (pretty t)
                    , [printf|   argument: %s|] (pretty x)
                    , [printf|     type %s|] (pretty $ type_of x)
                    ]
        maybe (Left [err_msg]) Right $ check_args [x] f

typ_fun2 :: ( TypeSystem2 t,IsName n )
         => AbsFun n t  
         -> TwoExprP n t q
typ_fun2 f@(Fun _ n _ ts t _) mx my     = do
        x <- mx
        y <- my
        let err_msg = unlines
                    [ [printf|arguments of '%s' do not match its signature:|] (render n)
                    , [printf|   signature: %s -> %s|]                        (pretty ts) (pretty t)
                    , [printf|   left argument: %s|]                          (pretty x)
                    , [printf|     type %s|]                                  (pretty $ type_of x) 
                    , [printf|   right argument: %s|]                         (pretty y)
                    , [printf|     type %s|]                                  (pretty $ type_of y)
                    ]
        maybe (Left [err_msg]) Right $ check_args [x,y] f

typ_fun3 :: ( TypeSystem2 t,IsName n )
         => AbsFun n t
         -> ThreeExprP n t q
typ_fun3 f@(Fun _ n _ ts t _) mx my mz  = do
        x <- mx
        y <- my
        z <- mz
        let err_msg = unlines
                   [ [printf|arguments of '%s' do not match its signature:|] (render n) 
                   , [printf|   signature: %s -> %s|]                        (pretty ts) (pretty t) 
                   , [printf|   first argument: %s|]                         (pretty x)
                   , [printf|     type %s|]                                  (pretty $ type_of x) 
                   , [printf|   second argument: %s|]                        (pretty y)
                   , [printf|     type %s|]                                  (pretty $ type_of y) 
                   , [printf|   third argument: %s|]                         (pretty z)
                   , [printf|     type %s|]                                  (pretty $ type_of z)
                   ]
        maybe (Left [err_msg]) Right $ check_args [x,y,z] f

unify_aux :: [(Type,Type)] -> Maybe (Map InternalName Type)
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

unify :: GenericType -> GenericType -> Maybe (Map InternalName GenericType)
unify t0 t1 = 
    unify_aux [(suffix_generics "1" t0, suffix_generics "2" t1)]

strip_generics :: IsName n 
               => AbsExpr n Type q 
               -> Maybe (AbsExpr InternalName FOType q)
strip_generics (Word v)    = do
    v <- var_strip_generics v
    return (Word v)
strip_generics (Lit m t) = do
    t  <- type_strip_generics t
    return (Lit m t)
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
    return (funApp f xs)
strip_generics (Binder q vs r t et) = do
    vs <- mapM var_strip_generics vs
    r  <- strip_generics r
    t  <- strip_generics t
    et' <- type_strip_generics et
    return (binder q vs r t et')
strip_generics (Record e) = Record <$> traverseRecExpr strip_generics e

type_strip_generics :: Type -> Maybe FOType
type_strip_generics (Gen s ts) = do
    ts <- mapM type_strip_generics ts
    return (FOT s ts)
type_strip_generics _       = Nothing

fun_strip_generics :: IsName n => AbsFun n Type -> Maybe FOFun
fun_strip_generics (Fun ts n lf ps rt wd) = do
    ts <- mapM type_strip_generics ts
    ps <- mapM type_strip_generics ps
    rt <- type_strip_generics rt
    return (Fun ts (asInternal n) lf ps rt wd)

def_strip_generics :: IsName n => AbsDef n Type q -> Maybe (AbsDef InternalName FOType q)
def_strip_generics (Def ts n ps rt val) = do
    ts  <- mapM type_strip_generics ts
    ps  <- mapM var_strip_generics ps
    rt  <- type_strip_generics rt
    val <- strip_generics val
    return (makeDef ts (asInternal n) ps rt val)

var_strip_generics :: IsName n => AbsVar n Type -> Maybe FOVar
var_strip_generics (Var n t) = do
    t <- type_strip_generics t
    return (Var (asInternal n) t)

ctx_strip_generics :: IsName n
                   => (GenContext n GenericType HOQuantifier) 
                   -> Maybe (GenContext InternalName FOType HOQuantifier)
ctx_strip_generics (Context a b c d e) = 
        Context a 
            <$> (mapKeys asInternal <$> traverse var_strip_generics b)
            <*> (mapKeys asInternal <$> traverse fun_strip_generics c)
            <*> (mapKeys asInternal <$> traverse def_strip_generics d)
            <*> (mapKeys asInternal <$> traverse var_strip_generics e)

class Typed a => HasGenerics a where
    generics    :: a -> S.Set InternalName
    variables   :: a -> S.Set InternalName
    types_of    :: a -> S.Set Type
    genericsList :: a -> [InternalName]
    generics x  = S.fromList $ genericsList x
    genericsList x  = concatMap genericsList $ S.toList $ types_of x
    variables x = S.unions $ map variables $ S.toList $ types_of x

class (HasGenerics a, TypeOf a ~ Type, TypeSystem (TypeOf b)) 
        => Generic a b where
    substitute_types'    :: (TypeOf a -> TypeOf b) -> a -> b
    instantiate' :: Map InternalName (TypeOf b) -> a -> b
    substitute_type_vars' :: Map InternalName (TypeOf b) -> a -> b

substitute_types :: Generic a a => (Type -> Type) -> a -> a
substitute_types = substitute_types'

instantiate :: Generic a a => Map InternalName Type -> a -> a
instantiate = instantiate'

substitute_type_vars :: Generic a a => Map InternalName Type -> a -> a
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

instance (HasGenerics t, TypeSystem t) => HasGenerics (AbsFun n t) where
    types_of (Fun _ _ _ ts t _) = S.unions $ L.map types_of $ t : ts

instance (TypeSystem t', Generic Type t') => Generic (AbsFun n Type) (AbsFun n t') where
    substitute_types' f (Fun gs n lf ts t wd) = Fun (map f gs) n lf (map f ts) (f t) wd
    instantiate' m x = substitute_types' (instantiate' m) x
    substitute_type_vars' m x = substitute_types' (substitute_type_vars' m) x

instance (TypeSystem t,HasGenerics t,IsName n,IsQuantifier q) => HasGenerics (AbsDef n t q) where
    types_of (Def _ _ ts t e) = S.unions $ types_of e : types_of t : map types_of ts

instance (IsQuantifier q, Generic Type t', TypeSystem t',IsName n) 
        => Generic (AbsDef n Type q) (AbsDef n t' q) where
    substitute_types' f (Def gs n ts t e) = 
            makeDef (map f gs) n 
                    (map (substitute_types' f) ts) 
                    (f t) 
                    (substitute_types' f e)
    instantiate' m x = substitute_types' (instantiate' m) x
    substitute_type_vars' m x = substitute_types' (substitute_type_vars' m) x

instance (TypeSystem t, HasGenerics t,IsName n) => HasGenerics (AbsVar n t) where
    types_of (Var _ t)  = types_of t

instance (TypeSystem t', Generic Type t',IsName n) => Generic (AbsVar n Type) (AbsVar n t') where
    substitute_types' f (Var x t) = Var x $ f t
    instantiate' m x = substitute_types' (instantiate' m) x
    substitute_type_vars' m x = substitute_types' (substitute_type_vars' m) x

instance (TypeSystem t,HasGenerics t,IsName n,IsQuantifier q) => HasGenerics (AbsExpr n t q) where
    types_of (Word v)      = types_of v
    types_of (Lit _ t)   = types_of t
    types_of (Cast e t)     = S.union (types_of t) (types_of e)
    types_of (Lift e t)     = S.union (types_of t) (types_of e)
    types_of (FunApp f xp)    = S.unions $ types_of f : map types_of xp
    types_of (Binder _ vs r xp t) = S.unions $ types_of t : types_of r : types_of xp : map types_of vs
    types_of (Record x) = S.unions $ x^.partsOf (traverseRecExpr.to types_of)

instance (IsQuantifier q, Generic Type t', TypeSystem t', IsName n) 
        => Generic (AbsExpr n Type q) (AbsExpr n t' q) where
    substitute_types' g = rewriteExpr g id (substitute_types' g)
    instantiate' m x = substitute_types' (instantiate' m) x
    substitute_type_vars' m x = substitute_types' (substitute_type_vars' m) x

ambiguities :: Expr -> [Expr]
ambiguities e@(Word (Var _ t))
        | S.null $ generics t = []
        | otherwise           = [e]
ambiguities e@(Lit _ t)    
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
ambiguities (Record e) = concat $ e^.partsOf (traverseRecExpr.to ambiguities)

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
        gen = map fromString'' gen'
        gen' = (letters ++ [ x ++ y | x <- gen', y <- letters ])
        f (m,names) e = visit f (M.union renaming m, drop n names) e
            where
                free_gen = nub (genericsList e) L.\\ keys m
                renaming = fromList $ zip free_gen names
                n        = length free_gen
        renaming = fst $ f (empty, map GENERIC gen) expr

instantiate_left :: Map InternalName GenericType -> GenericType -> GenericType
instantiate_left m t = instantiate m (suffix_generics "1" t)

_instantiate_right :: Map InternalName GenericType -> GenericType -> GenericType
_instantiate_right m t = instantiate m (suffix_generics "2" t)

    -- apply a type substitution to an expression
specialize :: (IsQuantifier q,IsName n)
           => Map InternalName GenericType 
           -> AbsExpr n Type q -> AbsExpr n Type q
specialize = instantiate

_specialize_left :: (IsQuantifier q,IsName n)
                 => Map InternalName GenericType 
                 -> AbsExpr n Type q -> AbsExpr n Type q
_specialize_left m e  = specialize m (rewrite_types "1" e)

specialize_right :: (IsQuantifier q,IsName n)
                 => Map InternalName GenericType 
                 -> AbsExpr n Type q -> AbsExpr n Type q
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
gen_to_fol :: (IsQuantifier q,IsName n,Pre)
           => S.Set FOType 
           -> Label 
           -> AbsExpr n Type q 
           -> [(Label,AbsExpr InternalName FOType q)]
gen_to_fol types lbl e = map (f &&& inst) xs
    where
        inst m = mk_error ("gen_to_fol", types_of $ e' m)
                    strip_generics $ e' m
        e' m   = substitute_type_vars (M.map as_generic m) e
        xs     = match_all pat (S.elems types)
        f xs   = composite_label [lbl, label $ concatMap z3_decoration $ M.ascElems xs]
        pat    = patterns e

to_fol_ctx :: forall q n. (IsQuantifier q,IsName n)
           => S.Set FOType 
           -> GenContext n Type q 
           -> GenContext InternalName FOType q
to_fol_ctx types (Context s vars funs defs dums) = 
        Context s 
            vars' funs' defs' dums'
    where
        vars' = M.mapKeys asInternal $ M.map fv vars
        funs' = M.mapKeys asInternal $ decorated_table $ concatMap ff $ M.elems funs
        defs' = M.mapKeys asInternal $ decorated_table $ concatMap fdf $ M.elems defs
        dums' = M.mapKeys asInternal $ M.map fdm dums
        fv    = mk_error () var_strip_generics
        ff :: AbsFun n Type -> [FOFun]
        ff fun = map inst xs
            where
                pat    = patterns fun
                xs     = L.map (M.map as_generic) 
                            $ match_all pat (S.elems types)
                inst :: Map InternalName Type -> FOFun
                inst m = mk_error m fun_strip_generics $ substitute_type_vars m fun'

                fun' :: AbsFun n Type
                fun' = substitute_types f fun
                f (GENERIC s) = VARIABLE s
                f t = rewrite f t
        fdf def = map inst xs -- M.fromJust . def_strip_generics
            where 
                pat    = patterns def
                xs     = L.map (M.map as_generic) 
                            $ match_all pat (S.elems types)
                
                inst :: Map InternalName Type -> AbsDef InternalName FOType q
                inst m = mk_error m def_strip_generics $ substitute_type_vars m def'

                def' :: AbsDef n Type q               
                def' = substitute_types f def
                f (GENERIC s) = VARIABLE s
                f t = rewrite f t
        fdm = MM.fromJust . var_strip_generics

match_all :: [Type] -> [FOType] -> [Map InternalName FOType]
match_all pat types = 
        foldM (\x p -> do
                t  <- types'
                m  <- MM.maybeToList $ unify p t
                ms <- MM.maybeToList $ mapM type_strip_generics (M.elems m) 
                let m'  = M.fromList $ zip (M.keys m) ms
                    m'' = M.mapKeys dropSuffix m'
                guard $ consistent m'' x
                return (m'' `M.union` x)
            ) M.empty pat'
    where
        pat' = L.map f pat
        f (VARIABLE s) = GENERIC s
        f t = rewrite f t
        types' = map as_generic types

match_some :: [Type] -> [FOType] -> [Map InternalName FOType]
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
        ms :: [Map InternalName [Map InternalName FOType]]
        ms = do
            p  <- pat'
            t  <- types'
            m  <- MM.maybeToList $ unify p t
            ms <- MM.maybeToList $ mapM type_strip_generics (M.elems m) 
            let ms' = M.fromList $ zip (map dropSuffix $ M.keys m) ms
            return $ M.map (const [ms']) ms' 

--mk_error :: (Expr -> Maybe FOExpr) -> Expr -> Maybe FOExpr
mk_error :: (Show a, Show c, Tree a, Pre) 
         => c -> (a -> Maybe b) -> a -> b
mk_error z f x = 
        case f x of
            Just y -> y
            Nothing -> assertFalseMessage $ [printf|failed to strip type variables: \n'%s'\n'%s'|] (pretty_print' x) (show z)

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

        gB2 = GENERIC $ reserved "b" 1
        gA2 = GENERIC $ reserved "a" 1

-- is_maybe :: Type -> Bool
-- is_maybe t = MM.isJust (unify t (maybe_type gA))
--     where
--         gA = GENERIC "a"

type_vars_to_sorts :: Type -> State ([FOType],Map InternalName FOType) FOType
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

vars_to_sorts_aux :: AbsExpr n Type q  -> State ([FOType],Map InternalName FOType) (AbsExpr n FOType q)
vars_to_sorts_aux = rewriteExprM type_vars_to_sorts return vars_to_sorts_aux

names :: Pre 
      => String -> [Name]
names n = map (makeName . (n ++) . show) [0 :: Int ..]

vars_to_sorts :: Table Name Sort -> AbsExpr n Type q -> AbsExpr n FOType q
vars_to_sorts sorts e = evalState (vars_to_sorts_aux e) (new_sorts, empty)
    where
        new_sorts = map as_type $ names "G" `minus` keys sorts
        as_type n = make_type (Sort n (asInternal n) 0) []
