{-# LANGUAGE DeriveDataTypeable     #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TypeFamilies, FlexibleContexts #-}
module Logic.Expr.Expr 
    ( Expr, Expr', AbsExpr, GenExpr (..), FOExpr
    , UntypedExpr, ExprP, ExprPG, ExprPC
    , Value(..)
    , HOQuantifier(..)
    , FOQuantifier(..)
    , Context, FOContext, AbsContext(..)
    , Decl, FODecl, AbsDecl(..)
    , Fun, FOFun, AbsFun(..)
    , Var, FOVar, AbsVar(..), UntypedVar
    , Def, FODef, AbsDef(..)
    , IsQuantifier(..)
    , rewriteExpr
    , type_of, var_type
    , merge, merge_all
    , merge_ctx, merge_all_ctx
    , mk_context, empty_ctx
    , used_var, used_fun, used_types
    , substitute, rename
    , z3_fun_name
    , z3_decoration
    -- , pretty_print
    , array
    , decl, Symbol
    , ztuple_type, ztuple
    , fun_type, fun_sort
    , maybe_type
    , pair, pair_type, pair_sort
    , free_vars
    , var_decl
    )
where

    -- Module
import Logic.Expr.Label
import Logic.Expr.Classes
import Logic.Expr.Type

    -- Library
import           GHC.Generics

import Control.Applicative ((<|>),(<$>))
import Control.DeepSeq
import Control.Monad.Reader

import           Data.List as L
import qualified Data.Map as M hiding (map,foldl)
import qualified Data.Set as S
import           Data.Typeable

import Utilities.Format

type Expr = AbsExpr GenericType HOQuantifier

type FOExpr = AbsExpr FOType FOQuantifier

type AbsExpr t q = GenExpr t t q

type Expr' = AbsExpr Type FOQuantifier

type UntypedExpr = GenExpr () GenericType HOQuantifier

data GenExpr t a q = 
        Word (AbsVar t) 
        | Const Value t
        | FunApp (AbsFun t) [GenExpr t a q]
        | Binder q [AbsVar t] (GenExpr t a q) (GenExpr t a q)
        | Cast (GenExpr t a q) a
        | Lift (GenExpr t a q) a
    deriving (Eq, Ord, Typeable, Generic)

data Value = RealVal Double | IntVal Int
    deriving (Eq,Ord,Generic)

instance Show Value where
    show (RealVal v) = show v
    show (IntVal v)  = show v

data HOQuantifier = Forall | Exists | Lambda
    deriving (Eq, Ord, Generic,Typeable)

data FOQuantifier = FOForall | FOExists 
    deriving (Eq,Ord,Generic,Typeable)

instance NFData HOQuantifier where

instance NFData FOQuantifier where

type ExprP = Either [String] Expr 

type ExprPG t q = Either [String] (AbsExpr t q)

type ExprPC e = Either [String] e

var_type :: AbsVar t -> t
var_type (Var _ t) = t

type_of :: (TypeSystem t, IsQuantifier q) => AbsExpr t q -> t
type_of (Word (Var _ t))         = t
type_of (Const _ t)              = t
type_of (Cast _ t)               = t
type_of (Lift _ t)               = t
type_of (FunApp (Fun _ _ _ t) _) = t
type_of (Binder q vs _ e)   = qType q tuple (type_of e)
    where
        tuple = ztuple_type $ map var_type vs

ztuple_type :: TypeSystem t => [t] -> t
ztuple_type []          = null_type
ztuple_type [x]         = x
ztuple_type [x0,x1]     = pair_type x0 $ pair_type x1 null_type
ztuple_type (x0:x1:xs)  = pair_type x0 $ ztuple_type (x1:xs)

ztuple :: (TypeSystem t, IsQuantifier q) => [AbsExpr t q] -> AbsExpr t q
ztuple []           = unit
ztuple [x]          = x
ztuple [x0,x1]      = pair x0 $ pair x1 unit    -- FunApp (Fun [tx, txs] "pair" [tx, txs] pair_type) [x,tail]
ztuple (x0:x1:xs)   = pair x0 $ ztuple (x1:xs)  -- FunApp (Fun [tx, txs] "pair" [tx, txs] pair_type) [x,tail]

pair_sort :: Sort
pair_sort = -- Sort "Pair" "Pair" 2
               Datatype ["a","b"] "Pair" 
                    [ ("pair", 
                        [ ("first",  GENERIC "a")
                        , ("second", GENERIC "b") ]) ]


pair_type :: TypeSystem t => t -> t -> t
pair_type x y = make_type pair_sort [x,y]

null_sort :: Sort
null_sort = Sort "Null" "Null" 2

null_type :: TypeSystem t => t
null_type = make_type null_sort []

unit :: TypeSystem t => AbsExpr t q
unit = FunApp (Fun [] "null" [] null_type) []

pair :: (TypeSystem t, IsQuantifier q) => AbsExpr t q -> AbsExpr t q -> AbsExpr t q
pair x y = FunApp (Fun [] "pair" [t0,t1] $ pair_type t0 t1) [x,y]
    where
        t0 = type_of x
        t1 = type_of y

maybe_sort :: Sort
maybe_sort   = Sort "\\maybe" "Maybe" 1

maybe_type :: TypeSystem t => t -> t
maybe_type t = make_type maybe_sort [t]

fun_sort :: Sort
fun_sort = DefSort "\\pfun" "pfun" ["a","b"] (array (GENERIC "a") (maybe_type $ GENERIC "b"))

fun_type :: TypeSystem t => t -> t -> t
fun_type t0 t1 = make_type fun_sort [t0,t1] --ARRAY t0 t1

class (Eq q, Show q) => IsQuantifier q where
    merge_range :: q -> StrList
    qType :: TypeSystem t => q -> t -> t -> t
    qForall :: q
    qExists :: q

instance IsQuantifier HOQuantifier where
    merge_range Forall = Str "=>"
    merge_range Exists = Str "and"
    merge_range Lambda = Str "PRE"
    qType Lambda arg term = fun_type arg term
    qType Forall _ t = t
    qType Exists _ t = t
    qForall = Forall
    qExists = Exists

instance IsQuantifier FOQuantifier where
    merge_range FOForall = Str "=>"
    merge_range FOExists   = Str "and"
    qType FOForall _ t = t
    qType FOExists _ t = t
    qForall = FOForall
    qExists = FOExists

type Context = AbsContext GenericType HOQuantifier

type FOContext = AbsContext FOType FOQuantifier

data AbsContext t q = Context 
        (M.Map String Sort) -- sorts
        (M.Map String (AbsVar t))  -- constants
        (M.Map String (AbsFun t))  -- functions and operators
        (M.Map String (AbsDef t q))  -- transparent definitions
        (M.Map String (AbsVar t))  -- dummies
    deriving (Show,Eq,Generic,Typeable)

instance (NFData t, NFData q) => NFData (AbsContext t q) where
    rnf (Context a b c d e) = rnf (a,b,c,d,e)

class Symbol a t q where
    decl :: a -> [AbsDecl t q]

z3_decoration :: TypeSystem t => t -> String
z3_decoration t = runReader (z3_decoration' t) ProverOutput

z3_decoration' :: TypeSystem t => t -> Reader OutputMode String
z3_decoration' t = do
        opt <- ask 
        case opt of
            ProverOutput -> f <$> as_tree' t
            UserOutput -> return ""
    where
        f (List ys) = format "@Open{0}@Close" xs
            where xs = concatMap f ys :: String
        f (Str y)   = format "@@{0}" y

array_sort :: Sort
array_sort = Sort "Array" "Array" 2

array :: TypeSystem t => t -> t -> t
array t0 t1 = make_type array_sort [t0,t1]

    -- replace it everywhere
z3_fun_name :: Fun -> String
z3_fun_name (Fun xs ys _ _) = ys ++ concatMap z3_decoration xs

type Decl = AbsDecl GenericType

type FODecl = AbsDecl FOType

data AbsDecl t q = 
        FunDecl [t] String [t] t
        | ConstDecl String t
        | FunDef [t] String [AbsVar t] t (AbsExpr t q)
        | SortDecl Sort

instance NFData q => NFData (AbsDecl FOType q) where
    rnf (FunDecl xs n args t) = rnf (xs,n,args,t)
    rnf (ConstDecl n t) = rnf (n,t)
    rnf (FunDef xs n args t e) = rnf (xs,n,args,t,e)
    rnf (SortDecl s) = rnf s

type Fun = AbsFun GenericType

type FOFun = AbsFun FOType

data AbsFun t = Fun [t] String [t] t
    deriving (Eq, Ord, Generic)

instance NFData t => NFData (AbsFun t) where
    rnf (Fun xs n args t) = rnf (xs,n,args,t)

type UntypedVar = AbsVar ()

type Var = AbsVar GenericType

type FOVar = AbsVar FOType

data AbsVar t = Var String t
    deriving (Eq,Ord,Generic,Typeable)

instance NFData t => NFData (AbsVar t) where
    rnf (Var xs t) = rnf (xs,t)

type FODef = AbsDef FOType HOQuantifier

type Def = AbsDef GenericType HOQuantifier

data AbsDef t q = Def [t] String [AbsVar t] t (AbsExpr t q)
    deriving (Eq,Ord,Generic)

instance Show StrList where
    show (List xs) = "(" ++ intercalate " " (map show xs) ++ ")"
    show (Str s)   = s

instance Show HOQuantifier where
    show Forall = "forall"
    show Exists = "exists"
    show Lambda = "lambda"

instance Show FOQuantifier where
    show FOForall = "forall"
    show FOExists = "exists"

instance (TypeSystem t, IsQuantifier q, Tree t') 
        => Tree (GenExpr t t' q) where
    -- as_tree' t = return $ as_tree t
    as_tree' (Cast e t)   = do
        t' <- as_tree' t
        e' <- as_tree' e
        return $ List [Str "as", e', t']
    as_tree' (Lift e t) = do
        t' <- as_tree' t
        e' <- as_tree' e
        return $ List [ List [Str "as", Str "const", t']
                             , e']
    as_tree' (Word (Var xs _))    = return $ Str $ z3_escape xs
    -- as_tree (Const [] "Nothing" t) = List [Str "as", Str "Nothing", as_tree t]
    as_tree' (Const xs _)         = return $ Str $ show xs
    as_tree' (FunApp f [])  = do
        f   <- decorated_name' f
        return $ Str f
    as_tree' (FunApp f ts)  = do
        ts' <- mapM as_tree' ts
        f   <- decorated_name' f
        return $ List (Str f : ts')
    as_tree' (Binder q xs r xp)  = do
        xs' <- mapM as_tree' xs
        r'  <- as_tree' r
        xp' <- as_tree' xp
        return $ List [ Str $ show q
                      , List xs'
                      , List 
                          [ merge_range q
                          , r'
                          , xp' ] ]
    rewriteM' _ s x@(Word _)           = return (s,x)
    rewriteM' _ s x@(Const _ _)        = return (s,x)
    rewriteM' f s (Lift e t)           = do
            (x,e') <- f s e
            return (x, Lift e' t)
    rewriteM' f s (Cast e t)           = do
            (x,e') <- f s e
            return (x, Cast e' t)
    rewriteM' f s0 (FunApp g@(Fun _ _ _ _) xs)  = do
            (s1,ys) <- fold_mapM f s0 xs
            return (s1,FunApp g ys)
    rewriteM' f s0 (Binder q xs r0 x)  = do
            (s1,r1) <- f s0 r0
            (s2,y)  <- f s1 x
            return (s2,Binder q xs r1 y)

instance (TypeSystem t, IsQuantifier q) => Show (AbsExpr t q) where
    show e = show $ runReader (as_tree' e) UserOutput

instance TypeSystem t => Named (AbsDecl t q) where
    name (FunDecl _ n _ _)  = n
    name (ConstDecl n _)    = n
    name (FunDef _ n _ _ _) = n
    name (SortDecl s)       = name s
    decorated_name x = runReader (decorated_name' x) ProverOutput
    decorated_name' d@(FunDef ts _ _ _ _) = do
        ts' <- mapM z3_decoration' ts
        return $ z3_name d ++ concat ts'
    decorated_name' d@(FunDecl ts _ _ _)  = do
        ts' <- mapM z3_decoration' ts
        return $ z3_name d ++ concat ts'
    decorated_name' (ConstDecl n _)     = return n
    decorated_name' (SortDecl s) = decorated_name' s

instance (TypeSystem t, IsQuantifier q) => Tree (AbsDecl t q) where
    as_tree' d@(FunDecl _ _ dom ran) = do
            argt <- mapM as_tree' dom
            t    <- as_tree' ran
            n    <- decorated_name' d
            return $ List [ Str "declare-fun", 
                Str n, 
                (List argt), t ]
    as_tree' (ConstDecl n t) = do
            t' <- as_tree' t
            return $ List [ Str "declare-const", Str n, t' ]
    as_tree' d@(FunDef _ _ dom ran val) = do
            argt <- mapM as_tree' dom
            rt   <- as_tree' ran
            def  <- as_tree' val
            n    <- decorated_name' d
            return $ List [ Str "define-fun", 
                Str n, (List argt), 
                rt, def ]
    as_tree' (SortDecl IntSort)  = return $ Str "; comment: we don't need to declare the sort Int"
    as_tree' (SortDecl BoolSort) = return $ Str "; comment: we don't need to declare the sort Bool" 
    as_tree' (SortDecl RealSort) = return $ Str "; comment: we don't need to declare the sort Real"
    as_tree' (SortDecl s@(Sort _ _ n)) = do
            return $ List [ 
                Str "declare-sort",
                Str (z3_name s),
                Str $ show n ]
    as_tree' (SortDecl s@(DefSort _ _ xs def)) = do
            def' <- as_tree' def 
            return $ List 
                [ Str "define-sort"
                , Str (z3_name s)
                , List $ map Str xs
                , def'
                ]
    as_tree' (SortDecl (Datatype xs n alt)) = do
            alt' <- mapM f alt
            return $ List 
                [ Str "declare-datatypes"
                , List $ map Str xs
                , List [List (Str n : alt')] ]
        where
            f (x,[])    = return $ Str x
            f (x,xs)    = do
                ys <- mapM g xs
                return $ List (Str x : ys)
            g (n,t)     = do
                t' <- as_tree' t
                return $ List [Str n, t']
    rewriteM' = id
    
instance TypeSystem t => Tree (AbsVar t) where
    as_tree' (Var vn vt) = do
        t <- as_tree' vt
        return $ List [Str vn, t]
    rewriteM' = id

instance TypeSystem t => Show (AbsVar t) where
    show (Var n t) = n ++ ": " ++ show (as_tree t)

instance TypeSystem t => Show (AbsFun t) where
    show (Fun xs n ts t) = n ++ show xs ++ ": " 
        ++ intercalate " x " (map (show . as_tree) ts)
        ++ " -> " ++ show (as_tree t)

instance (TypeSystem t, IsQuantifier q) => Show (AbsDef t q) where
    show (Def xs n ps t e) = n ++ show xs ++  ": " 
        ++ args ++ show (as_tree t)
        ++ "  =  " ++ show (as_tree e)
        where
            args
                | L.null ps = ""
                | otherwise = intercalate " x " (map (show . as_tree) ps) ++ " -> "

instance Symbol Sort t q where
    decl s = [SortDecl s]

instance Symbol (AbsFun t) t q where
    decl (Fun xs name params ret) = [FunDecl xs name params ret]

instance Symbol (AbsVar t) t q where
    decl (Var name typ)        = [ConstDecl name typ]

instance Symbol (AbsDef t q) t q where
    decl (Def xs name ps typ ex)  = [FunDef xs name ps typ ex]

instance Symbol (AbsContext t q) t q where
    decl (Context sorts cons fun defs _) = -- dums) = 
                concatMap decl (M.elems sorts)
--            ++  concatMap decl (elems (cons `merge` dums)) 
            ++  concatMap decl (M.elems cons) 
            ++  concatMap decl (M.elems fun) 
            ++  concatMap decl (M.elems defs) 

instance (NFData t, NFData q) => NFData (AbsDef t q) where
    rnf (Def xs n args t e) = rnf (xs,n,args,t,e)

merge :: (Ord k, Eq a, Show k, Show a)
          => M.Map k a -> M.Map k a -> M.Map k a
merge m0 m1 = M.unionWithKey f m0 m1
    where
        f k x y
            | x == y    = x
            | otherwise = error $ format "conflicting declaration for key {0}: {1} {2}" k x y

merge_all :: (Ord k, Eq a, Show k, Show a)
          => [M.Map k a] -> M.Map k a
merge_all ms = foldl (M.unionWithKey f) M.empty ms
    where
        f k x y
            | x == y    = x
            | otherwise = error $ format "conflicting declaration for key {0}: {1} {2}" k x y

mk_context :: TypeSystem t => [AbsDecl t q] -> AbsContext t q
mk_context (x:xs) = 
        case mk_context xs of
            Context ss vs fs defs dums -> 
                case x of
                    SortDecl s ->
                        Context
                            (M.insert (z3_name s) s ss) vs
                            fs defs dums
                    ConstDecl n t -> 
                        Context 
                            ss (M.insert n (Var n t) vs) 
                            fs defs dums
                    FunDecl gs n ps t -> 
                        Context 
                            ss vs 
                            (M.insert n (Fun gs n ps t) fs)
                            defs dums
                    FunDef gs n ps t e -> 
                        Context 
                            ss vs fs 
                            (M.insert n (Def gs n ps t e) defs) 
                            dums
mk_context [] = empty_ctx

substitute :: (TypeSystem t, IsQuantifier q)
           => M.Map String (AbsExpr t q) 
           -> (AbsExpr t q) -> (AbsExpr t q)
substitute m e = f e
    where
        f e@(Word v) = maybe e id $ M.lookup (name v) m
        f e@(Binder _ vs _ _) = rewrite (substitute $ subst vs) e
        f e = rewrite f e
        subst vs = m M.\\ symbol_table vs

empty_ctx :: AbsContext t q
empty_ctx = Context M.empty M.empty M.empty M.empty M.empty

merge_ctx :: (TypeSystem t, IsQuantifier q)
          => AbsContext t q -> AbsContext t q 
          -> AbsContext t q
merge_ctx (Context ss0 vs0 fs0 ds0 dum0) (Context ss1 vs1 fs1 ds1 dum1) = 
        Context 
            (ss0 `merge` ss1) 
            (vs0 `merge` vs1) 
            (fs0 `merge` fs1) 
            (ds0 `merge` ds1)
            (dum0 `merge` dum1)
merge_all_ctx :: [Context] -> Context
merge_all_ctx cs = Context 
        (merge_all $ map f0 cs) 
        (merge_all $ map f1 cs)
        (merge_all $ map f2 cs)
        (merge_all $ map f3 cs)
        (merge_all $ map f4 cs)
    where
        f0 (Context x _ _ _ _) = x
        f1 (Context _ x _ _ _) = x
        f2 (Context _ _ x _ _) = x
        f3 (Context _ _ _ x _) = x
        f4 (Context _ _ _ _ x) = x

used_var :: (TypeSystem t, IsQuantifier q) => AbsExpr t q -> S.Set (AbsVar t)
used_var (Word v) = S.singleton v
used_var (Binder _ vs r expr) = (used_var expr `S.union` used_var r) `S.difference` S.fromList vs
used_var expr = visit (\x y -> S.union x (used_var y)) S.empty expr

free_vars :: Context -> Expr -> M.Map String Var
free_vars (Context _ _ _ _ dum) e = M.fromList $ f [] e
    where
        f xs (Word v@(Var n _))
            | n `M.member` dum = (n,v):xs
            | otherwise      = xs
        f xs v@(Binder _ vs _ _) = M.toList (M.fromList (visit f xs v) M.\\ symbol_table vs)
        f xs v = visit f xs v

var_decl :: String -> Context -> Maybe Var
var_decl s (Context _ m _ _ d) = 
    M.lookup s m <|> M.lookup s d

used_fun :: (TypeSystem t, IsQuantifier q) => AbsExpr t q -> S.Set (AbsFun t)
used_fun e = visit f s e
    where
        f x y = S.union x (used_fun y)
        s = case e of
                FunApp f _ -> S.singleton f
                -- Const ts n t -> S.singleton $ Fun ts n [] t
                _          -> S.empty

instance TypeSystem t => Named (AbsFun t) where
    name (Fun _ x _ _) = x
    decorated_name f = runReader (decorated_name' f) ProverOutput
    decorated_name' (Fun ts x _ _) = do
            ts' <- mapM z3_decoration' ts
            return $ x ++ concat ts'

instance TypeSystem t => Named (AbsDef t q) where
    name (Def _ x _ _ _) = x
    decorated_name' (Def ts x _ _ _) = do
            ts' <- mapM z3_decoration' ts
            return $ x ++ concat ts'

instance Named (AbsVar t) where
    name (Var x _) = x
    decorated_name' = return . name




used_types :: (TypeSystem t, IsQuantifier q) => AbsExpr t q -> S.Set t
used_types e = visit (flip $ S.union . used_types) (
        case e of
            Binder _ vs e0 e1 -> S.fromList $ type_of e0 : type_of e1 : L.map f vs
            _ -> S.singleton $ type_of e
            ) e
    where
        f (Var _ t) = t

rename :: String -> String -> Expr -> Expr
rename x y e@(Word (Var vn t))
        | vn == x   = Word (Var y t)
        | otherwise = e
rename x y e@(Binder q vs r xp)
        | x `elem` L.map name vs  = e
        | otherwise             = Binder q vs (rename x y r) $ rename x y xp
rename x y e = rewrite (rename x y) e 

instance (NFData t, NFData t', NFData q) => NFData (GenExpr t t' q) where
    rnf (Word x) = rnf x
    rnf (Const n t) = rnf (n,t)
    rnf (Cast x0 x1) = rnf (x0,x1)
    rnf (Lift x0 x1) = rnf (x0,x1)
    rnf (FunApp f args) = rnf (f,args)
    rnf (Binder q vs e0 e1) = rnf (q,vs,e0,e1)

instance NFData Value where
    rnf (RealVal v) = rnf v
    rnf (IntVal v)  = rnf v
