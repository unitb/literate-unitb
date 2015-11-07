{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE TypeFamilies           #-}
module Logic.Expr.Expr 
    ( Expr, Expr', AbsExpr, GenExpr (..), FOExpr
    , UntypedExpr, ExprP, ExprPG, ExprPC
    , Value(..)
    , HOQuantifier(..)
    , FOQuantifier(..)
    , QuantifierType(..)
    , QuantifierWD(..)
    , Context', Context, FOContext, AbsContext(..)
    , Decl, FODecl, AbsDecl(..)
    , Fun, FOFun, AbsFun(..)
    , Var, FOVar, AbsVar(..), UntypedVar
    , Def, FODef, Def', AbsDef(..)
    , IsQuantifier(..)
    , IsExpr(..)
    , IsGenExpr(..)
    , Lifting(..)
    , HasExprs(..)
    , HasSymbols(..)
    , type_of, var_type
    , merge, merge_all
    , merge_ctx, merge_all_ctx
    , mk_context, empty_ctx
    , mk_fun, mk_lifted_fun
    , isLifted
    , used_var, used_var'
    , used_fun, used_types
    , substitute, rename
    , z3_fun_name
    , z3_decoration
    , array
    , decl, Symbol
    , ztuple_type, ztuple
    , fun_type, fun_sort
    , bool
    , maybe_type
    , pair, pair_type, pair_sort
    , free_vars
    , var_decl
    , target
    , finiteness
    , typeCheck, withLoc, locMsg
    , rewriteExpr, rewriteExprM
    , defsAsVars, defAsVar
        -- Lenses
    , funName, arguments
    , result, annotation
    , _Word, _Const, _FunApp
    , _Binder, _Cast, _Lift
    , HasAbsContext(..)
    , HasConstants(..)
    , HasSorts(..)
    , HasDummies(..)
    )
where

    -- Module
import Logic.Expr.Label
import Logic.Expr.Classes
import Logic.Expr.Scope
import Logic.Expr.Type
import Logic.Expr.Variable

    -- Library
import           GHC.Generics hiding (to)

import Control.Arrow
import Control.Applicative hiding (Const) -- ((<|>),(<$>),(<*>),many)
import Control.DeepSeq
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Identity
import Control.Lens hiding (rewrite,Context
                           ,Const,Context',List)

import           Data.Data
import           Data.DeriveTH
import           Data.List as L
import qualified Data.Map as M
import           Data.Serialize
import qualified Data.Set as S

import Language.Haskell.TH hiding (Type) -- (ExpQ,location,Loc)

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
        | Binder q [AbsVar t] (GenExpr t a q) (GenExpr t a q) t
        | Cast (GenExpr t a q) a
        | Lift (GenExpr t a q) a
    deriving (Eq, Ord, Typeable, Data, Generic)

data Lifting = Unlifted | Lifted
    deriving (Eq,Ord, Generic, Data, Typeable)

instance Serialize Lifting where

data Value = RealVal Double | IntVal Int
    deriving (Eq,Ord,Generic,Typeable,Data)

instance Show Value where
    show (RealVal v) = show v
    show (IntVal v)  = show v

data QuantifierType = QTConst Type | QTSort Sort | QTFromTerm Sort | QTTerm
    deriving (Eq,Ord,Generic,Typeable,Data)

data QuantifierWD  = FiniteWD | InfiniteWD
    deriving (Eq,Ord,Generic,Typeable,Data)

data HOQuantifier = 
        Forall 
        | Exists 
        | UDQuant Fun Type QuantifierType QuantifierWD
    deriving (Eq,Ord,Generic,Typeable,Data)

data FOQuantifier = FOForall | FOExists 
    deriving (Eq,Ord,Generic,Typeable,Data)

type ExprP = Either [String] Expr 

type ExprPG t q = Either [String] (AbsExpr t q)

type ExprPC e = Either [String] e

class ( TypeSystem (TypeT expr)
      , TypeSystem (AnnotT expr)
      , GenExpr (TypeT expr) (AnnotT expr) (QuantT expr) ~ ExprT expr) 
    => IsGenExpr expr where
    type TypeT expr :: *
    type AnnotT expr :: *
    type QuantT expr :: *
    type ExprT expr :: *
    asExpr :: expr -> ExprT expr
    ztrue :: expr
    zfalse :: expr

instance ( TypeSystem t0
         , TypeSystem t1
         , IsQuantifier q) 
         => IsGenExpr (GenExpr t0 t1 q) where
    type TypeT (GenExpr t0 t1 q)  = t0
    type AnnotT (GenExpr t0 t1 q) = t1
    type QuantT (GenExpr t0 t1 q) = q
    type ExprT (GenExpr t0 t1 q)  = GenExpr t0 t1 q
    asExpr = id
    ztrue  = FunApp (mk_fun [] "true" [] bool) []
    zfalse = FunApp (mk_fun [] "false" [] bool) []

class ( TypeT expr ~ AnnotT expr, IsGenExpr expr )
    => IsAbsExpr expr where

instance (TypeSystem t,IsQuantifier q) => IsAbsExpr (AbsExpr t q) where

var_type :: AbsVar t -> t
var_type (Var _ t) = t

type_of :: (IsAbsExpr expr) => expr -> TypeT expr
type_of e = aux $ asExpr e
    where
        aux (Word (Var _ t))         = t
        aux (Const _ t)              = t
        aux (Cast _ t)               = t
        aux (Lift _ t)               = t
        aux (FunApp (Fun _ _ _ _ t) _) = t
        aux (Binder _ _ _ _ t)   = t

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

unit :: TypeSystem t => AbsExpr t q
unit = FunApp (mk_fun [] "null" [] null_type) []

pair :: (TypeSystem t, IsQuantifier q) => AbsExpr t q -> AbsExpr t q -> AbsExpr t q
pair x y = FunApp (mk_fun [] "pair" [t0,t1] $ pair_type t0 t1) [x,y]
    where
        t0 = type_of x
        t1 = type_of y

finiteness :: HOQuantifier -> QuantifierWD
finiteness Forall = InfiniteWD
finiteness Exists = InfiniteWD
finiteness (UDQuant _ _ _ fin) = fin

class (Eq q, Show q, Data q) => IsQuantifier q where
    merge_range :: q -> StrList
    termType :: q -> Type
    exprType :: q -> Type -> Type -> Type
    qForall :: q
    qExists :: q    

instance IsQuantifier HOQuantifier where
    merge_range Forall = Str "=>"
    merge_range Exists = Str "and"
    merge_range (UDQuant _ _ _ _) = Str "PRE"
    termType Forall = bool
    termType Exists = bool
    termType (UDQuant _ t _ _) = t
    exprType Forall _ _ = bool
    exprType Exists _ _ = bool
    exprType (UDQuant _ _ (QTConst t) _) _ _ = t
    exprType (UDQuant _ _ (QTSort s) _) arg term = make_type s [arg,term]
    exprType (UDQuant _ _ (QTFromTerm s) _) _ term = make_type s [term]
    exprType (UDQuant _ _ QTTerm _) _ term = term
    qForall = Forall
    qExists = Exists


instance IsQuantifier FOQuantifier where
    merge_range FOForall = Str "=>"
    merge_range FOExists   = Str "and"
    termType FOForall = bool
    termType FOExists = bool
    exprType FOForall _ _ = bool
    exprType FOExists _ _ = bool
    qForall = FOForall
    qExists = FOExists

type Context = AbsContext GenericType HOQuantifier

type Context' = AbsContext GenericType FOQuantifier

type FOContext = AbsContext FOType FOQuantifier

class Symbol a t q where
    decl :: a -> [AbsDecl t q]

instance Symbol (AbsVar t) t q where
    decl (Var name typ)        = [ConstDecl name typ]

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

    -- replace it everywhere
z3_fun_name :: Fun -> String
z3_fun_name (Fun xs ys _ _ _) = ys ++ concatMap z3_decoration xs

type Decl = AbsDecl GenericType

type FODecl = AbsDecl FOType

data AbsDecl t q = 
        FunDecl [t] String [t] t
        | ConstDecl String t
        | FunDef [t] String [AbsVar t] t (AbsExpr t q)
        | SortDecl Sort

type Fun = AbsFun GenericType

type FOFun = AbsFun FOType

data AbsFun t = Fun 
        { _annotation :: [t]
        , _funName :: String
        , lifted :: Lifting
        , _arguments :: [t]
        , _result :: t }
    deriving (Eq, Ord, Generic, Typeable, Data)

instance (Data t,TypeSystem t) => Tree (AbsFun t) where
    as_tree' f@(Fun _ _ _ argT rT) = List <$> sequenceA
            [ Str <$> decorated_name' f 
            , List <$> mapM as_tree' argT 
            , as_tree' rT ]

instance (Data t,Data q,TypeSystem t, IsQuantifier q) => Tree (AbsDef t q) where
    as_tree' d@(Def _ _ argT rT e) = List <$> sequenceA
            [ Str <$> decorated_name' d 
            , List <$> mapM as_tree' argT 
            , as_tree' rT 
            , as_tree' e ]

mk_fun :: [t] -> String -> [t] -> t -> AbsFun t
mk_fun ps n ts t = Fun ps n Unlifted ts t

mk_lifted_fun :: [t] -> String -> [t] -> t -> AbsFun t
mk_lifted_fun ps n ts t = Fun ps n Lifted ts t

target :: AbsDef t q -> AbsExpr t q
target (Def _ _ _ _ e) = e

type FODef = AbsDef FOType HOQuantifier

type Def = AbsDef GenericType HOQuantifier

type Def' = AbsDef GenericType FOQuantifier

data AbsDef t q = Def [t] String [AbsVar t] t (AbsExpr t q)
    deriving (Eq,Ord,Generic,Typeable,Data)

instance Show HOQuantifier where
    show Forall = "forall"
    show Exists = "exists"
    show (UDQuant f _ _ _) = f^.name

instance Show FOQuantifier where
    show FOForall = "forall"
    show FOExists = "exists"

isLifted :: AbsFun t -> Bool
isLifted (Fun _ _ lf _ _) = lf == Lifted

instance (TypeSystem t, IsQuantifier q, Tree t') 
        => Tree (GenExpr t t' q) where
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
    as_tree' (Const xs _)         = return $ Str $ show xs
    as_tree' (FunApp f@(Fun _ _ _ _ t) [])
            | isLifted f =List <$> sequence   
                               [ List 
                                 <$> (map Str ["_","map"] ++) 
                                 <$> mapM as_tree' [t]
                               , Str <$> decorated_name' f
                               ]
            | otherwise  = Str <$> decorated_name' f
    as_tree' (FunApp f ts)  = do
        ts' <- mapM as_tree' ts
        f   <- if isLifted f 
            then (List . map Str) 
                            <$> (["_","map"] ++) 
                            <$> mapM decorated_name' [f]
            else Str <$> decorated_name' f
        return $ List (f : ts')
    as_tree' (Binder q xs r xp _)  = do
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
    rewriteM' f s0 (FunApp g xs)  = do
            (s1,ys) <- fold_mapM f s0 xs
            return (s1,FunApp g ys)
    rewriteM' f s0 (Binder q xs r0 x t)  = do
            (s1,r1) <- f s0 r0
            (s2,y)  <- f s1 x
            return (s2,Binder q xs r1 y t)

rewriteExpr :: (t0 -> t1)
            -> (q0 -> q1)
            -> (AbsExpr t0 q0 -> AbsExpr t1 q1)
            -> AbsExpr t0 q0 -> AbsExpr t1 q1
rewriteExpr fT fQ fE = runIdentity . rewriteExprM 
        (return . fT) (return . fQ) (return . fE)

rewriteExprM :: (Applicative m, Monad m)
             => (t0 -> m t1)
             -> (q0 -> m q1)
             -> (AbsExpr t0 q0 -> m (AbsExpr t1 q1))
             -> AbsExpr t0 q0 -> m (AbsExpr t1 q1)
rewriteExprM fT fQ fE e = 
        case e of
            Word v -> Word <$> fvar v
            Const v t -> Const v <$> fT t
            FunApp f args -> 
                FunApp <$> ffun f
                       <*> mapM fE args
            Binder q vs re te t ->
                Binder <$> fQ q 
                       <*> mapM fvar vs 
                       <*> fE re
                       <*> fE te
                       <*> fT t
            Cast e t -> Cast <$> fE e <*> fT t
            Lift e t -> Lift <$> fE e <*> fT t
    where
        ffun (Fun ts n lf targs rt) = 
                Fun <$> mapM fT ts 
                    <*> pure n <*> pure lf
                    <*> mapM fT targs 
                    <*> fT rt
        fvar (Var n t) = Var n <$> fT t

instance (TypeSystem t, IsQuantifier q, Tree t') => Show (GenExpr t t' q) where
    show e = show $ runReader (as_tree' e) UserOutput

instance HasName (AbsDecl t q) String where
    name = to $ \case 
        (FunDecl _ n _ _)  -> n
        (ConstDecl n _)    -> n
        (FunDef _ n _ _ _) -> n
        (SortDecl s)       -> s^.name

instance TypeSystem t => Named (AbsDecl t q) where
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
    
instance TypeSystem t => Show (AbsFun t) where
    show (Fun xs n _ ts t) = n ++ show xs ++ ": " 
            ++ args ++ show (as_tree t)
        where
            args
                | not $ null ts = intercalate " x " (map (show . as_tree) ts) ++ " -> "
                | otherwise     = ""

instance (TypeSystem t, IsQuantifier q) => Show (AbsDef t q) where
    show (Def xs n ps t e) = n ++ showL xs ++  ": " 
        ++ args ++ show (as_tree t)
        ++ "  =  " ++ show (as_tree e)
        where
            showL [] = ""
            showL xs = show xs ++ " "
            args
                | L.null ps = ""
                | otherwise = intercalate " x " (map (show . as_tree) ps) ++ " -> "

instance (TypeSystem t) => Typed (AbsFun t) where
    type TypeOf (AbsFun t) = t

instance TypeSystem t => Typed (AbsDef t q) where
    type TypeOf (AbsDef t q) = t

instance TypeSystem t => Typed (AbsExpr t q) where
    type TypeOf (AbsExpr t q) = t

data AbsContext t q = Context
        { _absContextSorts :: M.Map String Sort
        , _absContextConstants :: M.Map String (AbsVar t)
        , _functions :: M.Map String (AbsFun t)
        , _definitions :: M.Map String (AbsDef t q)
        , _absContextDummies :: M.Map String (AbsVar t)
        }
    deriving (Show,Eq,Generic,Typeable)

makeFields ''AbsContext
makeClassy ''AbsContext

defAsVar :: AbsDef t q -> Maybe (AbsVar t)
defAsVar (Def [] n [] t _) = Just $ Var n t
defAsVar _ = Nothing

defsAsVars :: AbsContext t q -> AbsContext t q
defsAsVars = execState $ do
        defs <- uses definitions $ M.mapMaybe defAsVar
        constants %= M.union defs

instance HasScope Expr where
    scopeCorrect' e = do
        areVisible [vars,constants] (used_var' e) e

class HasSymbols a b | a -> b where
    symbols :: a -> M.Map String b

instance HasSymbols (AbsContext t q) () where
    symbols ctx = M.unions [f a,f b,f c]
        where
            (Context _ a b c _) = ctx^.absContext
            f = M.map (const ())

instance Symbol Sort t q where
    decl s = [SortDecl s]

instance Symbol (AbsFun t) t q where
    decl (Fun xs name Unlifted params ret) = [FunDecl xs name params ret]
    decl _ = error "Symbol.decl: cannot declare lifted functions"

instance Symbol (AbsDef t q) t q where
    decl (Def xs name ps typ ex)  = [FunDef xs name ps typ ex]

instance Symbol (AbsContext t q) t q where
    decl (Context sorts cons fun defs _) = -- dums) = 
                concatMap decl (M.elems sorts)
--            ++  concatMap decl (elems (cons `merge` dums)) 
            ++  concatMap decl (M.elems cons) 
            ++  concatMap decl (M.elems fun) 
            ++  concatMap decl (M.elems defs) 

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
                            (M.insert n (Fun gs n Unlifted ps t) fs)
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
        f e@(Word v) = maybe e id $ M.lookup (v^.name) m
        f e@(Binder _ vs _ _ _) = rewrite (substitute $ subst vs) e
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
used_var (Binder _ vs r expr _) = (used_var expr `S.union` used_var r) `S.difference` S.fromList vs
used_var expr = visit (\x y -> S.union x (used_var y)) S.empty expr

used_var' :: IsExpr expr => expr -> M.Map String Var
used_var' = symbol_table . S.toList . used_var . asExpr

free_vars :: Context -> Expr -> M.Map String Var
free_vars (Context _ _ _ _ dum) e = M.fromList $ f [] e
    where
        f xs (Word v@(Var n _))
            | n `M.member` dum = (n,v):xs
            | otherwise      = xs
        f xs v@(Binder _ vs _ _ _) = M.toList (M.fromList (visit f xs v) M.\\ symbol_table vs)
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

instance HasName (AbsFun t) String where
    name = to $ \(Fun _ x _ _ _) -> x

instance TypeSystem t => Named (AbsFun t) where
    decorated_name f = runReader (decorated_name' f) ProverOutput
    decorated_name' (Fun ts x _ _ _) = do
            ts' <- mapM z3_decoration' ts
            return $ x ++ concat ts'

instance HasName (AbsDef t q) String where
    name = to $ \(Def _ x _ _ _) -> x

instance TypeSystem t => Named (AbsDef t q) where
    decorated_name' (Def ts x _ _ _) = do
            ts' <- mapM z3_decoration' ts
            return $ x ++ concat ts'

used_types :: (TypeSystem t, IsQuantifier q) => AbsExpr t q -> S.Set t
used_types e = visit (flip $ S.union . used_types) (
        case e of
            Binder _ vs e0 e1 t -> S.fromList $ t : type_of e0 : type_of e1 : L.map f vs
            _ -> S.singleton $ type_of e
            ) e
    where
        f (Var _ t) = t

rename :: (TypeSystem t, IsQuantifier q) 
       => String -> String 
       -> AbsExpr t q -> AbsExpr t q
rename x y e@(Word (Var vn t))
        | vn == x   = Word (Var y t)
        | otherwise = e
rename x y e@(Binder q vs r xp t)
        | x `elem` L.map (view name) vs  = e
        | otherwise             = Binder q vs (rename x y r) (rename x y xp) t
rename x y e = rewrite (rename x y) e 

defExpr :: Lens' (AbsDef t q) (AbsExpr t q) 
defExpr f (Def ps n args rt e) = Def ps n args rt <$> f e


class (IsGenExpr e
        , Show e, Eq e
        , HasScope e
        , TypeT e ~ GenericType
        , AnnotT e ~ GenericType
        , QuantT e ~ HOQuantifier)
        => IsExpr e where
    getExpr :: e -> Expr

instance IsExpr Expr where
    getExpr = id

class HasExprs a expr where
    traverseExprs :: Traversal' a expr

instance HasExprs (AbsContext t q) (AbsExpr t q) where
    traverseExprs = definitions.traverse.defExpr

--class ( IsGenExpr expr
--         , TypeT expr ~ GenericType
--         , AnnotT expr ~ GenericType
--         , QuantT expr ~ HOQuantifier)
--    => IsExpr expr

--instance ( IsGenExpr expr
--         , TypeT expr ~ GenericType
--         , AnnotT expr ~ GenericType
--         , QuantT expr ~ HOQuantifier)
--    => IsExpr expr


derive makeNFData ''AbsFun
derive makeNFData ''QuantifierType
derive makeNFData ''QuantifierWD
derive makeNFData ''Lifting
derive makeNFData ''AbsDef
derive makeNFData ''AbsVar
derive makeNFData ''Value
derive makeNFData ''GenExpr
derive makeNFData ''AbsDecl
derive makeNFData ''AbsContext
derive makeNFData ''FOQuantifier
derive makeNFData ''HOQuantifier

makeLenses ''AbsFun
makePrisms ''GenExpr

fromEither :: Loc -> Either [String] a -> a
fromEither _ (Right x)  = x
fromEither loc (Left msg) = error $ unlines $ map (format "\n{0}\n{1}" loc') msg
    where
        loc' :: String
        loc' = locMsg loc


typeCheck :: ExpQ
typeCheck = withLoc 'fromEither

locMsg :: Loc -> String
locMsg loc = format "{0}:{1}:{2}" (loc_filename loc) (fst $ loc_start loc) (snd $ loc_end loc)

withLoc :: Name -> ExpQ
withLoc fun = do
    loc <- location
    let litS f = LitE $ StringL $ f loc
        litP f = TupE [LitE $ IntegerL x, LitE $ IntegerL y]
            where
                (x,y) = (toInteger *** toInteger) (f loc)
    let e = AppE (VarE fun)  
            (RecConE 'Loc
                [ ('loc_filename,litS loc_filename)
                , ('loc_package,litS loc_package)
                , ('loc_module,litS loc_module)
                , ('loc_start,litP loc_start)
                , ('loc_end,litP loc_end) ])
    return e
