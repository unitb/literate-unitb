{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE OverloadedStrings      #-}
module Logic.Expr.Expr 
    ( module Logic.Expr.Expr
    , module Logic.Expr.Variable
    , HasConstants(..)
    , Loc(..) )
where

    -- Module
import Logic.Expr.Classes
import Logic.Expr.PrettyPrint
import Logic.Expr.Scope
import Logic.Expr.Type
import Logic.Expr.Variable
import Logic.Names

    -- Library
import Control.DeepSeq
import Control.Monad.Reader
import Control.Monad.Identity
import Control.Lens hiding (rewrite,Context,elements
                           ,Const,Context',List,rewriteM
                           ,Traversable1(..))

import           Data.Data
import           Data.List as L
import qualified Data.Map as M
import           Data.Serialize
import qualified Data.Set as S

import Language.Haskell.TH hiding (Type,Name) -- (ExpQ,location,Loc)

import Test.QuickCheck

import Utilities.Format
import Utilities.Functor
import Utilities.Instances
import Utilities.Partial

type Expr = AbsExpr Name GenericType HOQuantifier

type FOExpr = AbsExpr InternalName FOType FOQuantifier

type AbsExpr n t q = GenExpr n t t q

type RawExpr = AbsExpr InternalName Type HOQuantifier

type Expr' = AbsExpr InternalName Type FOQuantifier

type UntypedExpr = GenExpr Name () GenericType HOQuantifier

data GenExpr n t a q = 
        Word (AbsVar n t) 
        | Const Value t
        | FunApp (AbsFun n t) [GenExpr n t a q]
        | Binder q [AbsVar n t] (GenExpr n t a q) (GenExpr n t a q) t
        | Cast (GenExpr n t a q) a
        | Lift (GenExpr n t a q) a
    deriving (Eq,Ord,Typeable,Data,Generic,Show,Functor,Foldable,Traversable)

data Lifting = Unlifted | Lifted
    deriving (Eq,Ord, Generic, Data, Typeable,Show)

instance Serialize Lifting where

data Value = RealVal Double | IntVal Int
    deriving (Eq,Ord,Generic,Typeable,Data,Show)

instance PrettyPrintable Value where
    pretty (RealVal v) = show v
    pretty (IntVal v)  = show v

instance (Arbitrary t,Arbitrary a,Arbitrary n,Arbitrary q,Tree a,TypeSystem t,IsQuantifier q) 
        => Arbitrary (GenExpr n t a q) where
    arbitrary = do
        inductive $ \arb -> 
            [ Word   <$> arbitrary' 
            , Const  <$> arbitrary' <*> arbitrary'
            , FunApp <$> arbitrary' <*> listOf' arb
            , Binder <$> arbitrary' <*> arbitrary' <*> arb <*> arb <*> arbitrary'
            , Cast   <$> arb <*> arbitrary'
            , Lift   <$> arb <*> arbitrary'
            ]

instance Functor1 (GenExpr a b) where
instance Functor2 (GenExpr a) where
instance Functor3 GenExpr where
instance Foldable1 (GenExpr a b) where
instance Foldable2 (GenExpr a) where
instance Foldable3 GenExpr where

instance Traversable1 (GenExpr a b) where
    traverse1 _ (Word v) = pure $ Word v
    traverse1 _ (Const v t) = pure $ Const v t
    traverse1 f (Cast e t) = Cast <$> traverse1 f e <*> f t
    traverse1 f (Lift e t) = Lift <$> traverse1 f e <*> f t
    traverse1 f (FunApp fun e) = FunApp fun <$> (traverse.traverse1) f e
    traverse1 f (Binder a b c d e) = Binder a b <$> traverse1 f c 
                                                <*> traverse1 f d 
                                                <*> pure e
instance Traversable2 (GenExpr a) where
    traverse2 f (Word v) = Word <$> traverse f v
    traverse2 f (Const v t) = Const v <$> f t
    traverse2 f (Cast e t) = Cast <$> traverse2 f e <*> pure t
    traverse2 f (Lift e t) = Lift <$> traverse2 f e <*> pure t
    traverse2 f (FunApp fun e) = FunApp <$> traverse f fun 
                                        <*> (traverse.traverse2) f e
    traverse2 f (Binder a b c d e) = Binder a <$> (traverse.traverse) f b
                                              <*> traverse2 f c 
                                              <*> traverse2 f d
                                              <*> f e
instance Traversable3 GenExpr where
    traverse3 f (Word v) = Word <$> traverse1 f v
    traverse3 _ (Const v t) = pure $ Const v t
    traverse3 f (Cast e t) = Cast <$> traverse3 f e <*> pure t
    traverse3 f (Lift e t) = Lift <$> traverse3 f e <*> pure t
    traverse3 f (FunApp fun e) = FunApp <$> traverse1 f fun <*> (traverse.traverse3) f e
    traverse3 f (Binder a b c d e) = Binder a <$> (traverse.traverse1) f b
                                              <*> traverse3 f c
                                              <*> traverse3 f d
                                              <*> pure e

instance IsName n => Translatable 
        (GenExpr n t a q) 
        (GenExpr InternalName t a q) where
    translate = fmap3 asInternal

make_unique :: (IsGenExpr expr, Name ~ NameT expr)
            => Assert
            -> String               -- suffix to be added to the name of variables
            -> M.Map Name var       -- set of variables that must renamed
            -> expr                 -- expression to rewrite
            -> expr
make_unique arse suf vs = freeVarsOf.namesOf %~ newName
    where
        newName vn | vn `M.member` vs = setSuffix arse suf vn
                   | otherwise        = vn


expSize :: GenExpr n t a q -> Int
expSize (Word _) = 0
expSize (Const _ _)   = 0
expSize (FunApp _ xs) = 1 + sum (map expSize xs)
expSize (Binder _ _ r t _) = 1 + expSize r + expSize t
expSize (Cast e _) = 1 + expSize e
expSize (Lift e _) = 1 + expSize e

instance Arbitrary Value where
    arbitrary = genericArbitrary

instance Arbitrary Lifting where
    arbitrary = genericArbitrary

instance Arbitrary HOQuantifier where
    arbitrary = genericArbitrary

instance Arbitrary QuantifierWD where
    arbitrary = genericArbitrary

instance Arbitrary QuantifierType where
    arbitrary = genericArbitrary

instance (Arbitrary t,Arbitrary n) => Arbitrary (AbsFun n t) where
    arbitrary = genericArbitrary

data QuantifierType = QTConst Type | QTSort Sort | QTFromTerm Sort | QTTerm
    deriving (Eq,Ord,Generic,Typeable,Data,Show)

data QuantifierWD  = FiniteWD | InfiniteWD
    deriving (Eq,Ord,Generic,Typeable,Data,Show)

data HOQuantifier = 
        Forall 
        | Exists 
        | UDQuant Fun Type QuantifierType QuantifierWD
    deriving (Eq,Ord,Generic,Typeable,Data,Show)

data FOQuantifier = FOForall | FOExists 
    deriving (Eq,Ord,Generic,Typeable,Data,Show)

type P = Either [String]

type RawExprP = Either [String] RawExpr 

type ExprP = Either [String] Expr 

type ExprPG n t q = Either [String] (AbsExpr n t q)

type ExprPC e = Either [String] e

class ( TypeSystem (TypeT expr)
      , TypeSystem (AnnotT expr)
      , IsName (NameT expr)
      , IsQuantifier (QuantT expr)
      , Typeable expr
      , VarT expr ~ AbsVar (NameT expr) (TypeT expr)
      , expr ~ GenExpr (NameT expr) (TypeT expr) (AnnotT expr) (QuantT expr)) 
    => IsGenExpr expr where
    type NameT expr :: *
    type TypeT expr :: *
    type AnnotT expr :: *
    type QuantT expr :: *
    type VarT expr :: *
    type FunT expr :: *
    type SetTypeT t expr :: *
    type SetAnnotT t expr :: *
    type SetQuantT t expr :: *

class (IsGenExpr (ExprT expr),Typeable expr) => HasGenExpr expr where
    type ExprT expr :: *
    asExpr :: expr -> ExprT expr
    ztrue :: expr
    zfalse :: expr

instance ( IsName n
         , TypeSystem t0
         , TypeSystem t1
         , IsQuantifier q) 
         => IsGenExpr (GenExpr n t0 t1 q) where
    type VarT (GenExpr n t0 t1 q)   = AbsVar n t0
    type FunT (GenExpr n t0 t1 q)   = AbsFun n t0
    type NameT (GenExpr n t0 t1 q)  = n
    type TypeT (GenExpr n t0 t1 q)  = t0
    type AnnotT (GenExpr n t0 t1 q) = t1
    type QuantT (GenExpr n t0 t1 q) = q
    type SetTypeT arg (GenExpr n t0 t1 q)  = GenExpr n arg t1 q
    type SetAnnotT arg (GenExpr n t0 t1 q) = GenExpr n t0 arg q
    type SetQuantT arg (GenExpr n t0 t1 q) = GenExpr n t0 t1 arg

instance ( IsName n,TypeSystem t0,TypeSystem t1
         , IsQuantifier q)
        => HasGenExpr (GenExpr n t0 t1 q) where
    type ExprT (GenExpr n t0 t1 q)  = GenExpr n t0 t1 q
    asExpr = id
    ztrue  = FunApp (mkConstant "true" bool) []
    zfalse = FunApp (mkConstant "false" bool) []

mkConstant :: (?loc :: CallStack,IsName n) 
           => String -> t -> AbsFun n t
mkConstant n t = mk_fun [] (fromString'' n) [] t

class ( TypeT expr ~ AnnotT expr, IsGenExpr expr )
    => IsAbsExpr expr where

instance (IsName n,TypeSystem t,IsQuantifier q) 
        => IsAbsExpr (AbsExpr n t q) where

var_type :: AbsVar n t -> t
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

ztuple :: (IsName n,TypeSystem t,IsQuantifier q) => [AbsExpr n t q] -> AbsExpr n t q
ztuple []           = unit
ztuple [x]          = x
ztuple [x0,x1]      = pair x0 $ pair x1 unit    -- FunApp (Fun [tx, txs] "pair" [tx, txs] pair_type) [x,tail]
ztuple (x0:x1:xs)   = pair x0 $ ztuple (x1:xs)  -- FunApp (Fun [tx, txs] "pair" [tx, txs] pair_type) [x,tail]

unit :: (TypeSystem t,IsName n) => AbsExpr n t q
unit = FunApp (mkConstant "null" null_type) []

pair :: (IsName n,TypeSystem t, IsQuantifier q) => AbsExpr n t q -> AbsExpr n t q -> AbsExpr n t q
pair x y = FunApp (mk_fun [] (fromString'' "pair") [t0,t1] $ pair_type t0 t1) [x,y]
    where
        t0 = type_of x
        t1 = type_of y

finiteness :: HOQuantifier -> QuantifierWD
finiteness Forall = InfiniteWD
finiteness Exists = InfiniteWD
finiteness (UDQuant _ _ _ fin) = fin

class (Ord q, PrettyPrintable q, Show q, Data q) => IsQuantifier q where
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

freeVarsOf :: IsGenExpr expr
           => Traversal' expr (VarT expr)
freeVarsOf f = freeVarsOf'' (const f) M.empty

freeVarsOf'' :: (IsGenExpr expr, n ~ NameT expr,Applicative f) 
             => (M.Map n (VarT expr) -> VarT expr -> f (VarT expr))
             -> M.Map n (VarT expr)
             -> expr -> f expr
freeVarsOf'' f vs (Word v) | (v^.name) `M.member` vs = pure (Word v)
                           | otherwise       = Word <$> f vs v
freeVarsOf'' f vs e@(Binder _ us _ _ _) = 
        rewriteM (freeVarsOf'' f $ M.union vs $ symbol_table us) e
freeVarsOf'' f vs e = rewriteM (freeVarsOf'' f vs) e

--freeVarsOf' :: (Applicative f,IsName n,TypeSystem t) 
--            => (M.Map n (AbsVar n t) -> AbsVar n t -> f (AbsVar n t))
--            -> M.Map n (AbsVar n t)
--            -> AbsExpr n t q
--            -> f (AbsExpr n t q)
--freeVarsOf' f vs (Word v) | (v^.name) `M.member` vs = Word <$> f vs v
--                          | otherwise       = pure (Word v)
--freeVarsOf' f vs e@(Binder _ us _ _ _) = 
--        rewriteExprM pure pure (freeVarsOf' f $ M.union vs $ symbol_table us) e
--freeVarsOf' f vs e = rewriteM (freeVarsOf' f vs) e
    -- instead of Applicative f => (a -> f b) -> ...
    -- use Applicative f => (a -> ReaderT FreeVars f b)
    -- ReaderT FreeVars f is an applicative functor

varsOf :: IsGenExpr expr
       => Traversal' expr (VarT expr)
varsOf f (Word v) = Word <$> f v
varsOf f t = rewriteM (varsOf f) t

subexprs :: IsGenExpr expr
         => Traversal' expr expr
subexprs = rewriteExprM' pure pure pure

--traverseLeaves :: ( IsQuantifier q, TypeSystem t
--                  , Data leaf, Data t)
--               => Traversal' (AbsExpr t q) leaf
--traverseLeaves f = fix $ \call -> gtraverse (call `castPlus` f)

--castPlus :: (Typeable a,Typeable b,Typeable c,Applicative f)
--      => (a -> f a)
--      -> (b -> f b)
--      -> (c -> f c)
--castPlus f g x = case (eqT' f x,eqT' g x) of
--                    (Just Refl,_) -> f x
--                    (Nothing, Just Refl) -> g x
--                    (Nothing, Nothing) -> pure x
--    where
--        eqT' :: (Typeable a,Typeable b) 
--             => (a -> f a) -> b -> Maybe (a :~: b)
--        eqT' _ _ = eqT

--type VerbExpr = WithTypeInfo Type HOQuantifier

--newtype WithTypeInfo t q = WithTypeInfo { unVerb :: AbsExpr t q }
--    deriving (Eq)

--instance (TypeSystem t, IsQuantifier q) => Show (WithTypeInfo t q) where
--    show = show . unVerb
--    --show (WithTypeInfo e) = pretty_print' $ e & traverseVars %~ renameWithTypes
--    --show (WithTypeInfo e) = show $ e & traverseVars %~ renameWithTypes
--        --where
--        --    renameWithTypes (Var x t) = Var (printf "(%s :: %s)" x (show t)) t
--            --withDec

typesOf :: Traversal (GenExpr n t0 a q) (GenExpr n t1 a q)
                     t0 t1
typesOf = traverse2

typesOf' :: Traversal (AbsExpr n t0 q) (AbsExpr n t1 q)
                      t0 t1
typesOf' f = rewriteExprM f pure (typesOf' f)

instance IsName n => HasNames (GenExpr n t0 t1 q) n where
    type SetNameT n' (GenExpr n t0 t1 q) = GenExpr n' t0 t1 q
    namesOf = traverse3

z3_decoration :: TypeSystem t => t -> String
z3_decoration t = runReader (z3_decoration' t) ProverOutput

z3_decoration' :: TypeSystem t => t -> Reader (OutputMode n) String
z3_decoration' t = do
        opt <- ask 
        case opt of
            ProverOutput -> f <$> as_tree' t
            UserOutput -> return ""
    where
        f (List ys) = format "@Open{0}@Close" xs
            where xs = concatMap f ys :: String
        f (Str y)   = format "@@{0}" y

    -- replace it everywhere (replace what? with what?)
z3_fun_name :: Fun -> InternalName
z3_fun_name (Fun xs ys _ _ _) = fromString'' $ render ys ++ concatMap z3_decoration xs

type Fun = AbsFun Name GenericType

type FOFun = AbsFun InternalName FOType

type InternalFun = AbsFun InternalName Type

data AbsFun n t = Fun 
        { _annotation :: [t]
        , _funName :: n
        , lifted :: Lifting
        , _arguments :: [t]
        , _result :: t }
    deriving (Eq,Ord,Generic,Typeable,Data,Functor,Foldable,Traversable,Show)

instance (Data n,Data t,IsName n,TypeSystem t) => Tree (AbsFun n t) where
    as_tree' f@(Fun _ _ _ argT rT) = List <$> sequenceA
            [ Str  <$> render_decorated f
            , List <$> mapM as_tree' argT 
            , as_tree' rT ]

instance (Data n,IsName n,Data t,Data q,TypeSystem t, IsQuantifier q) => Tree (AbsDef n t q) where
    as_tree' d@(Def _ _ argT rT e) = List <$> sequenceA
            [ Str  <$> render_decorated d
            , List <$> mapM as_tree' argT 
            , as_tree' rT 
            , as_tree' e ]


mk_fun' :: (?loc :: CallStack,IsName n) 
        => [t] -> String -> [t] -> t -> AbsFun n t
mk_fun' ps = mk_fun ps . z3Name

mk_fun :: [t] -> n -> [t] -> t -> AbsFun n t
mk_fun  ps n ts t = Fun ps n Unlifted ts t

mk_lifted_fun :: IsName n => [t] -> n -> [t] -> t -> AbsFun n t
mk_lifted_fun ps n ts t = Fun ps n Lifted ts t

target :: AbsDef n t q -> AbsExpr n t q
target (Def _ _ _ _ e) = e

type FODef = AbsDef InternalName FOType HOQuantifier

type Def = AbsDef Name GenericType HOQuantifier

--type Z3Def = AbsDef MixedDef GenericType HOQuantifier

type Def' = AbsDef InternalName GenericType FOQuantifier

data AbsDef n t q = Def [t] n [AbsVar n t] t (AbsExpr n t q)
    deriving (Eq,Ord,Generic,Typeable,Data,Functor,Foldable,Traversable,Show)

instance HasScope Def where
    scopeCorrect' (Def _tp _n args _t e) = withVars args $ scopeCorrect' e

instance Functor1 (AbsDef n) where
instance Functor2 AbsDef where

instance Foldable1 (AbsDef n) where
instance Foldable2 AbsDef where

instance Traversable1 (AbsDef n) where
    traverse1 f (Def a b c d e) = Def
        <$> traverse f a
        <*> pure b 
        <*> (traverse.traverse) f c 
        <*> f d 
        <*> typesOf' f e
instance Traversable2 AbsDef where
    traverse2 f (Def a b c d e) = Def a 
        <$> f b
        <*> (traverse.traverse1) f c
        <*> pure d 
        <*> traverse3 f e

instance IsName n => HasNames (AbsDef n t q) n where
    type SetNameT m (AbsDef n t q) = AbsDef m t q
    namesOf = traverse2

instance PrettyPrintable HOQuantifier where
    pretty Forall = "forall"
    pretty Exists = "exists"
    pretty (UDQuant f _ _ _) = render $ f^.name

instance PrettyPrintable FOQuantifier where
    pretty FOForall = "forall"
    pretty FOExists = "exists"

instance Arbitrary Def where
    arbitrary = genericArbitrary

z3Def :: (?loc :: CallStack) 
      => [Type] 
      -> String
      -> [Var] -> Type -> Expr
      -> Def
z3Def ts n = Def ts (z3Name n)

instance (Arbitrary t,Arbitrary n) => Arbitrary (AbsVar n t) where
    arbitrary = genericArbitrary

isLifted :: AbsFun n t -> Bool
isLifted (Fun _ _ lf _ _) = lf == Lifted

instance (TypeSystem t, IsQuantifier q, Tree t', IsName n) 
        => Tree (GenExpr n t t' q) where
    as_tree' (Cast e t)   = do
        t' <- as_tree' t
        e' <- as_tree' e
        return $ List [Str "as", e', t']
    as_tree' (Lift e t) = do
        t' <- as_tree' t
        e' <- as_tree' e
        return $ List [ List [Str "as", Str "const", t']
                             , e']
    as_tree' (Word (Var xs _))    = return $ Str $ render xs
    as_tree' (Const xs _)         = return $ Str $ pretty xs
    as_tree' (FunApp f@(Fun _ _ _ _ t) [])
            | isLifted f =List <$> sequence   
                               [ List 
                                 <$> (map Str ["_","map"] ++) 
                                 <$> mapM as_tree' [t]
                               , Str <$> render_decorated f
                               ]
            | otherwise  = Str <$> render_decorated f
    as_tree' (FunApp f ts)  = do
        ts' <- mapM as_tree' ts
        f   <- if isLifted f 
            then (List . map Str) 
                            <$> (["_","map"] ++) 
                            <$> mapM render_decorated [f]
            else Str <$> render_decorated f
        return $ List (f : ts')
    as_tree' (Binder q xs r xp _)  = do
        xs' <- mapM as_tree' xs
        r'  <- as_tree' r
        xp' <- as_tree' xp
        return $ List [ Str $ pretty q
                      , List xs'
                      , List 
                          [ merge_range q
                          , r'
                          , xp' ] ]
    rewriteM _ x@(Word _)           = pure x
    rewriteM _ x@(Const _ _)        = pure x
    rewriteM f (Lift e t)    = Lift <$> f e <*> pure t
    rewriteM f (Cast e t)    = Cast <$> f e <*> pure t
    rewriteM f (FunApp g xs) = FunApp g <$> traverse f xs
    rewriteM f (Binder q xs r x t)  = Binder q xs <$> f r <*> f x <*> pure t

rewriteExpr :: (t0 -> t1)
            -> (q0 -> q1)
            -> (AbsExpr n t0 q0 -> AbsExpr n t1 q1)
            -> AbsExpr n t0 q0 -> AbsExpr n t1 q1
rewriteExpr fT fQ fE = runIdentity . rewriteExprM 
        (return . fT) (return . fQ) (return . fE)

rewriteExprM' :: (Applicative m)
              => (t0 -> m t1)
              -> (a0 -> m a1)
              -> (q0 -> m q1)
              -> (GenExpr n t0 a0 q0 -> m (GenExpr n t1 a1 q1))
              -> GenExpr n t0 a0 q0 -> m (GenExpr n t1 a1 q1)
rewriteExprM' fT fA fQ fE e = 
        case e of
            Word v -> Word <$> fvar v
            Const v t -> Const v <$> fT t
            FunApp f args -> 
                FunApp <$> ffun f
                       <*> traverse fE args
            Binder q vs re te t ->
                Binder <$> fQ q 
                       <*> traverse fvar vs 
                       <*> fE re
                       <*> fE te
                       <*> fT t
            Cast e t -> Cast <$> fE e <*> fA t
            Lift e t -> Lift <$> fE e <*> fA t
    where
        ffun (Fun ts n lf targs rt) = 
                Fun <$> traverse fT ts 
                    <*> pure n <*> pure lf
                    <*> traverse fT targs 
                    <*> fT rt
        fvar (Var n t) = Var n <$> fT t

rewriteExprM :: (Applicative m)
             => (t0 -> m t1)
             -> (q0 -> m q1)
             -> (AbsExpr n t0 q0 -> m (AbsExpr n t1 q1))
             -> AbsExpr n t0 q0 -> m (AbsExpr n t1 q1)
rewriteExprM fT = rewriteExprM' fT fT

instance (TypeSystem t, IsQuantifier q,IsName n, Tree t') => PrettyPrintable (GenExpr n t t' q) where
    pretty e = pretty $ runReader (as_tree' e) UserOutput

instance (IsName n,TypeSystem t) => PrettyPrintable (AbsFun n t) where
    pretty (Fun xs n _ ts t) = render n ++ pretty xs ++ ": " 
            ++ args ++ pretty (as_tree t)
        where
            args
                | not $ null ts = intercalate " x " (map (pretty . as_tree) ts) ++ " -> "
                | otherwise     = ""

instance (TypeSystem t, IsQuantifier q, IsName n) => PrettyPrintable (AbsDef n t q) where
    pretty (Def xs n ps t e) = render n ++ showL xs ++  ": " 
        ++ args ++ pretty (as_tree t)
        ++ "  =  " ++ pretty (as_tree e)
        where
            showL [] = ""
            showL xs = pretty xs ++ " "
            args
                | L.null ps = ""
                | otherwise = intercalate " x " (map (pretty . as_tree) ps) ++ " -> "

instance (TypeSystem t) => Typed (AbsFun n t) where
    type TypeOf (AbsFun n t) = t

instance TypeSystem t => Typed (AbsDef n t q) where
    type TypeOf (AbsDef n t q) = t

instance TypeSystem t => Typed (AbsExpr n t q) where
    type TypeOf (AbsExpr n t q) = t

defAsVar :: AbsDef n t q -> Maybe (AbsVar n t)
defAsVar (Def [] n [] t _) = Just $ Var n t
defAsVar _ = Nothing

instance HasScope Expr where
    scopeCorrect' e = do
        let free = symbol_table $ used_var' e
        areVisible [vars,constants] free e

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

substitute :: (TypeSystem t, IsQuantifier q, IsName n)
           => M.Map n (AbsExpr n t q) 
           -> (AbsExpr n t q) -> (AbsExpr n t q)
substitute m e = f e
    where
        f e@(Word v) = maybe e id $ M.lookup (v^.name) m
        f e@(Binder _ vs _ _ _) = rewrite (substitute $ subst vs) e
        f e = rewrite f e
        subst vs = m M.\\ symbol_table vs

used_var :: (TypeSystem t, IsQuantifier q, IsName n, Tree t') 
         => GenExpr n t t' q -> S.Set (AbsVar n t)
used_var (Word v) = S.singleton v
used_var (Binder _ vs r expr _) = (used_var expr `S.union` used_var r) `S.difference` S.fromList vs
used_var expr = visit (\x y -> S.union x (used_var y)) S.empty expr

used_var' :: HasGenExpr expr => expr -> M.Map (NameT (ExprT expr)) (VarT (ExprT expr))
used_var' = symbol_table . S.toList . used_var . asExpr

used_fun :: (TypeSystem t, IsQuantifier q, IsName n) 
         => AbsExpr n t q -> S.Set (AbsFun n t)
used_fun e = visit f s e
    where
        f x y = S.union x (used_fun y)
        s = case e of
                FunApp f _ -> S.singleton f
                -- Const ts n t -> S.singleton $ Fun ts n [] t
                _          -> S.empty

instance HasName (AbsFun n t) n where
    name = to $ \(Fun _ x _ _ _) -> x

instance IsName n => HasNames (AbsFun n t) n where
    type SetNameT n' (AbsFun n t) = AbsFun n' t
    namesOf = traverse1
    --name = to $ \(Fun _ x _ _ _) -> x

instance (IsName n,TypeSystem t) => Named (AbsFun n t) where
    type NameOf (AbsFun n t) = n
    decorated_name' (Fun ts x _ _ _) = do
            ts' <- mapM z3_decoration' ts
            let suf = concat ts'
            onInternalName (addSuffix suf) 
                $ adaptName x

instance HasName (AbsDef n t q) n where
    name = to $ \(Def _ x _ _ _) -> x

instance (TypeSystem t,IsName n,Typeable q) => Named (AbsDef n t q) where
    type NameOf (AbsDef n t q) = n
    decorated_name' (Def ts x _ _ _) = do
            ts' <- mapM z3_decoration' ts
            let suf = concat ts'
            onInternalName (addSuffix suf) 
                $ adaptName x

used_types :: (TypeSystem t,IsQuantifier q,IsName n) 
           => AbsExpr n t q -> S.Set t
used_types e = visit (flip $ S.union . used_types) (
        case e of
            Binder _ vs e0 e1 t -> S.fromList $ t : type_of e0 : type_of e1 : L.map f vs
            _ -> S.singleton $ type_of e
            ) e
    where
        f (Var _ t) = t

rename :: (TypeSystem t, IsQuantifier q, IsName n) 
       => n -> n
       -> AbsExpr n t q -> AbsExpr n t q
rename x y e@(Word (Var vn t))
        | vn == x   = Word (Var y t)
        | otherwise = e
rename x y e@(Binder q vs r xp t)
        | x `elem` L.map (view name) vs  = e
        | otherwise             = Binder q vs (rename x y r) (rename x y xp) t
rename x y e = rewrite (rename x y) e 

primeOnly :: M.Map Name var -> Expr -> Expr
primeOnly vs = freeVarsOf %~ pr
    where
        pr v | (v^.name) `M.member` vs = prime v
             | otherwise               = v

defExpr :: Lens' (AbsDef n t q) (AbsExpr n t q) 
defExpr f (Def ps n args rt e) = Def ps n args rt <$> f e


class (IsGenExpr e
        , Show e, Eq e
        --, HasScope e
        , NameT e ~ Name
        , TypeT e ~ Type
        , AnnotT e ~ Type
        , QuantT e ~ HOQuantifier )
        => IsExpr e where

class (IsGenExpr e
        , Show e, Eq e
        --, HasScope e
        , NameT e ~ InternalName
        , TypeT e ~ Type
        , AnnotT e ~ Type
        , QuantT e ~ HOQuantifier )
        => IsRawExpr e where

getExpr :: HasExpr e => e 
        -> AbsExpr (NameT (ExprT e)) Type HOQuantifier
getExpr = asExpr

class (HasGenExpr e,Show e,Eq e,IsExpr (ExprT e),HasScope e) => HasExpr e where
class (HasGenExpr e,IsRawExpr (ExprT e),HasScope e) => HasRawExpr e where

instance IsRawExpr (AbsExpr InternalName Type HOQuantifier) where
instance IsExpr (AbsExpr Name Type HOQuantifier) where
--instance HasRawExpr (AbsExpr InternalName Type HOQuantifier) where
instance HasExpr (AbsExpr Name Type HOQuantifier) where
    --getExpr = id

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


instance (NFData t,NFData n) => NFData (AbsFun n t) where
instance NFData QuantifierType
instance NFData QuantifierWD
instance NFData Lifting
instance (NFData t,NFData q,NFData n) => NFData (AbsDef n t q)
instance (NFData t,NFData n) => NFData (AbsVar n t)
instance NFData Value
instance (NFData t0,NFData t1,NFData q,NFData n) => NFData (GenExpr n t0 t1 q)
instance NFData FOQuantifier
instance NFData HOQuantifier

makeLenses ''AbsFun
makePrisms ''GenExpr

instance Functor1 AbsFun where
instance Foldable1 AbsFun where
instance Traversable1 AbsFun where
    traverse1 = funName

fromEither :: Loc -> Either [String] a -> a
fromEither _ (Right x)  = x
fromEither loc (Left msg) = error $ unlines $ map (format "\n{0}\n{1}" loc') msg
    where
        loc' :: String
        loc' = locMsg loc


typeCheck :: ExpQ
typeCheck = withLoc 'fromEither

