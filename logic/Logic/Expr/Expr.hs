{-# LANGUAGE TypeFamilies #-}
module Logic.Expr.Expr 
    ( module Logic.Expr.Expr
    , module Logic.Expr.Fun
    , module Logic.Expr.Quantifier
    , module Logic.Expr.Variable
    , HasConstants(..)
    , Loc(..) )
where

    -- Module
import Logic.Expr.Classes
import Logic.Expr.Fun
import Logic.Expr.PrettyPrint
import Logic.Expr.Scope
import Logic.Expr.Quantifier
import Logic.Expr.Type
import Logic.Expr.Variable
import Logic.Names

    -- Library
import Control.Applicative hiding (Const)
import Control.DeepSeq
import Control.Monad.Reader
import Control.Monad.Identity
import Control.Lens hiding (rewrite,Context,elements
                           ,Const,Context',List,rewriteM
                           ,Traversable1(..))
import Control.Precondition

import           Data.Data
import           Data.Hashable
import           Data.List as L
import qualified Data.Map.Class as M
import           Data.Serialize
import qualified Data.Set as S

import GHC.Generics hiding (to,from)
import GHC.Generics.Instances

import Language.Haskell.TH hiding (Type,Name) -- (ExpQ,location,Loc)

import Test.QuickCheck
import Test.QuickCheck.ZoomEq

import Text.Printf.TH

import Utilities.Functor
import Utilities.Table

type Expr = AbsExpr Name GenericType HOQuantifier

type FOExpr = AbsExpr InternalName FOType FOQuantifier

type AbsExpr n t q = GenExpr n t t q

type RawExpr = AbsExpr InternalName Type HOQuantifier

type Expr' = AbsExpr InternalName Type FOQuantifier

type UntypedExpr = GenExpr Name () GenericType HOQuantifier

data CastType = Parse | CodeGen
    deriving (Eq,Ord,Typeable,Data,Generic,Show,Enum,Bounded)

data GenExpr n t a q = 
        Word (AbsVar n t) 
        | Record (RecordExpr (GenExpr n t a q))
        | Lit Value t
        | FunApp (AbsFun n a) [GenExpr n t a q]
        | Binder q [AbsVar n t] (GenExpr n t a q) (GenExpr n t a q) t
        | Cast CastType (GenExpr n t a q) a
        | Lift (GenExpr n t a q) a
    deriving (Eq,Ord,Typeable,Data,Generic,Show,Functor,Foldable,Traversable)
type RecFields expr = Table Name expr

data RecordExpr expr =
        RecLit (RecFields expr)
        | RecUpdate expr (RecFields expr)
        | FieldLookup expr Name
    deriving (Eq,Ord,Typeable,Data,Generic,Show,Functor,Foldable,Traversable)

data Value = RealVal Double | IntVal Int
    deriving (Eq,Ord,Generic,Typeable,Data,Show)

instance PrettyPrintable Value where
    pretty (RealVal v) = show v
    pretty (IntVal v)  = show v

instance ZoomEq Value where
    (.==) = (===)

instance ZoomEq CastType where
instance (ZoomEq n,ZoomEq t,ZoomEq a,ZoomEq q) => ZoomEq (GenExpr n t a q) where
instance Arbitrary CastType where
    arbitrary = elements $ enumFromTo minBound maxBound
instance (Arbitrary t,Arbitrary n,Arbitrary a,Arbitrary q,TypeSystem t,IsQuantifier q) 
        => Arbitrary (GenExpr n t a q) where
    arbitrary = do
        inductive $ \arb -> 
            [ Word   <$> arbitrary' 
            , Lit    <$> arbitrary' <*> arbitrary'
            , FunApp <$> arbitrary' <*> listOf' arb
            , Binder <$> arbitrary' <*> arbitrary' <*> arb <*> arb <*> arbitrary'
            , Cast   <$> arbitrary' <*> arb <*> arbitrary'
            , Lift   <$> arb <*> arbitrary'
            , Record <$> (arb & _Wrapped.mapped %~ arbitraryRecord)
            ]
    shrink = genericShrink

arbitraryRecord :: Gen expr
                -> Gen (RecordExpr expr)
arbitraryRecord arb = oneof 
      [ RecLit <$> arbitraryFields arb
      , RecUpdate <$> arb <*> arbitraryFields arb
      , FieldLookup <$> arb <*> arbitrary ]

arbitraryFields :: (Arbitrary k,Ord k)
                => Gen a -> Gen (M.Map k a)
arbitraryFields arb = M.fromList <$> listOf (liftA2 (,) arbitrary arb) 

instance (ZoomEq expr) 
        => ZoomEq (RecordExpr expr) where

instance (Arbitrary expr) => Arbitrary (RecordExpr expr) where
    arbitrary = arbitraryRecord arbitrary
    shrink = genericShrink

instance Functor1 (GenExpr a b) where
instance Functor2 (GenExpr a) where
instance Functor3 GenExpr where
instance Foldable1 (GenExpr a b) where
instance Foldable2 (GenExpr a) where
instance Foldable3 GenExpr where

instance Hashable Value
instance Hashable CastType
instance (Hashable n,Hashable t,Hashable a,Hashable q) 
        => Hashable (GenExpr n t a q) where

instance (Hashable expr) => Hashable (RecordExpr expr) where

{-# INLINE traverseRecExpr #-}
traverseRecExpr :: Traversal (RecordExpr expr) (RecordExpr expr')
                             expr expr'
traverseRecExpr f (RecLit m) = RecLit <$> traverse f m
traverseRecExpr f (RecUpdate x m) = 
      liftA2 RecUpdate (f x) (traverse f m)
traverseRecExpr f (FieldLookup x field) = liftA2 FieldLookup (f x) (pure field)

instance Traversable1 (GenExpr a b) where
    traverse1 _ (Word v) = pure $ Word v
    traverse1 _ (Lit v t)  = pure $ Lit v t
    traverse1 f (Cast b e t) = Cast b <$> traverse1 f e <*> f t
    traverse1 f (Lift e t) = Lift <$> traverse1 f e <*> f t
    traverse1 f (FunApp fun e) = liftA2 FunApp (traverse f fun) ((traverse.traverse1) f e)
    traverse1 f (Binder a b c d e) = Binder a b <$> traverse1 f c 
                                                <*> traverse1 f d 
                                                <*> pure e
    traverse1 f (Record x) = Record <$> traverseRecExpr (traverse1 f) x

instance Traversable2 (GenExpr a) where
    traverse2 f (Word v) = Word <$> traverse f v
    traverse2 f (Lit v t)  = Lit v <$> f t
    traverse2 f (Cast b e t) = Cast b <$> traverse2 f e <*> pure t
    traverse2 f (Lift e t) = Lift <$> traverse2 f e <*> pure t
    traverse2 f (FunApp fun e) = FunApp fun 
                                        <$> (traverse.traverse2) f e
    traverse2 f (Binder a b c d e) = Binder a <$> (traverse.traverse) f b
                                              <*> traverse2 f c 
                                              <*> traverse2 f d
                                              <*> f e
    traverse2 f (Record x) = Record <$> traverseRecExpr (traverse2 f) x

instance Traversable3 GenExpr where
    traverse3 f (Word v) = Word <$> traverse1 f v
    traverse3 _ (Lit v t) = pure $ Lit v t
    traverse3 f (Cast b e t) = Cast b <$> traverse3 f e <*> pure t
    traverse3 f (Lift e t) = Lift <$> traverse3 f e <*> pure t
    traverse3 f (FunApp fun e) = FunApp <$> traverse1 f fun <*> (traverse.traverse3) f e
    traverse3 f (Binder a b c d e) = Binder a <$> (traverse.traverse1) f b
                                              <*> traverse3 f c
                                              <*> traverse3 f d
                                              <*> pure e
    traverse3 f (Record x) = Record <$> traverseRecExpr (traverse3 f) x

instance (IsName n) => Translatable 
        (GenExpr n t a q) 
        (GenExpr InternalName t a q) where
    translate = fmap3 asInternal

make_unique :: (IsGenExpr expr, Name ~ NameT expr,Pre)
            => String               -- suffix to be added to the name of variables
            -> Table Name var       -- set of variables that must renamed
            -> expr                 -- expression to rewrite
            -> expr
make_unique suf vs = freeVarsOf.namesOf %~ newName
    where
        newName vn | vn `M.member` vs = setSuffix suf vn
                   | otherwise        = vn


expSize :: GenExpr n t a q -> Int
expSize (Word _) = 0
expSize (Lit _ _)   = 0
expSize (Record (RecLit m)) = 1 + sum (M.map expSize m)
expSize (Record (RecUpdate e m)) = 1 + expSize e + sum (M.map expSize m)
expSize (Record (FieldLookup e _)) = 1 + expSize e
expSize (FunApp _ xs) = 1 + sum (map expSize xs)
expSize (Binder _ _ r t _) = 1 + expSize r + expSize t
expSize (Cast _ e _) = 1 + expSize e
expSize (Lift e _) = 1 + expSize e

instance Arbitrary Value where
    arbitrary = genericArbitrary
    shrink = genericShrink

type P = Either [String]

type RawExprP = Either [String] RawExpr 

type ExprP = Either [String] Expr 

type ExprP' = Either [String] Expr'

type ExprPG n t q = Either [String] (AbsExpr n t q)

type ExprPC e = Either [String] e

class ( TypeSystem (TypeT expr)
      , TypeSystem (AnnotT expr)
      , IsName (NameT expr)
      , TypeAnnotationPair (TypeT expr) (AnnotT expr)
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
    zword :: VarT (ExprT expr) -> expr

instance ( IsName n
         , TypeSystem a
         , TypeSystem t
         , TypeAnnotationPair t a
         , IsQuantifier q) 
         => IsGenExpr (GenExpr n t a q) where
    type VarT (GenExpr n t a q)   = AbsVar n t
    type FunT (GenExpr n t a q)   = AbsFun n t
    type NameT (GenExpr n t a q)  = n
    type TypeT (GenExpr n t a q)  = t
    type AnnotT (GenExpr n t a q) = a
    type QuantT (GenExpr n t a q) = q
    type SetTypeT arg (GenExpr n t a q)  = GenExpr n arg a q
    type SetAnnotT arg (GenExpr n t a q) = GenExpr n t arg q
    type SetQuantT arg (GenExpr n t a q) = GenExpr n t a arg

true_fun :: (IsName n, TypeSystem t) => AbsFun n t
true_fun = mkConstant "true" bool

false_fun :: (IsName n, TypeSystem t) => AbsFun n t
false_fun = mkConstant "false" bool

instance ( IsName n
         , TypeSystem a
         , TypeSystem t
         , TypeAnnotationPair t a
         , IsQuantifier q)
        => HasGenExpr (GenExpr n t a q) where
    type ExprT (GenExpr n t a q)  = GenExpr n t a q
    asExpr = id
    ztrue  = FunApp true_fun []
    zfalse = FunApp false_fun []
    zword  = Word

class ( IsGenExpr expr, AnnotT expr ~ TypeT expr )
    => IsAbsExpr expr where

instance (IsName n,TypeSystem t,IsQuantifier q) 
        => IsAbsExpr (AbsExpr n t q) where

var_type :: AbsVar n t -> t
var_type (Var _ t) = t


instance ( IsName n,TypeSystem t,TypeSystem a
         , TypeAnnotationPair t a,IsQuantifier q) 
        => Typed (GenExpr n t a q) where
    type TypeOf (GenExpr n t a q) = t
    type_of e = type_of $ aux $ asExpr e
        where
            aux (Word (Var _ t))         = t
            aux (Lit _ t)              = t
            aux (Cast _ _ t)               = strippedType t
            aux (Lift _ t)               = strippedType t
            aux (Record r)               = typeOfRecord r
            aux (FunApp (Fun _ _ _ _ t _) _) = strippedType t
            aux (Binder _ _ _ _ t)   = t

typeOfRecord :: ( TypeSystem t, TypeSystem a
                , TypeAnnotationPair t a
                , IsName n,IsQuantifier q,Pre)
             => RecordExpr (GenExpr n t a q) -> t
typeOfRecord (RecLit m) = recordTypeOfFields m
typeOfRecord (RecUpdate x m) = recordTypeOfFields $ 
              M.map type_of m `M.union` fromJust' (type_of x^?fieldTypes) 
typeOfRecord (FieldLookup x field) = fromJust' (type_of x^?fieldTypes.ix field)

fieldTypes :: TypeSystem t => Prism' t (Table Name t)
fieldTypes =  _FromSort.swapped.below _RecordSort
            . iso (\(ts,m) -> m & unsafePartsOf traverse .~ ts) 
                  (\m -> (M.elems m,() <$ m))

recordTypeOfFields :: (Typed e, t ~ TypeOf e,TypeSystem t) => Table Name e -> t
recordTypeOfFields m = make_type (RecordSort $ () <$ m) $ type_of <$> M.elems m

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

pair :: (IsName n,TypeSystem t,IsQuantifier q) => AbsExpr n t q -> AbsExpr n t q -> AbsExpr n t q
pair x y = FunApp (mk_fun [] (fromString'' "pair") [t0,t1] $ pair_type t0 t1) [x,y]
    where
        t0 = type_of x
        t1 = type_of y

freeVarsOf :: IsGenExpr expr
           => Traversal' expr (VarT expr)
freeVarsOf f = freeVarsOf'' (const f) M.empty

freeVarsOf'' :: (IsGenExpr expr, n ~ NameT expr,Applicative f) 
             => (Table n (VarT expr) -> VarT expr -> f (VarT expr))
             -> Table n (VarT expr)
             -> expr -> f expr
freeVarsOf'' f vs (Word v) | (v^.name) `M.member` vs = pure (Word v)
                           | otherwise       = Word <$> f vs v
freeVarsOf'' f vs e@(Binder _ us _ _ _) = 
        rewriteM (freeVarsOf'' f $ M.union vs $ symbol_table us) e
freeVarsOf'' f vs e = rewriteM (freeVarsOf'' f vs) e

varsOf :: IsGenExpr expr
       => Traversal' expr (VarT expr)
varsOf f (Word v) = Word <$> f v
varsOf f t = rewriteM (varsOf f) t

subexprs :: IsGenExpr expr
         => Traversal' expr expr
subexprs = rewriteExprM' pure pure pure

typesOf :: Traversal (GenExpr n t0 a q) (GenExpr n t1 a q)
                     t0 t1
typesOf = traverse2

typesOf' :: Traversal (AbsExpr n t0 q) (AbsExpr n t1 q)
                      t0 t1
typesOf' f = rewriteExprM f pure (typesOf' f)

instance IsName n => HasNames (GenExpr n t a q) n where
    type SetNameT n' (GenExpr n t a q) = GenExpr n' t a q
    namesOf = traverse3

instance (Data n,IsName n,Data t,Data q,TypeSystem t, IsQuantifier q) => Tree (AbsDef n t q) where
    as_tree' d@(Def _ _ argT rT e) = List <$> sequenceA
            [ Str  <$> render_decorated d
            , List <$> mapM as_tree' argT 
            , as_tree' rT 
            , as_tree' e ]

target :: AbsDef n t q -> AbsExpr n t q
target (Def _ _ _ _ e) = e

type FODef = AbsDef InternalName FOType HOQuantifier

type Def = AbsDef Name GenericType HOQuantifier

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

z3Def :: Pre 
      => [Type] 
      -> String
      -> [Var] -> Type -> Expr
      -> Def
z3Def ts n = Def ts (z3Name n)

lookupFields :: ( IsName n,TypeSystem t,TypeSystem a
                , TypeAnnotationPair t a,IsQuantifier q) 
             => GenExpr n t a q -> Table Name (GenExpr n t a q)
lookupFields e = fromJust' $ type_of e^?fieldTypes.to (imap $ \f _ -> Record $ FieldLookup e f)

instance ( ZoomEq t
         , ZoomEq n
         , ZoomEq q) 
        => ZoomEq (AbsDef n t q) where

instance ( TypeSystem t
         , IsQuantifier q
         , Arbitrary t
         , Arbitrary n
         , Arbitrary q) 
        => Arbitrary (AbsDef n t q) where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance (TypeSystem a, TypeSystem t
         , TypeAnnotationPair t a
         , IsQuantifier q, IsName n)
        => Tree (GenExpr n t a q) where
    as_tree' (Cast CodeGen e t)   = do
        t' <- as_tree' t
        e' <- as_tree' e
        return $ List [Str "as", e', t']
    as_tree' (Cast Parse e _)   = as_tree' e
    as_tree' (Lift e t) = do
        t' <- as_tree' t
        e' <- as_tree' e
        return $ List [ List [ Str "as", Str "const", t']
                             , e']
    as_tree' (Record (RecLit m))  = 
        List <$> liftA2 (:) 
            (pure $ Str $ render (recordName m)) 
            (traverse as_tree' $ M.elems m)
    as_tree' (Record (RecUpdate x m))  = 
        as_tree' (Record $ RecLit $ m `M.union` lookupFields x)
    as_tree' (Record (FieldLookup x field)) =
        List <$> sequenceA [pure $ Str $ render field, as_tree' x]
    as_tree' (Word (Var xs _))    = return $ Str $ render xs
    as_tree' (Lit xs _)         = return $ Str $ pretty xs
    as_tree' (FunApp f@(Fun _ _ _ _ t _) [])
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
    -- {-# INLINE rewriteM #-}
    rewriteM _ x@(Word _)           = pure x
    rewriteM _ x@(Lit _ _)        = pure x
    rewriteM f (Record e)        = Record <$> traverseRecExpr f e
    rewriteM f (Lift e t)    = Lift <$> f e <*> pure t
    rewriteM f (Cast b e t)  = Cast b <$> f e <*> pure t
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
            Lit v t -> Lit v <$> fT t
            FunApp f args -> 
                FunApp <$> ffun f
                       <*> traverse fE args
            Binder q vs re te t ->
                Binder <$> fQ q 
                       <*> traverse fvar vs 
                       <*> fE re
                       <*> fE te
                       <*> fT t
            Cast b e t -> Cast b <$> fE e <*> fA t
            Lift e t -> Lift <$> fE e <*> fA t
            Record e -> Record <$> traverseRecExpr fE e
    where
        ffun (Fun ts n lf targs rt wd) = 
                Fun <$> traverse fA ts 
                    <*> pure n <*> pure lf
                    <*> traverse fA targs 
                    <*> fA rt
                    <*> pure wd
        fvar (Var n t) = Var n <$> fT t

rewriteExprM :: (Applicative m)
             => (t0 -> m t1)
             -> (q0 -> m q1)
             -> (AbsExpr n t0 q0 -> m (AbsExpr n t1 q1))
             -> AbsExpr n t0 q0 -> m (AbsExpr n t1 q1)
rewriteExprM fT = rewriteExprM' fT fT

instance ( TypeSystem a,TypeSystem t
         , TypeAnnotationPair t a
         , IsQuantifier q,IsName n) 
        => PrettyPrintable (GenExpr n t a q) where
    pretty e = pretty $ runReader (as_tree' e) UserOutput

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

instance TypeSystem t => Typed (AbsDef n t q) where
    type TypeOf (AbsDef n t q) = t
    type_of (Def _ _ _ t _) = t


defAsVar :: AbsDef n t q -> Maybe (AbsVar n t)
defAsVar (Def [] n [] t _) = Just $ Var n t
defAsVar _ = Nothing

instance HasScope Expr where
    scopeCorrect' e = do
        let free = used_var' e
        areVisible [vars,constants] free e

{-# SPECIALIZE merge :: (Ord k,Eq a,Show k,Show a) => M.Map k a -> M.Map k a -> M.Map k a #-}
{-# SPECIALIZE merge :: (M.IsKey Table k,Eq a,Show k,Show a) => Table k a -> Table k a -> Table k a #-}
merge :: (M.IsKey map k, Eq a, Show k, Show a,M.IsMap map)
          => map k a -> map k a -> map k a
merge m0 m1 = M.unionWithKey f m0 m1
    where
        f k x y
            | x == y    = x
            | otherwise = error $ [printf|conflicting declaration for key %s: %s %s|] 
                            (show k) (show x) (show y)

merge_all :: (M.IsKey map k, Eq a, Show k, Show a,M.IsMap map)
          => [map k a] -> map k a
merge_all ms = foldl (M.unionWithKey f) M.empty ms
    where
        f k x y
            | x == y    = x
            | otherwise = error $ [printf|conflicting declaration for key %s: %s %s|]
                            (show k) (show x) (show y)

substitute :: (TypeSystem t, IsQuantifier q, IsName n)
           => Table n (AbsExpr n t q) 
           -> (AbsExpr n t q) -> (AbsExpr n t q)
substitute m e = f e
    where
        f e@(Word v) = maybe e id $ M.lookup (v^.name) m
        f e@(Binder _ vs _ _ _) = rewrite (substitute $ subst vs) e
        f e = rewrite f e
        subst vs = m M.\\ symbol_table vs

substitute' :: (TypeSystem t, TypeSystem a, IsQuantifier q, IsName n, TypeAnnotationPair t a)
           => Table n (GenExpr n t a q)
           -> (GenExpr n t a q) -> (GenExpr n t a q)
substitute' m e = f e
    where
        f e@(Word v) = maybe e id $ M.lookup (v^.name) m
        f e@(Binder _ vs _ _ _) = rewrite (substitute' $ subst vs) e
        f e = rewrite f e
        subst vs = m M.\\ symbol_table vs

used_var :: ( TypeSystem a,TypeSystem t
            , TypeAnnotationPair t a
            , IsQuantifier q, IsName n) 
         => GenExpr n t a q -> S.Set (AbsVar n t)
used_var (Word v) = S.singleton v
used_var (Binder _ vs r expr _) = (used_var expr `S.union` used_var r) `S.difference` S.fromList vs
used_var expr = visit (\x y -> S.union x (used_var y)) S.empty expr

used_var' :: HasGenExpr expr => expr -> Table (NameT (ExprT expr)) (VarT (ExprT expr))
used_var' = symbol_table . S.toList . used_var . asExpr

used_fun :: (TypeSystem t, IsQuantifier q, IsName n) 
         => AbsExpr n t q -> S.Set (AbsFun n t)
used_fun e = visit f s e
    where
        f x y = S.union x (used_fun y)
        s = case e of
                FunApp f _ -> S.singleton f
                _          -> S.empty

free_vars' :: HasExpr expr
           => Table Name Var -> expr -> Table Name Var
free_vars' ds e = vs `M.intersection` ds
    where
        vs = used_var' (getExpr e)

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

primeOnly :: Table Name var -> Expr -> Expr
primeOnly vs = freeVarsOf %~ pr
    where
        pr v | (v^.name) `M.member` vs = prime v
             | otherwise               = v

defExpr :: Lens' (AbsDef n t q) (AbsExpr n t q) 
defExpr f (Def ps n args rt e) = Def ps n args rt <$> f e

funOf :: (TypeSystem t, IsQuantifier q, IsName n) 
      => AbsDef n t q -> AbsFun n t
funOf (Def ps n args rt _e) = Fun ps n Unlifted (map type_of args) rt InfiniteWD

class (IsGenExpr e
        , Show e
        , PrettyPrintable e, Eq e
        , NameT e ~ Name
        , TypeT e ~ Type
        , AnnotT e ~ Type
        , QuantT e ~ HOQuantifier )
        => IsExpr e where

class (IsGenExpr e
        , Show e
        , PrettyPrintable e, Eq e
        , NameT e ~ InternalName
        , TypeT e ~ Type
        , AnnotT e ~ Type
        , QuantT e ~ HOQuantifier )
        => IsRawExpr e where

getExpr :: HasExpr e => e 
        -> AbsExpr (NameT (ExprT e)) Type HOQuantifier
getExpr = asExpr

class (HasGenExpr e,Show e,PrettyPrintable e,Eq e,IsExpr (ExprT e),HasScope e) => HasExpr e where
class (HasGenExpr e,IsRawExpr (ExprT e),HasScope e) => HasRawExpr e where

instance IsRawExpr (AbsExpr InternalName Type HOQuantifier) where
instance IsExpr (AbsExpr Name Type HOQuantifier) where
instance HasExpr (AbsExpr Name Type HOQuantifier) where




instance NFData CastType where
instance (NFData t,NFData q,NFData n) => NFData (AbsDef n t q)
instance (NFData t,NFData n) => NFData (AbsVar n t)
instance NFData Value
instance (NFData t,NFData q,NFData n,NFData a) => NFData (GenExpr n t a q)
instance (NFData expr) => NFData (RecordExpr expr)

instance Serialize CastType where
instance (Serialize n,Serialize q,Serialize t,Serialize a)
    => Serialize (GenExpr n t a q) where
instance (Serialize expr)
    => Serialize (RecordExpr expr) where
instance Serialize Value where
instance (Serialize n,Serialize q,Serialize t) 
    => Serialize (AbsDef n t q) where

makePrisms ''GenExpr
makePrisms ''RecordExpr

fromEither :: Loc -> Either [String] a -> a
fromEither _ (Right x)  = x
fromEither loc (Left msg) = error $ unlines $ map ([printf|\n%s\n%s|] loc') msg
    where
        loc' :: String
        loc' = locMsg loc


typeCheck :: ExpQ
typeCheck = withLoc 'fromEither
