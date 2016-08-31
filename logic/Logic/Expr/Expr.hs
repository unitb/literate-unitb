{-# LANGUAGE TypeFamilies,TypeOperators #-}
module Logic.Expr.Expr 
    ( module Logic.Expr.Expr
    , module Logic.Expr.Fun
    , module Logic.Expr.Quantifier
    , module Logic.Expr.Variable
    , HasConstants(..)
    , Loc(..) )
where

    -- Module
import Logic.Expr.Bound
import Logic.Expr.Classes
import Logic.Expr.Fun hiding (Lifting)
import Logic.Expr.PrettyPrint
import Logic.Expr.Scope
import Logic.Expr.Quantifier
import Logic.Expr.Type
import Logic.Expr.Variable
import Logic.Names

    -- Library
import qualified Bound as B

import Control.Applicative hiding (Const)
import Control.Category
import Control.DeepSeq
import qualified Control.Invariant as I
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Control.Lens hiding (rewrite,Context,elements
                           ,Const,Context',List,rewriteM
                           ,Traversable1(..))
import Control.Precondition

import           Data.Bifunctor
import           Data.Bifoldable
import           Data.Bitraversable
import           Data.Constraint
import           Data.Constraint.Lifting
import           Data.Bytes.Serial
import           Data.Data
import           Data.Hashable
import           Data.Hashable.Extras
import           Data.List as L
import qualified Data.Map.Class as M
import           Data.Serialize
import qualified Data.Set as S

import GHC.Generics hiding (to,from)
import GHC.Generics.Instances

import Language.Haskell.TH hiding (Type,Name) -- (ExpQ,location,Loc)

import Prelude hiding ((.),id)
import Prelude.Extras

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

data BoundVar n t a q fun lv v = BoundVar (Scope lv (GenExpr n t a q fun) v) (Scope lv (GenExpr n t a q fun) v)
    deriving (Eq,Ord,Typeable,Generic,Generic1,Show,Functor,Foldable,Traversable)
data CastType = Parse | CodeGen
    deriving (Eq,Ord,Typeable,Data,Generic,Show,Enum,Bounded)

data GenExpr n t a q fun v = 
        Word v
        | Record (RecordExpr (GenExpr n t a q fun v))
        | Lit Value t
        | FunApp fun [GenExpr n t a q fun v] t
        | Binder q (Scoped (BoundVar n t a q fun) (AbsVar n t) v) t
        | Cast (GenExpr n t a q fun v) a
        | Lift (GenExpr n t a q fun v) a
    deriving (Eq,Ord,Typeable,Generic,Generic1,Show,Functor,Foldable,Traversable)
type RecFields expr = Table Field expr

data RecordExpr expr =
        RecLit !(RecFields expr)
        | RecUpdate !expr !(RecFields expr)
        | RecSet !(RecFields expr)
        | FieldLookup !expr !Field
    deriving (Eq,Ord,Typeable,Generic,Generic1,Show,Functor,Foldable,Traversable)

data Value = RealVal !Double | IntVal !Int
    deriving (Eq,Ord,Generic,Typeable,Data,Show)

instance (Eq n,Eq t,Eq a,Eq q,Eq fun) => Eq1 (GenExpr n t a q fun) where
instance (Ord n,Ord t,Ord a,Ord q,Ord fun) => Ord1 (GenExpr n t a q fun) where
instance (Show n,Show t,Show a,Show q,Show fun) => Show1 (GenExpr n t a q fun) where
instance Applicative (GenExpr n t a q fun) where
    pure = Word
    (<*>) = ap
instance Monad (GenExpr n t a q fun) where
    Word x >>= f = f x
instance Bifunctor (BoundVar n t a q fun) where
-- instance Monad (BoundVar n t a q fun lv) where

instance PrettyPrintable Value where
    pretty (RealVal v) = show v
    pretty (IntVal v)  = show v

instance ZoomEq Value where
    (.==) = (I.===)

instance Bifoldable (BoundVar n t a q fun) where
    bifoldMap = bifoldMapDefault
instance Bitraversable (BoundVar n t a q fun) where

instance Lifting ZoomEq (GenExpr n t a q fun)
instance (ZoomEq n,ZoomEq t,ZoomEq a,ZoomEq q,ZoomEq fun,ZoomEq var,ZoomEq lv) 
        => ZoomEq (BoundVar n t a q fun lv var) where
instance (ZoomEq n,ZoomEq t,ZoomEq a,ZoomEq q,ZoomEq fun,ZoomEq var) 
        => ZoomEq (GenExpr n t a q fun var) where
instance Arbitrary (BoundVar n t a q fun lv var) where
instance (Arbitrary t,Arbitrary n,Arbitrary a,Arbitrary q
         ,TypeSystem t,IsQuantifier q,Arbitrary fun,Arbitrary var
         ,IsName n) 
        => Arbitrary (GenExpr n t a q fun var) where
    arbitrary = do
        inductive $ \arb -> 
            [ Word   <$> arbitrary'
            , Lit    <$> arbitrary' <*> arbitrary'
            , funApp <$> arbitrary' <*> listOf' arb <*> arbitrary'
            -- , Binder <$> arbitrary' <*> arbitrary' <*> arb <*> arb <*> arbitrary'
            , Cast   <$> arb <*> arbitrary'
            , Lift   <$> arb <*> arbitrary'
            ]
    shrink = genericShrink

mkRecord :: (TypeSystem t,TypeSystem a,IsName n,IsQuantifier q,TypeAnnotationPair t a) 
         => RecordExpr (GenExpr n t a q) -> Maybe (GenExpr n t a q)
mkRecord (RecLit m) = Just $ Record (RecLit m) (record_type $ type_of <$> m)
mkRecord r@(RecUpdate e m) = Record r . record_type . (M.map type_of m `M.union`) <$> (type_of e^?fieldTypes) 
mkRecord r@(RecSet m) = Just $ Record r $ record_type $ set_type . type_of <$> m
mkRecord r@(FieldLookup e fields) = do
      t <- type_of e^?fieldTypes
      Record r <$> M.lookup fields t

arbitraryRecord :: (RecordExpr expr -> expr)
                -> Gen expr
                -> Gen (RecordExpr expr)
arbitraryRecord mkExpr arb = oneof 
      [ rec
      -- , RecUpdate <$> arb <*> arbitraryFields arb
      , liftA2 FieldLookup (mkExpr <$> rec) arbitrary ]
    where
      recLit = RecLit <$> arbitraryFields arb
      recUpd e = RecUpdate e <$> arbitraryFields arb
      updateOnce = StateT $ fmap ((),) . recUpd . mkExpr
      rec = do
        n <- choose (0,2)
        execStateT (replicateM n updateOnce) =<< recLit

arbitraryFields :: (Arbitrary k,Ord k)
                => Gen a -> Gen (M.Map k a)
arbitraryFields arb = M.fromList <$> fields
    where
      fields = do
          n <- choose (0,3) 
          replicateM n 
              $ liftM2 (,) arbitrary arb

instance (ZoomEq expr) 
        => ZoomEq (RecordExpr expr) where

instance (Arbitrary t,Arbitrary n,Arbitrary a,Arbitrary q,TypeSystem t,IsQuantifier q) 
        => Arbitrary (RecordExpr (GenExpr n t a q)) where
    arbitrary = undefined' -- arbitraryRecord mkRecord arbitrary
    shrink = genericShrink

instance Functor1 (GenExpr a b c d) where
instance Functor2 (GenExpr a b c) where
instance Functor3 (GenExpr a b) where
instance Functor4 (GenExpr a) where
instance Functor5 GenExpr where
instance Foldable1 (GenExpr a b c d) where
instance Foldable2 (GenExpr a b c) where
instance Foldable3 (GenExpr a b) where
instance Foldable4 (GenExpr a) where
instance Foldable5 GenExpr where

instance Hashable Value
instance (Hashable n,Hashable t,Hashable a,Hashable q
         ,Hashable fun,Hashable lv,Hashable var,Ord n,Ord t ) 
        => Hashable (BoundVar n t a q fun lv var) where
instance (Hashable n,Hashable t,Hashable a,Hashable q
         ,Hashable fun,Hashable var,Ord n,Ord t) 
        => Hashable (GenExpr n t a q fun var) where
instance (Hashable n,Hashable t,Hashable a,Hashable q
         ,Hashable fun,Ord n,Ord t) 
        => Hashable1 (GenExpr n t a q fun) where

instance (Hashable expr) => Hashable (RecordExpr expr) where

binder :: q -> [AbsVar n t]
       -> GenExpr n t a q
       -> GenExpr n t a q
       -> t
       -> GenExpr n t a q
binder q = Binder q . evalList

funApp :: AbsFun n a -> [GenExpr n t a q] -> GenExpr n t a q
funApp fun = FunApp fun . evalList

{-# INLINE traverseRecExpr #-}
traverseRecExpr :: Traversal (RecordExpr expr) (RecordExpr expr')
                             expr expr'
traverseRecExpr f (RecLit m) = RecLit <$> traverse f m
traverseRecExpr f (RecSet m) = RecSet <$> traverse f m
traverseRecExpr f (RecUpdate x m) = 
      liftA2 RecUpdate (f x) (traverse f m)
traverseRecExpr f (FieldLookup x field) = liftA2 FieldLookup (f x) (pure field)

instance Traversable1 (GenExpr a b c d) where
    traverse1 _ (Word v)   = pure $ Word v
    traverse1 _ (Lit v t)  = pure $ Lit v t
    traverse1 f (Cast e t) = Cast <$> traverse1 f e <*> pure t
    traverse1 f (Lift e t) = Lift <$> traverse1 f e <*> pure t
    traverse1 f (FunApp fun e t) = liftA3 FunApp (f fun) ((traverse.traverse1) f e) (pure t)
    -- traverse1 f (Binder a b c d e) = Binder a b <$> traverse1 f c 
    --                                             <*> traverse1 f d 
    --                                             <*> pure e
    traverse1 f (Record x t) = Record <$> traverseRecExpr (traverse1 f) x
                                      <*> pure t

instance Traversable2 (GenExpr a b c) where
    traverse2 _ (Word v)   = pure $ Word v
    traverse2 f (Lit v t)  = pure $ Lit v t
    traverse2 f (Cast b e t) = Cast b <$> traverse2 f e <*> pure t
    traverse2 f (Lift e t) = Lift <$> traverse2 f e <*> pure t
    traverse2 f (FunApp fun e t) = FunApp fun 
                                        <$> (traverse.traverse2) f e
                                        <*> pure t
    -- traverse2 f (Binder a b c d e) = Binder a <$> (traverse.traverse) f b
    --                                           <*> traverse2 f c 
    --                                           <*> traverse2 f d
    --                                           <*> f e
    traverse2 f (Record x t) = Record 
          <$> traverseRecExpr (traverse2 f) x
          <*> f t

instance Traversable3 (GenExpr a b) where
instance Traversable4 (GenExpr a) where
instance Traversable5 GenExpr where
    -- traverse3 f (Word v t) = pure $ Word v t
    -- traverse3 _ (Lit v t)  = pure $ Lit v t
    -- traverse3 f (Cast e t) = Cast <$> traverse3 f e <*> f t
    -- traverse3 f (Lift e t) = Lift <$> traverse3 f e <*> f t
    -- traverse3 f (FunApp fun e t) = 
    --      FunApp <$> pure fun 
    --             <*> (traverse.traverse3) f e
    --             <*> pure t
    -- traverse3 f (Binder a b c d e) = Binder a <$> (traverse.traverse1) f b
    --                                           <*> traverse3 f c
    --                                           <*> traverse3 f d
    --                                           <*> pure e
    -- traverse3 f (Record x) = Record <$> traverseRecExpr (traverse3 f) x

-- instance (IsName n) => Translatable 
--         (GenExpr n t a q fun var) 
--         (GenExpr InternalName t a q fun var) where
--     translate = fmap3 asInternal

-- make_unique :: (IsGenExpr expr, Name ~ NameT expr,Pre)
--             => String               -- suffix to be added to the name of variables
--             -> Table Name var       -- set of variables that must renamed
--             -> expr                 -- expression to rewrite
--             -> expr
-- make_unique suf vs = freeVarsOf.namesOf %~ newName
--     where
--         newName vn | vn `M.member` vs = setSuffix suf vn
--                    | otherwise        = vn


expSize :: GenExpr n t a q fun var -> Int
expSize (Word _)  = 0
expSize (Lit _ _) = 0
expSize (Record (RecLit m)) = 1 + sum (M.map expSize m)
expSize (Record (RecUpdate e m)) = 1 + expSize e + sum (M.map expSize m)
expSize (Record (FieldLookup e _)) = 1 + expSize e
expSize (FunApp _ xs _) = 1 + sum (map expSize xs)
-- expSize (Binder _ _ r t _) = 1 + expSize r + expSize t
expSize (Cast _ e _) = 1 + expSize e
expSize (Lift e _) = 1 + expSize e

instance Arbitrary Value where
    arbitrary = genericArbitrary
    shrink = genericShrink

-- type P = Either [String]

-- type RawExprP = Either [String] RawExpr 

-- type ExprP = Either [String] Expr 

-- type ExprP' = Either [String] Expr'

-- type ExprPG n t q = Either [String] (AbsExpr n t q)

-- type ExprPC e = Either [String] e

class ( TypeSystem (TypeT expr)
      , TypeSystem (AnnotT expr)
      , IsName (NameT expr)
      , TypeAnnotationPair (TypeT expr) (AnnotT expr)
      , IsQuantifier (QuantT expr)
      -- , Typeable expr
      -- , VarT expr ~ AbsVar (NameT expr) (TypeT expr)
      , expr ~ GenExpr (NameT expr) (TypeT expr) (AnnotT expr) (QuantT expr) (FunT expr) (VarT expr)) 
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

class (IsGenExpr (ExprT expr)) => HasGenExpr expr where
    type ExprT expr :: *
    asExpr :: expr -> ExprT expr
    ztrue :: expr
    zfalse :: expr
    -- zword :: VarT (ExprT expr) -> expr

instance ( IsName n
         , TypeSystem a
         , TypeSystem t
         -- , Typeable fun
         -- , Typeable var
         , TypeAnnotationPair t a
         , IsQuantifier q) 
         => IsGenExpr (GenExpr n t a q fun var) where
    type VarT (GenExpr n t a q fun var)   = var
    type FunT (GenExpr n t a q fun var)   = fun
    type NameT (GenExpr n t a q fun var)  = n
    type TypeT (GenExpr n t a q fun var)  = t
    type AnnotT (GenExpr n t a q fun var) = a
    type QuantT (GenExpr n t a q fun var) = q
    type SetTypeT arg (GenExpr n t a q fun var)  = GenExpr n arg a q fun var
    type SetAnnotT arg (GenExpr n t a q fun var) = GenExpr n t arg q fun var
    type SetQuantT arg (GenExpr n t a q fun var) = GenExpr n t a arg fun var

class IsFun fun where
    true_fun :: fun 
    false_fun :: fun 

-- true_fun :: (IsName n, TypeSystem t) => AbsFun n t
-- true_fun = mkConstant "true" bool

-- false_fun :: (IsName n, TypeSystem t) => AbsFun n t
-- false_fun = mkConstant "false" bool

instance ( IsName n
         , TypeSystem a
         , TypeSystem t
         -- , Typeable fun
         , IsFun fun
         -- , Typeable var
         , TypeAnnotationPair t a
         , IsQuantifier q)
        => HasGenExpr (GenExpr n t a q fun var) where
    type ExprT (GenExpr n t a q fun var)  = GenExpr n t a q fun var
    asExpr = id
    ztrue  = FunApp true_fun [] bool
    zfalse = FunApp false_fun [] bool
    -- zword  = Word

class ( IsGenExpr expr, AnnotT expr ~ TypeT expr )
    => IsAbsExpr expr where

instance (IsName n,TypeSystem t,IsQuantifier q) 
        => IsAbsExpr (AbsExpr n t q fun var) where

var_type :: AbsVar n t -> t
var_type (Var _ t) = t


instance ( IsName n,TypeSystem t,TypeSystem a
         , IsFun fun, Typed var, TypeOf var ~ t
         , TypeAnnotationPair t a,IsQuantifier q) 
        => Typed (GenExpr n t a q fun var) where
    type TypeOf (GenExpr n t a q fun var) = t
    type_of e = type_of $ aux $ asExpr e
        where
            aux (Word v)          = type_of v
            aux (Lit _ t)         = t
            aux (Cast _ t)        = strippedType t
            aux (Lift _ t)        = strippedType t
            aux (Record r)        = typeOfRecord r
            aux (FunApp _ _ t) = strippedType t
            -- aux (Binder _ _ _ _ t)   = t

typeOfRecord :: ( TypeSystem t, TypeSystem a
                , TypeAnnotationPair t a
                , IsFun fun, Typed var, TypeOf var ~ t
                , IsName n,IsQuantifier q,Pre)
             => RecordExpr (GenExpr n t a q fun var) -> t
typeOfRecord (RecLit m) = recordTypeOfFields m
typeOfRecord (RecSet m) = record_type $ type_of <$> m
typeOfRecord (RecUpdate x m) = recordTypeOfFields $ 
              M.map type_of m `M.union` fromJust' (type_of x^?fieldTypes) 
typeOfRecord (FieldLookup x field) = fromJust' (type_of x^?fieldTypes.ix field)

fieldTypes :: TypeSystem t => Prism' t (Table Field t)
fieldTypes =  _FromSort.swapped.below _RecordSort
            . iso (\(ts,m) -> m & unsafePartsOf traverse .~ ts) 
                  (\m -> (M.elems m,() <$ m))

recordTypeOfFields :: (Typed e, t ~ TypeOf e,TypeSystem t) => Table Field e -> t
recordTypeOfFields m = make_type (RecordSort $ () <$ m) $ type_of <$> M.elems m

ztuple_type :: TypeSystem t => [t] -> t
ztuple_type []          = null_type
ztuple_type [x]         = x
ztuple_type [x0,x1]     = pair_type x0 $ pair_type x1 null_type
ztuple_type (x0:x1:xs)  = pair_type x0 $ ztuple_type (x1:xs)

-- ztuple :: (IsName n,TypeSystem t,IsQuantifier q) => [AbsExpr n t q fun var] -> AbsExpr n t q fun var
-- ztuple []           = unit
-- ztuple [x]          = x
-- ztuple [x0,x1]      = pair x0 $ pair x1 unit    -- FunApp (Fun [tx, txs] "pair" [tx, txs] pair_type) [x,tail]
-- ztuple (x0:x1:xs)   = pair x0 $ ztuple (x1:xs)  -- FunApp (Fun [tx, txs] "pair" [tx, txs] pair_type) [x,tail]

-- unit :: (TypeSystem t,IsName n) => AbsExpr n t q fun var
-- unit = FunApp (mkConstant "null" null_type) []

-- pair :: (IsName n,TypeSystem t,IsQuantifier q) => AbsExpr n t q fun var -> AbsExpr n t q fun var -> AbsExpr n t q fun var
-- pair x y = FunApp (mk_fun [] (fromString'' "pair") [t0,t1] $ pair_type t0 t1) [x,y]
--     where
--         t0 = type_of x
--         t1 = type_of y

-- freeVarsOf :: IsGenExpr expr
--            => Traversal' expr (VarT expr)
-- freeVarsOf f = freeVarsOf'' (const f) M.empty

-- freeVarsOf'' :: (IsGenExpr expr, n ~ NameT expr,Applicative f) 
--              => (Table n (VarT expr) -> VarT expr -> f (VarT expr))
--              -> Table n (VarT expr)
--              -> expr -> f expr
-- freeVarsOf'' f vs (Word v) | (v^.name) `M.member` vs = pure (Word v)
--                            | otherwise       = Word <$> f vs v
-- freeVarsOf'' f vs e@(Binder _ us _ _ _) = 
--         rewriteM (freeVarsOf'' f $ M.union vs $ symbol_table us) e
-- freeVarsOf'' f vs e = rewriteM (freeVarsOf'' f vs) e

-- varsOf :: IsGenExpr expr
--        => Traversal' expr (VarT expr)
-- varsOf f (Word v) = Word <$> f v
-- varsOf f t = rewriteM (varsOf f) t

subexprs :: IsGenExpr expr
         => Traversal' expr expr
subexprs = rewriteExprM' pure pure pure

typesOf :: Traversal (GenExpr n t0 a q fun var) (GenExpr n t1 a q fun var)
                     t0 t1
typesOf = traverse4

typesOf' :: Traversal (AbsExpr n t0 q fun var) (AbsExpr n t1 q fun var)
                      t0 t1
typesOf' f = rewriteExprM f pure (typesOf' f)

instance IsName n => HasNames (GenExpr n t a q fun var) n where
    type SetNameT n' (GenExpr n t a q fun var) = GenExpr n' t a q fun var
    namesOf = traverse5

-- instance ( TypeAnnotationPair t a,IsName n
--          , TypeSystem t
--          , TypeSystem a
--          , IsQuantifier q
--          )
--       => Tree (Scope lv (GenExpr n t a q fun) var) where
--     as_tree' = as_tree' . fromScope
--     rewriteM _ = pure

instance TypeSystem t => Typed (Scope lv (GenExpr n t a q fun) var) where
    type TypeOf (Scope lv (GenExpr n t a q fun) var) = t

instance ( IsName n,TypeSystem t
         , IsQuantifier q
         , var ~ AbsVar n t
         , fun ~ AbsFun n t
         , Typeable fun) 
        => Tree (AbsDef n t q fun var) where
    as_tree' d@(Def _ _ vs e) = List <$> sequenceA
            [ Str  <$> render_decorated d
            , List <$> mapM as_tree' vs
            , as_tree' (type_of e) 
            , as_tree' (instantiate (pure . (vs !!)) e) ]
            -- , as_tree' (fromScope e & mapped %~ first (vs !!)) ]
        where
          -- word v = 
    rewriteM _ = pure

-- target :: AbsDef n t q fun var -> AbsExpr n t q fun var
-- target (Def _ _ e) = _ e

type FODef = AbsDef InternalName FOType HOQuantifier

type Def = AbsDef Name GenericType HOQuantifier

type Def' = AbsDef InternalName GenericType FOQuantifier

data AbsDef n t q fun var = Def [t] n [AbsVar n t] (Scope Int (AbsExpr n t q fun) var)
    deriving (Eq,Ord,Generic,Typeable,Functor,Foldable,Traversable,Show)

-- instance HasScope Def where
--     scopeCorrect' (Def _tp _n args _t e) = withVars args $ scopeCorrect' e

instance Functor1 (AbsDef n t q) where
instance Functor2 (AbsDef n t) where
instance Functor3 (AbsDef n) where
instance Functor4 AbsDef where

instance Foldable1 (AbsDef n t q) where
instance Foldable2 (AbsDef n t) where
instance Foldable3 (AbsDef n) where
instance Foldable4 AbsDef where

instance Traversable1 (AbsDef n t q) where
instance Traversable2 (AbsDef n t) where
instance Traversable3 (AbsDef n) where
instance Traversable4 AbsDef where
    traverseOn4 f g h p q (Def a b c d) = 
        Def <$> traverse g a
            <*> f b
            <*> traverse (traverseOn1 f g) c
            <*> scope (traverseOn5 f g g h p $ traverse q) d

            -- <*> traverseScoped 
            --       (traverseScope' $ traverseOn5 f g g h p (traverse q))
            --       (traverseOn1 f g) 
            --       c

instance IsName n => HasNames (AbsDef n t q fun var) n where
    type SetNameT m (AbsDef n t q fun var) = AbsDef m t q fun var
    namesOf = traverse4

z3Def :: Pre 
      => [Type] 
      -> String
      -> [Var] -> Expr fun Var
      -> Def fun Var
z3Def ts n vs e = Def ts (z3Name n) vs (abstract (`elemIndex` vs) e)

lookupFields :: ( IsName n,TypeSystem t,TypeSystem a
                , TypeAnnotationPair t a,IsQuantifier q
                , IsFun fun, HasType var t ) 
             => GenExpr n t a q fun var -> Table Name (GenExpr n t a q fun var)
lookupFields e = fromJust' $ type_of e^?fieldTypes.to (imap $ \f _ -> Record $ FieldLookup e f)

instance ( ZoomEq t
         , ZoomEq n
         , ZoomEq q
         , ZoomEq fun
         , ZoomEq var)
        => ZoomEq (AbsDef n t q fun var) where

instance Lifting Arbitrary (GenExpr n t a q fun) where

instance ( TypeSystem t
         , IsQuantifier q
         , Arbitrary t
         , Arbitrary n
         , Arbitrary q
         , Arbitrary fun
         , Arbitrary var) 
        => Arbitrary (AbsDef n t q fun var) where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance (TypeSystem a, TypeSystem t
         , TypeAnnotationPair t a
         , AbsVar n t ~ var
         , AbsFun n t ~ fun
         , IsQuantifier q, IsName n)
        => Tree (GenExpr n t a q fun var) where
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
    as_tree' (Record (RecLit m) _)  = 
        List <$> liftA2 (:) 
            (pure $ Str $ render (recordName m)) 
            (traverse as_tree' $ M.elems m)
    as_tree' (Record (RecSet m) _)  = 
        List <$> liftA2 (:) 
            (pure $ Str $ render (recordName m)) 
            (traverse as_tree' $ M.elems m)
    as_tree' (Record (RecUpdate x m') _)  = 
            List <$> liftA2 (:) 
                (pure $ Str $ render (recordName m)) 
                (traverse as_tree' $ M.elems m)
        where
          m = m' `M.union` lookupFields x
    as_tree' (Record (FieldLookup x field) _) =
        List <$> sequenceA [pure $ Str $ accessor field, as_tree' x]
    as_tree' (Word (Var xs _))    = return $ Str $ render xs
    as_tree' (Lit xs _)         = return $ Str $ pretty xs
    as_tree' (FunApp f [] t)
            | isLifted f = List <$> sequence   
                               [ List 
                                 <$> (map Str ["_","map"] ++) 
                                 <$> mapM as_tree' [t]
                               , Str <$> render_decorated f
                               ]
            | otherwise  = Str <$> render_decorated f
    as_tree' (FunApp f ts _)  = do
        ts' <- mapM as_tree' ts
        f   <- if isLifted f 
            then (List . map Str) 
                            <$> (["_","map"] ++) 
                            <$> mapM render_decorated [f]
            else Str <$> render_decorated f
        return $ List (f : ts')
    as_tree' (Binder q b t)  = do
        xs' <- mapM as_tree' $ boundVars b
        r'  <- as_tree' _r
        xp' <- as_tree' _xp
        return $ List [ Str $ pretty q
                      , List xs'
                      , List 
                          [ merge_range q
                          , r'
                          , xp' ] ]
    -- {-# INLINE rewriteM #-}
    rewriteM _ x@(Word _)        = pure x
    rewriteM _ x@(Lit _ _)       = pure x
    rewriteM f (Record e t)       = Record <$> traverseRecExpr f e <*> pure t
    rewriteM f (Lift e t)    = Lift <$> f e <*> pure t
    rewriteM f (Cast e t)    = Cast <$> f e <*> pure t
    rewriteM f (FunApp g xs t) = FunApp g <$> traverse f xs <*> pure t
    rewriteM f (Binder q xs x)  = Binder q 
            <$> traverseScoped (traverseExprs _) pure xs 
            <*> pure x

class HasExprs a expr where
    traverseExprs :: Traversal' a expr

instance HasExprs (BoundVar n t a q fun lv var) (GenExpr n t a q fun (B.Var lv var)) where
    traverseExprs f (BoundVar r t) = BoundVar <$> scope f r <*> scope f t

rewriteExpr :: (t0 -> t1)
            -> (q0 -> q1)
            -> (AbsExpr n t0 q0 fun var -> AbsExpr n t1 q1 fun var)
            -> AbsExpr n t0 q0 fun var -> AbsExpr n t1 q1 fun var
rewriteExpr fT fQ fE = runIdentity . rewriteExprM 
        (return . fT) (return . fQ) (return . fE)

rewriteExprM' :: (Applicative m)
              => (t0 -> m t1)
              -> (a0 -> m a1)
              -> (q0 -> m q1)
              -> (GenExpr n t0 a0 q0 fun var -> m (GenExpr n t1 a1 q1 fun var))
              -> GenExpr n t0 a0 q0 fun var -> m (GenExpr n t1 a1 q1 fun var)
rewriteExprM' fT fA fQ fE e = 
        case e of
            Word v -> Word <$> fvar v
            Lit v t -> Lit v <$> fT t
            FunApp f args t -> 
                funApp <$> ffun f
                       <*> traverse fE args
                       <*> fT t
            Binder q vs re ->
                binder <$> fQ q 
                       <*> traverse fvar vs 
                       <*> fT re
                       -- <*> fE te
                       -- <*> fT t
            Cast b e t -> Cast b <$> fE e <*> fA t
            Lift e t -> Lift <$> fE e <*> fA t
            Record e t -> Record <$> traverseRecExpr fE e <*> fT t
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
             -> (AbsExpr n t0 q0 fun var -> m (AbsExpr n t1 q1 fun var))
             -> AbsExpr n t0 q0 fun var -> m (AbsExpr n t1 q1 fun var)
rewriteExprM fT = rewriteExprM' fT fT

instance ( TypeSystem a,TypeSystem t
         , TypeAnnotationPair t a
         , fun ~ AbsFun n t
         , var ~ AbsVar n t
         , IsQuantifier q,IsName n) 
        => PrettyPrintable (GenExpr n t a q fun var) where
    pretty e = pretty $ runReader (as_tree' e) UserOutput

instance (TypeSystem t, IsQuantifier q, IsName n) => PrettyPrintable (AbsDef n t q fun var) where
    pretty (Def xs n ps e) = render n ++ showL xs ++  ": " 
        ++ args ++ pretty (as_tree (type_of e))
        ++ "  =  " ++ pretty (as_tree e)
        where
            showL [] = ""
            showL xs = pretty xs ++ " "
            args
                | L.null ps = ""
                | otherwise = intercalate " x " (map (pretty . as_tree) ps) ++ " -> "

instance TypeSystem t => Typed (AbsDef n t q fun var) where
    type TypeOf (AbsDef n t q fun var) = t
    type_of (Def _ _ _ e) = type_of e


defAsVar :: TypeSystem t => AbsDef n t q fun var -> Maybe (AbsVar n t)
defAsVar (Def [] n [] e) = Just $ Var n (type_of e)
defAsVar _ = Nothing

-- instance HasScope Expr where
--     scopeCorrect' e = do
--         let free = used_var' e
--         areVisible [vars,constants] free e

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
merge_all ms = foldl' (M.unionWithKey f) M.empty ms
    where
        f k x y
            | x == y    = x
            | otherwise = error $ [printf|conflicting declaration for key %s: %s %s|]
                            (show k) (show x) (show y)

substitute :: (TypeSystem t, IsQuantifier q, IsName n)
           => Table var (AbsExpr n t q fun var) 
           -> (AbsExpr n t q fun var) -> (AbsExpr n t q fun var)
substitute m e = e >>= _ . M.lookup m
    where
        f e@(Word v _) = maybe e id $ M.lookup (v^.name) m
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
         => GenExpr n t a q fun var -> S.Set (AbsVar n t)
used_var (Word v) = S.singleton v
used_var (Binder _ vs r expr _) = (used_var expr `S.union` used_var r) `S.difference` S.fromList vs
used_var expr = visit (\x y -> S.union x (used_var y)) S.empty expr

used_var' :: HasGenExpr expr => expr -> Table (NameT (ExprT expr)) (VarT (ExprT expr))
used_var' = symbol_table . S.toList . used_var . asExpr

used_fun :: (TypeSystem t, IsQuantifier q, IsName n) 
         => AbsExpr n t q fun var -> S.Set (AbsFun n t)
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

instance HasName (AbsDef n t q fun var) n where
    name = to $ \(Def _ x _ _ _) -> x

instance (TypeSystem t,IsName n) => Named (AbsDef n t q fun var) where
    type NameOf (AbsDef n t q fun var) = n
    decorated_name' (Def ts x _ _ _) = do
            ts' <- mapM z3_decoration' ts
            let suf = concat ts'
            onInternalName (addSuffix suf) 
                $ adaptName x

used_types :: (TypeSystem t,IsQuantifier q,IsName n) 
           => AbsExpr n t q fun var -> S.Set t
used_types e = visit (flip $ S.union . used_types) (
        case e of
            Binder _ vs e0 e1 t -> S.fromList $ t : type_of e0 : type_of e1 : L.map f vs
            _ -> S.singleton $ type_of e
            ) e
    where
        f (Var _ t) = t

rename :: (TypeSystem t, IsQuantifier q, IsName n) 
       => n -> n
       -> AbsExpr n t q fun var -> AbsExpr n t q fun var
rename x y e@(Word (Var vn t))
        | vn == x   = Word (Var y t)
        | otherwise = e
rename x y e@(Binder q vs r xp t)
        | x `elem` L.map (view name) vs  = e
        | otherwise             = Binder q vs (rename x y r) (rename x y xp) t
rename x y e = rewrite (rename x y) e 

-- primeOnly :: Table Name v -> Expr fun var -> Expr fun var
-- primeOnly vs = freeVarsOf %~ pr
--     where
--         pr v | (v^.name) `M.member` vs = prime v
--              | otherwise               = v

defExpr :: Lens' (AbsDef n t q fun var) (AbsExpr n t q fun var) 
defExpr f (Def ps n args rt e) = makeDef ps n args rt <$> f e

funOf :: (TypeSystem t, IsQuantifier q, IsName n) 
      => AbsDef n t q fun var -> AbsFun n t
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

getExpr :: ( HasExpr e )
        => e 
        -> AbsExpr (NameT (ExprT e)) Type HOQuantifier (FunT (ExprT e)) (VarT (ExprT e))
getExpr = asExpr

class (HasGenExpr e,Show e,PrettyPrintable e,Eq e,IsExpr (ExprT e),HasScope e) => HasExpr e where
class (HasGenExpr e,IsRawExpr (ExprT e),HasScope e) => HasRawExpr e where

-- instance (Eq fun,Eq var) => IsRawExpr (AbsExpr InternalName Type HOQuantifier fun var) where
-- instance (Eq fun,Eq var) => IsExpr (AbsExpr Name Type HOQuantifier fun var) where
-- instance (Eq fun,Eq var) => HasExpr (AbsExpr Name Type HOQuantifier fun var) where

liftRnf :: (NFData a,NFData b)
        => (NFData a :- NFData (f a))
        -> (NFData (B.Var b (f a)) :- NFData (f (B.Var b (f a))))
        -> f (B.Var b (f a)) -> ()
liftRnf (Sub Dict) (Sub Dict) = rnf

instance Serial1 RecordExpr where
instance (Ord n,Ord t,Serial t,Serial a
         ,Serial q,Serial fun,Serial lv
         ,Serial n) 
    => Serial1 (BoundVar n t a q fun lv) where
instance (Ord n,Ord t,Serial n,Serial t,Serial a,Serial q,Serial fun) => Serial1 (GenExpr n t a q fun) where
instance Lifting NFData (GenExpr n t a q fun) where
instance (Lifting NFData f,NFData a,NFData b) => NFData (Scope b f a) where
    rnf (Scope x) = liftRnf lifting lifting x
instance (NFData b,NFData a) => NFData (B.Var b a) where
instance (NFData t,NFData q,NFData n,NFData var) 
    => NFData (AbsDef n t q fun var)
instance (NFData t,NFData n) => NFData (AbsVar n t)
instance NFData Value
instance (NFData t,NFData q,NFData n,NFData a,NFData fun,NFData var) 
    => NFData (GenExpr n t a q fun var)
instance (NFData expr) => NFData (RecordExpr expr)

instance (Serialize lv,Serialize var,Serial t,Serial a
         ,Serial q,Serial fun,Serial var,Ord n,Ord t)
    => Serialize (BoundVar n t a q fun lv var) where

instance (Ord n,Ord t,Serialize n,Serialize q
         ,Serialize t,Serial t,Serial a
         ,Serial q,Serial fun,Serial var
         ,Serialize a,Serialize fun
         ,Serialize var)
    => Serialize (GenExpr n t a q fun var) where
instance (Serialize expr)
    => Serialize (RecordExpr expr) where
instance Serialize Value where
instance (Ord n,Ord t,Serialize n,Serialize q
         ,Serialize t,Serial t,Serial q
         ,Serial fun
         ,Serialize var,Serialize fun) 
    => Serialize (AbsDef n t q fun var) where

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
