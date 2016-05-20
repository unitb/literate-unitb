{-# LANGUAGE TypeFamilies #-}
module Logic.Expr.Context where

    -- Module
import Logic.Expr.Classes
import Logic.Expr.Expr
import Logic.Expr.Type
import Logic.Names

    -- Library
import Control.Applicative hiding (Const) -- ((<|>),(<$>),(<*>),many)
import Control.DeepSeq
import Control.Monad.Reader
import Control.Monad.State
import Control.Lens hiding (rewrite,Context,elements
                           ,Const,Context',List,rewriteM
                           ,Traversable1(..),children)
import Control.Lens.Misc

import           Data.Data
import           Data.Default
import qualified Data.Map.Class as M
import           Data.PartialOrd
import           Data.Semigroup
import           Data.Serialize

import GHC.Generics.Instances

import Test.QuickCheck
import Test.QuickCheck.Report ()
import Test.QuickCheck.ZoomEq

import Utilities.Functor
import Utilities.Table

type Context = AbsContext GenericType HOQuantifier

type RawContext = GenContext InternalName Type HOQuantifier

type Context' = GenContext InternalName GenericType FOQuantifier

type FOContext = GenContext InternalName FOType FOQuantifier

type AbsContext = GenContext Name

data GenContext name t q = Context
        { _genContextSorts :: Table Name Sort
        , _genContextConstants :: Table name (AbsVar name t)
        , _functions :: Table name (AbsFun name t)
        , _definitions :: Table name (AbsDef name t q)
        , _genContextDummies :: Table name (AbsVar name t)
        }
    deriving (Show,Eq,Generic,Typeable,Functor,Foldable,Traversable)

makeFields ''GenContext
makeClassy ''GenContext

absContext :: HasGenContext a name t q 
           => Lens' a (GenContext name t q)
absContext = genContext

defsAsVars :: AbsContext t q -> AbsContext t q
defsAsVars = execState $ do
        defs <- uses definitions $ M.mapMaybe defAsVar
        constants %= M.union defs

class HasSymbols a b n | a -> b n where
    symbols :: a -> Table n b

instance (Ord n,Hashable n) => HasSymbols (GenContext n t q) () n where
    symbols ctx = M.unions [f a,f b,f c]
        where
            (Context _ a b c _) = ctx^.genContext
            f = M.map (const ())

merge_ctx :: (Show t, TypeSystem t, IsQuantifier q,IsName n)
          => GenContext n t q -> GenContext n t q 
          -> GenContext n t q
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
instance Default (GenContext n t q) where
    def = genericDefault

instance Default (CtxConflict n t q) where
    def = genericDefault

data CtxConflict n t q = CtxWith 
            { conflict :: GenContext n t q
            , declaration :: GenContext n t q }
    deriving (Generic)

instance (Ord n,Hashable n) => Semigroup (GenContext n t q) where
instance (Ord n,Hashable n) => Monoid (GenContext n t q) where
    mempty  = genericMEmpty
    mconcat = genericMConcat
    mappend = genericMAppend
instance (Ord n,Hashable n) => Semigroup (Intersection (GenContext n t q)) where
    (<>) = genericSemigroupMAppendWith
    sconcat = genericSemigroupMConcatWith

instance (Ord n,Hashable n) => Semigroup (CtxConflict n t q) where
instance (Ord n,Hashable n) => Monoid (CtxConflict n t q) where
    mempty  = def
    mappend c0 c1 = CtxWith 
        { conflict = mconcat [conflict c0,conflict c1
            , getIntersection $ Intersection (declaration c0) <> Intersection (declaration c1)] 
        , declaration = declaration c0 `mappend` declaration c1 }

instance (Ord n,Eq t,Eq q) => PreOrd (GenContext n t q) where
    partCompare = genericPreorder

instance (Ord n,Eq t,Eq q) => PartialOrd (GenContext n t q) where

instance ( Ord n,ZoomEq n,ZoomEq t,ZoomEq q) 
        => ZoomEq (GenContext n t q) where
instance ( Ord n,TypeSystem t,IsQuantifier q
         , Arbitrary n,Arbitrary t,Arbitrary q) 
        => Arbitrary (GenContext n t q) where
    arbitrary = scale (`div` 2) genericArbitrary
    shrink = genericShrink

empty_ctx :: GenContext n t q
empty_ctx = def

--merge_ctx :: (TypeSystem t, IsQuantifier q,Show n,IsName n)
--          => GenContext n t q -> GenContext n t q 
--          -> GenContext n t q
--merge_ctx ctx0 ctx1 = byPred assert "merge_ctx" (def ==) (conflict ctx') (declaration ctx')
--    where
--        ctx' = CtxWith def ctx0 <> CtxWith def ctx1

--merge_all_ctx :: [Context] -> Context
--merge_all_ctx cs = byPred assert "merge_ctx" (def ==) (conflict ctx') (declaration ctx')
--    where
--        ctx' = mconcat $ CtxWith def <$> cs

free_vars :: Context -> Expr -> Table Name Var
free_vars (Context _ _ _ _ dum) e = M.fromList $ runReader (f e) dum
    where
        f (Word v) = do
            dum <- ask
            pure $ if (v^.name) `M.member` dum 
                then [(v^.name,v)]
                else []
        f e@(Binder _ vs _ _ _) = local (M.\\ symbol_table vs) $ concat <$> forM (e^.partsOf children) f
            --M.toList (M.fromList (visitM f xs v) M.\\ symbol_table vs)
        f e = concat <$> forM (e^.partsOf children) f -- visitM f v

var_decl :: Name -> Context -> Maybe Var
var_decl s (Context _ m _ _ d) = 
    M.lookup s m <|> M.lookup s d

class HasExprs a expr where
    traverseExprs :: Traversal' a expr

instance HasExprs (GenContext n t q) (AbsExpr n t q) where
    traverseExprs = definitions.traverse.defExpr

instance (NFData n,NFData t,NFData q) => NFData (GenContext n t q)

instance IsName n => Translatable (GenContext n t q) (GenContext InternalName t q) where
    translate = namesOf %~ asInternal

instance Functor1 (GenContext n) where
--instance Functor2 GenContext where

instance Foldable1 (GenContext n) where
--instance Foldable2 GenContext where

instance Traversable1 (GenContext n) where
    traverse1 f (Context a b c d e) = Context a 
            <$> (traverse.traverse) f b
            <*> (traverse.traverse) f c
            <*> (traverse.traverse1) f d
            <*> (traverse.traverse) f e
instance IsName n => HasNames (GenContext n t q) n where
    type SetNameT m (GenContext n t q) = GenContext m t q
    namesOf f (Context a b c d e) = Context a 
            <$> traversePairs (onBoth f $ traverse1 f) b
            <*> traversePairs (onBoth f $ traverse1 f) c
            <*> traversePairs (onBoth f $ traverse2 f) d
            <*> traversePairs (onBoth f $ traverse1 f) e

instance (Ord n,Serialize n,Serialize t,Serialize q) 
    => Serialize (GenContext n t q) where
