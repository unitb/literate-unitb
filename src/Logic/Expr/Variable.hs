{-# LANGUAGE TypeFamilies #-}
module Logic.Expr.Variable where

    -- Module
import Logic.Expr.Classes
import Logic.Expr.PrettyPrint
import Logic.Expr.Type
import Logic.Names

    -- Library
import Control.Lens hiding (rewrite,Context
                           ,Const,Context',List
                           ,Traversable1(..))
import Control.Precondition

import Data.Data
import Data.Map.Class as M
import Data.Serialize

import GHC.Generics.Instances

import Test.QuickCheck

import Utilities.Functor
import Utilities.Table

type UntypedVar = AbsVar Name ()

type Var = AbsVar Name GenericType

type Var' = AbsVar InternalName Type

type FOVar = AbsVar InternalName FOType

data AbsVar name t = Var name t
    deriving (Eq,Ord,Generic,Typeable,Data,Functor,Foldable,Traversable,Show)

translate' :: (n0 -> n1) -> AbsVar n0 t -> AbsVar n1 t
translate' = fmap1

instance (Hashable name,Hashable t) => Hashable (AbsVar name t) where

instance (Arbitrary t,Arbitrary n) => Arbitrary (AbsVar n t) where
    arbitrary = genericArbitrary

instance IsName n => Translatable (AbsVar n t) (AbsVar InternalName t) where
    translate = translate' asInternal

instance (TypeSystem t,IsName n) => Tree (AbsVar n t) where
    as_tree' (Var vn vt) = do
        t <- as_tree' vt
        return $ List [Str $ render vn, t]
    rewriteM _ = pure

instance (TypeSystem t, IsName n) => Typed (AbsVar n t) where
    type TypeOf (AbsVar n t) = t
    type_of (Var _ t) = t

instance (TypeSystem t, IsName n) => PrettyPrintable (AbsVar n t) where
    pretty (Var n t) = render n ++ ": " ++ show (as_tree t)

instance Functor1 AbsVar where
instance Foldable1 AbsVar where
instance Traversable1 AbsVar where
    traverse1 f (Var n t) = Var <$> f n <*> pure t

prime :: IsName n => AbsVar n t -> AbsVar n t
prime (Var n t) = Var (addPrime n) t

primeAll :: IsName n => Table n (AbsVar n t) -> Table n (AbsVar n t)
primeAll m = M.mapKeys addPrime $ M.map prime m

z3Var :: Pre
      => String -> t -> AbsVar Name t
z3Var = Var . fromString''

instance HasName (AbsVar n t) n where
    name = to $ \(Var x _) -> x

instance IsName n => HasNames (AbsVar n t) n where
    type SetNameT n' (AbsVar n t) = AbsVar n' t
    namesOf f (Var x t) = Var <$> f x <*> pure t

instance (IsName n,Typeable t) => Named (AbsVar n t) where
    type NameOf (AbsVar n t) = n
    decorated_name' (Var x _) = adaptName x

instance (Serialize n,Serialize t) => Serialize (AbsVar n t) where
