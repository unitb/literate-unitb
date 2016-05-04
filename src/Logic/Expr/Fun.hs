{-# LANGUAGE TypeFamilies #-}
module Logic.Expr.Fun where

    -- Module
import Logic.Expr.Classes
import Logic.Expr.PrettyPrint
import Logic.Expr.Type
import Logic.Names

    -- Library
import Control.DeepSeq
import Control.Lens hiding (rewrite,Context,elements
                           ,Const,Context',List,rewriteM
                           ,Traversable1(..))
import Control.Precondition

import           Data.Data
import           Data.Hashable
import           Data.List as L
import           Data.Serialize

import GHC.Generics.Instances


import Test.QuickCheck


import Utilities.Functor

data SetWD  = FiniteWD | InfiniteWD
    deriving (Eq,Ord,Generic,Typeable,Data,Show)

data AbsFun n t = Fun 
        { _annotation :: [t]
        , _funName :: n
        , lifted :: Lifting
        , _arguments :: [t] 
        , _result :: t
        , _finite :: SetWD }
    deriving (Eq,Ord,Generic,Typeable,Data,Functor,Foldable,Traversable,Show)

data Lifting = Unlifted | Lifted
    deriving (Eq,Ord, Generic, Data, Typeable,Show)

makeLenses ''AbsFun

instance Serialize Lifting where

instance (Hashable n,Hashable t) => Hashable (AbsFun n t)
instance Hashable Lifting
instance Hashable SetWD

instance Arbitrary Lifting where
    arbitrary = genericArbitrary

instance Arbitrary SetWD where
    arbitrary = genericArbitrary

instance (Arbitrary t,Arbitrary n) => Arbitrary (AbsFun n t) where
    arbitrary = genericArbitrary

instance (NFData t,NFData n) => NFData (AbsFun n t) where
instance NFData Lifting
instance NFData SetWD

instance Functor1 AbsFun where
instance Foldable1 AbsFun where
instance Traversable1 AbsFun where
    traverse1 = funName

instance (IsName n,TypeSystem t) => PrettyPrintable (AbsFun n t) where
    pretty (Fun xs n _ ts t _) = render n ++ pretty xs ++ ": " 
            ++ args ++ pretty (as_tree t)
        where
            args
                | not $ null ts = intercalate " x " (map (pretty . as_tree) ts) ++ " -> "
                | otherwise     = ""

instance (TypeSystem t) => Typed (AbsFun n t) where
    type TypeOf (AbsFun n t)  = t
    type_of (Fun _ _ _ _ t _) = t

instance HasName (AbsFun n t) n where
    name = to $ \(Fun _ x _ _ _ _) -> x

instance IsName n => HasNames (AbsFun n t) n where
    type SetNameT n' (AbsFun n t) = AbsFun n' t
    namesOf = traverse1

instance (IsName n,TypeSystem t) => Named (AbsFun n t) where
    type NameOf (AbsFun n t) = n
    decorated_name' (Fun ts x _ _ _ _) = do
            ts' <- mapM z3_decoration' ts
            let suf = concat ts'
            onInternalName (addSuffix suf) 
                $ adaptName x

mk_fun' :: (Pre,IsName n) 
        => [t] -> String -> [t] -> t -> AbsFun n t
mk_fun' ps = mk_fun ps . z3Name

mk_fun :: [t] -> n -> [t] -> t -> AbsFun n t
mk_fun  ps n ts t = Fun ps n Unlifted ts t InfiniteWD

mk_lifted_fun :: IsName n => [t] -> n -> [t] -> t -> AbsFun n t
mk_lifted_fun ps n ts t = Fun ps n Lifted ts t InfiniteWD

mkConstant :: (Pre,IsName n) 
           => String -> t -> AbsFun n t
mkConstant n t = mk_fun [] (fromString'' n) [] t

    -- replace it everywhere (replace what? with what?)
z3_fun_name :: Fun -> InternalName
z3_fun_name (Fun xs ys _ _ _ _) = fromString'' $ render ys ++ concatMap z3_decoration xs

isLifted :: AbsFun n t -> Bool
isLifted (Fun _ _ lf _ _ _) = lf == Lifted

type Fun = AbsFun Name GenericType

type FOFun = AbsFun InternalName FOType

type InternalFun = AbsFun InternalName Type

instance (Data n,Data t,IsName n,TypeSystem t) => Tree (AbsFun n t) where
    as_tree' f@(Fun _ _ _ argT rT _) = List <$> sequenceA
            [ Str  <$> render_decorated f
            , List <$> mapM as_tree' argT 
            , as_tree' rT ]

instance (Serialize n,Serialize t) => Serialize (AbsFun n t) where
instance Serialize SetWD where
