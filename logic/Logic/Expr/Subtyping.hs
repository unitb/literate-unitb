{-# LANGUAGE TypeFamilies #-}
module Logic.Expr.Subtyping where

    -- Modules
import Logic.Expr.Classes
import Logic.Expr.Expr
import Logic.Expr.Fun
import Logic.Expr.Type
import Logic.Expr.Genericity hiding (Generic)

    -- Libraries
import Control.Lens hiding (rewriteM)

import Data.Bifunctor
import Data.Data
import Data.Hashable
import Data.List as L
import Data.Maybe
import Data.Typeable

import GHC.Generics hiding (from,to)

import Text.Pretty

newtype SubType = SubType { unSubType :: Type }
    deriving (Eq,Ord,Typeable,Generic,Data,Show,PrettyPrintable,Hashable)

instance Wrapped SubType where
    type Unwrapped SubType = Type
    _Wrapped' = iso unSubType SubType

instance TypeAnnotationPair SubType SubType where
    strippedType (SubType t) = SubType $ strippedType t

instance Tree SubType where
    as_tree' (SubType t) = as_tree' t
    rewriteM f = _Wrapped' (rewriteM $ from _Wrapped' f)

instance TypeSystem SubType where
    make_type s = SubType . make_type s . L.map unSubType
    _FromSort = _Wrapped'._FromSort.seconding (mapping $ from _Wrapped')

instance Typed SubType where
    type TypeOf SubType = SubType
    type_of = id

subtypeOf :: Sort -> Sort -> [SubType] -> Maybe [SubType]
subtypeOf sub super tParam 
    | sub == fun_sort && super == set_sort = Just $ case tParam of
                                                        [x0,x1] -> [pair_type x0 x1]
    | sub == super                         = Just tParam
    | otherwise                            = Nothing

something :: SubType -> AbsExpr n SubType q -> AbsExpr n SubType q
something t e = fromMaybe e $ do
        (sub,xs) <- type_of e^?_FromSort
        super    <- t^?_FromSort._1
        t <- make_type super <$> (subtypeOf sub super xs)
        _ e t

instance TypeSystem2 SubType where
    check_args' mkExpr fun args = do 
            _ $ zipWith _ (fun^.arguments) args
            mkExpr fun _ _
    zcast = undefined
