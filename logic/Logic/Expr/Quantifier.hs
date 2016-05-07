module Logic.Expr.Quantifier where

    -- Modules
import Logic.Expr.Classes
import Logic.Expr.Fun
import Logic.Expr.PrettyPrint
import Logic.Expr.Type
import Logic.Names

    -- Libraries
import Control.DeepSeq
import Control.Lens

import Data.Data
import Data.Hashable
import Data.Serialize

import GHC.Generics
import GHC.Generics.Instances

import Test.QuickCheck

data QuantifierType = QTConst Type | QTSort Sort | QTFromTerm Sort | QTTerm
    deriving (Eq,Ord,Generic,Typeable,Data,Show)

data HOQuantifier = 
        Forall 
        | Exists 
        | UDQuant Fun Type QuantifierType SetWD
    deriving (Eq,Ord,Generic,Typeable,Data,Show)

data FOQuantifier = FOForall | FOExists 
    deriving (Eq,Ord,Generic,Typeable,Data,Show)

class (Ord q, PrettyPrintable q, Show q, Data q, Hashable q) => IsQuantifier q where
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

instance PrettyPrintable HOQuantifier where
    pretty Forall = "forall"
    pretty Exists = "exists"
    pretty (UDQuant f _ _ _) = render $ f^.name

instance PrettyPrintable FOQuantifier where
    pretty FOForall = "forall"
    pretty FOExists = "exists"

instance NFData QuantifierType
instance NFData FOQuantifier
instance NFData HOQuantifier

instance Hashable QuantifierType
instance Hashable HOQuantifier
instance Hashable FOQuantifier

instance Arbitrary HOQuantifier where
    arbitrary = genericArbitrary

instance Arbitrary QuantifierType where
    arbitrary = genericArbitrary

instance Serialize HOQuantifier where
instance Serialize QuantifierType where

finiteness :: HOQuantifier -> SetWD
finiteness Forall = InfiniteWD
finiteness Exists = InfiniteWD
finiteness (UDQuant _ _ _ fin) = fin
