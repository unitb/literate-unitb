{-# LANGUAGE TypeFamilies #-}
module Logic.Expr.Variable where

    -- Module
import Logic.Expr.Classes
import Logic.Expr.Type

    -- Library
import           GHC.Generics hiding (to)

import Control.Lens hiding (rewrite,Context
                           ,Const,Context',List)

import Data.Data
import Data.Map as M

type UntypedVar = AbsVar ()

type Var = AbsVar GenericType

type FOVar = AbsVar FOType

data AbsVar t = Var String t
    deriving (Eq,Ord,Generic,Typeable,Data)

instance TypeSystem t => Tree (AbsVar t) where
    as_tree' (Var vn vt) = do
        t <- as_tree' vt
        return $ List [Str vn, t]
    rewriteM' = id

instance TypeSystem t => Show (AbsVar t) where
    show (Var n t) = n ++ ": " ++ show (as_tree t)

instance TypeSystem t => Typed (AbsVar t) where
    type TypeOf (AbsVar t) = t

prime :: AbsVar t -> AbsVar t
prime (Var n t) = Var (n ++ "@prime") t

primeAll :: Map String (AbsVar t) -> Map String (AbsVar t)
primeAll m = M.mapKeys (++ "@prime") $ M.map prime m

instance HasName (AbsVar t) String where
    name = to $ \(Var x _) -> x

instance Named (AbsVar t) where
    decorated_name' = return . view name
