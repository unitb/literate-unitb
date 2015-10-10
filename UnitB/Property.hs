{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE DeriveFoldable       #-}
{-# LANGUAGE DeriveTraversable    #-}
module UnitB.Property 
    ( Transient
    , RawTransient
    , Transient'  (..)
    , Constraint 
    , RawConstraint 
    , Constraint' (..)
    , ProgressProp
    , RawProgressProp
    , ProgressProp'(..)
    , SafetyProp 
    , RawSafetyProp 
    , SafetyProp' (..) 
    , PropertySet 
    , RawPropertySet 
    , PropertySet' (..) 
    , PropertySet'Field (..) 
    , PropertySetField
    , empty_property_set
    , TrHint
    , RawTrHint
    , TrHint' (..)
    , empty_hint
    , makePropertySet'
    , changePropertySet'
    , ProgId (..)
    , variant_decreased
    , variant_equals_dummy
    , variant_bounded
    , Variant (..)
    , Direction (..)
    , make_unique
    , safety, transient
    , proofs, progress
    , constraint, inv, inv_thm )
where

    -- Modules
import Logic.Proof

import Theories.SetTheory

import UnitB.Expr

    -- Libraries
import Control.DeepSeq
import Control.Lens hiding (Const)

import Data.Default
import Data.DeriveTH
import Data.Foldable
import Data.Map  as M
import Data.List as L
import Data.String
import Data.Typeable

import Utilities.TableConstr

type Constraint = Constraint' Expr
type RawConstraint = Constraint' RawExpr

data Constraint' expr = 
        Co [Var] expr
    deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

type TrHint = TrHint' Expr
type RawTrHint = TrHint' RawExpr

data TrHint' expr = TrHint (Map String (Type,expr)) (Maybe Label)
    deriving (Eq,Ord,Show,Functor,Foldable,Traversable)


empty_hint :: TrHint
empty_hint = TrHint empty Nothing

type Transient = Transient' Expr
type RawTransient = Transient' RawExpr

data Transient' expr = 
        Tr 
            (Map String Var)     -- Free variables
            expr                 -- Predicate
            [Label]              -- Event, Schedule 
            (TrHint' expr)       -- Hints for instantiation
            -- (Map String Expr)    -- Index substitution
            -- (Maybe Label)        -- Progress Property for fine schedule
    deriving (Eq,Ord,Show,Functor,Foldable,Traversable)


data Direction = Up | Down
    deriving (Eq,Show)

data Variant = 
        SetVariant     Var RawExpr RawExpr Direction
      | IntegerVariant Var RawExpr RawExpr Direction
    deriving (Eq,Show)

type PropertySet = PropertySet' Expr
type RawPropertySet = PropertySet' RawExpr

data PropertySet' expr = PS
        { _transient    :: Map Label (Transient' expr)
        , _constraint   :: Map Label (Constraint' expr)
        , _inv          :: Map Label expr       -- inv
        , _inv_thm      :: Map Label expr       -- inv thm
        , _proofs       :: Map Label Proof
        , _progress     :: Map Label (ProgressProp' expr)
--        , schedule     :: Map Label Schedule
        , _safety       :: Map Label (SafetyProp' expr)
        }
    deriving (Eq,Functor,Foldable,Traversable)

newtype ProgId = PId { getProgId :: Label }
    deriving (Eq,Ord,IsString)

type ProgressProp = ProgressProp' Expr
type RawProgressProp = ProgressProp' RawExpr

data ProgressProp' expr = LeadsTo [Var] expr expr
    deriving (Eq,Ord,Typeable,Functor,Foldable,Traversable)

type SafetyProp = SafetyProp' Expr
type RawSafetyProp = SafetyProp' RawExpr

data SafetyProp' expr = Unless [Var] expr expr (Maybe Label)
    deriving (Eq,Ord,Typeable,Functor,Foldable,Traversable)

instance Show expr => Show (ProgressProp' expr) where
    show (LeadsTo _ p q) = show p ++ "  |->  " ++ show q

instance Show expr => Show (SafetyProp' expr) where
    show (Unless _ p q ev) = show p ++ "  UNLESS  " ++ show q ++ except
        where
            except = maybe "" (("  EXCEPT  " ++) . show) ev

instance Show expr => Show (PropertySet' expr) where
    show x = intercalate ", " $ L.map (\(x,y) -> x ++ " = " ++ y)
        [ ("transient",  show $ _transient x)
        , ("constraint", show $ _constraint x)
        , ("inv", show $ _inv x)
        , ("inv_thm", show $ _inv_thm x)
        , ("proofs", show $ keys $ _proofs x)
        , ("progress", show $ _progress x)
        , ("safety", show $ _safety x)
        ]

makeRecordConstr ''PropertySet'

type PropertySetField = PropertySet'Field Expr

empty_property_set :: PropertySet' expr
empty_property_set = makePropertySet' []

instance Default (PropertySet' expr) where
    def = empty_property_set

variant_equals_dummy :: Variant -> RawExpr
--variant_equals_dummy (SetVariant d var _ _)     = Word d `zeq` asExpr var
variant_equals_dummy (IntegerVariant d var _ _) = Word d `zeq` asExpr var
variant_equals_dummy (SetVariant d var _ _) = Word d `zeq` asExpr var

variant_decreased :: Variant -> RawExpr
variant_decreased (SetVariant d var _ Up)       = ($typeCheck) $ Right (Word d) `zsubset` Right (asExpr var)
variant_decreased (IntegerVariant d var _ Up)   = Word d `zless` asExpr var
variant_decreased (SetVariant d var _ Down)     = ($typeCheck) $ Right (asExpr var) `zsubset` Right (Word d)
variant_decreased (IntegerVariant d var _ Down) = asExpr var `zless` Word d

variant_bounded :: Variant -> RawExpr
--variant_bounded (SetVariant d var _ _)     = error "set variants unavailable"
variant_bounded (IntegerVariant _ var b Down) = asExpr b `zle` asExpr var
variant_bounded (IntegerVariant _ var b Up)   = asExpr var `zle` asExpr b
variant_bounded (SetVariant _ var b Down) = ($typeCheck) $ 
    mzand (Right (asExpr b) `zsubset` Right (asExpr var))
          (mzfinite $ Right (asExpr var) `zsetdiff` Right (asExpr b))
variant_bounded (SetVariant _ var b Up)   = ($typeCheck) $ 
    mzand (Right (asExpr var) `zsubset` Right (asExpr b))
          (mzfinite $ Right (asExpr b) `zsetdiff` Right (asExpr var))

make_unique :: String           -- suffix to be added to the name of variables
            -> Map String Var   -- set of variables that must renamed
            -> RawExpr          -- expression to rewrite
            -> RawExpr
make_unique suf vs w@(Word (Var vn vt)) 
        | vn `M.member` vs    = Word (Var (vn ++ suf) vt)
        | otherwise           = w
make_unique _ _ c@(Const _ _)    = c
make_unique suf vs (FunApp f xs)     = FunApp f $ L.map (make_unique suf vs) xs
make_unique suf vs (Cast e t)        = Cast (make_unique suf vs e) t
make_unique suf vs (Lift e t)        = Lift (make_unique suf vs e) t
make_unique suf vs (Binder q d r xp t) = Binder q d (f r) (f xp) t
    where
        local = (L.foldr M.delete vs (L.map name d))
        f = make_unique suf local

makeLenses ''PropertySet'

derive makeNFData ''ProgId
derive makeNFData ''Constraint'
derive makeNFData ''Direction
derive makeNFData ''ProgressProp'
derive makeNFData ''PropertySet'
derive makeNFData ''SafetyProp'
derive makeNFData ''Transient'
derive makeNFData ''TrHint'
derive makeNFData ''Variant
