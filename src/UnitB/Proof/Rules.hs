{-# LANGUAGE KindSignatures
        , GADTs, TypeOperators
        , Arrows, CPP
        , PatternSynonyms
        , ScopedTypeVariables
        , ConstraintKinds
        , TypeFamilies
        , StandaloneDeriving
        #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module UnitB.Proof.Rules where

    -- Modules
import Logic.Expr as E hiding (Context)

import UnitB.Property

    -- Libraries
import Control.Applicative
import Control.Arrow.Unfold
import Control.Category
import Control.DeepSeq
import Control.Lens 

import Data.Default
import Data.Existential
import Data.ForallInstances
#if MIN_VERSION_transformers(0,5,0)
import Prelude.Extras hiding (Lift1)
#else
import Data.Functor.Classes
#endif
import Data.Maybe
import Data.Serialize hiding (label)
import Data.Typeable
import Data.Unfoldable

import GHC.Generics.Instances

import Prelude hiding (id,(.))

import Test.QuickCheck.ZoomEq

import Utilities.Syntactic

type Builder r t = forall arr a b constr. ArrowUnfold arr 
               => (constr r :- Unfoldable t)
               -> arr b (Maybe a) 
               -> arr (b,Inst1 Proxy constr r,LineInfo) (Either [Error] (t a))

reproxy :: proxy (Proxy rule) -> Proxy rule
reproxy _ = Proxy

class ( Eq rule
      , Eq1 (ProgressHyp rule)
      , Eq1 (SafetyHyp rule)
      , Eq1 (TransientHyp rule)
      , Typeable (ProgressHyp rule)
      , Typeable (SafetyHyp rule)
      , Typeable rule
      , ZoomEq rule
      , Show rule
      , Serialize rule
      , InstForall ZoomEq (ProgressHyp rule)
      , InstForall ZoomEq (SafetyHyp rule)
      , InstForall ZoomEq (TransientHyp rule)
      , Show1 (ProgressHyp rule)
      , Show1 (SafetyHyp rule)
      , Show1 (TransientHyp rule)
      , Serialize1 (ProgressHyp rule)
      , Serialize1 (TransientHyp rule)
      , Serialize1 (SafetyHyp rule)
      , NFData rule
      , NFData1 (ProgressHyp rule)
      , NFData1 (SafetyHyp rule)
      , NFData1 (TransientHyp rule)
      , Unfoldable (TransientHyp rule)
      , Unfoldable (ProgressHyp rule)
      , Unfoldable (SafetyHyp rule)
      , Traversable (TransientHyp rule)
      , Traversable (ProgressHyp rule)
      , Traversable (SafetyHyp rule) ) =>
        LivenessRule rule where
    type SafetyHyp rule :: * -> *
    type ProgressHyp rule :: * -> *
    type TransientHyp rule :: * -> *
    type TransientHyp rule = None
    type EventSupport rule :: * -> *
    type EventSupport rule = None
    rule_name' :: proxy rule -> Label
    travRefs' :: Traversal' rule ProgId
    travEvent' :: Traversal' rule EventId
    voidInference' :: HasExpr expr
                   => (LivenessRule rule :- constr rule)
                   -> ProgressProp' expr
                   -> Proxy rule
                   -> ((None ~ ProgressHyp rule,None ~ SafetyHyp rule,None ~ TransientHyp rule) 
                        => RawProgressProp -> Proxy rule -> f rule)
                   -> Maybe (Cell1 f constr)
    default voidInference' :: ( HasExpr expr
                              , ProgressHyp rule ~ None
                              , SafetyHyp rule ~ None
                              , TransientHyp rule ~ None )
                           => (LivenessRule rule :- constr rule)
                           -> ProgressProp' expr
                           -> Proxy rule
                           -> (RawProgressProp -> Proxy rule -> f rule)
                           -> Maybe (Cell1 f constr)
    voidInference' (Sub Dict) g r f = Just $ Cell $ f (getExpr <$> g) r

instance InstForall ZoomEq NonEmpty where
instance InstForall ZoomEq Maybe where
instance InstForall ZoomEq None where
instance InstForall ZoomEq One where

instance LivenessRule rule => LivenessRule (Proxy rule) where
    type ProgressHyp (Proxy rule) = ProgressHyp rule
    type SafetyHyp (Proxy rule) = SafetyHyp rule
    type TransientHyp (Proxy rule) = TransientHyp rule
    rule_name' = rule_name' . reproxy
    travEvent' _ = pure
    travRefs' _ = pure
    voidInference' _ _ _ _ = Nothing

data Reference = Reference (ProgId) 
    deriving (Eq,Generic,Typeable,Show)
instance ZoomEq Reference where
instance LivenessRule Reference where
    type ProgressHyp Reference = None
    type SafetyHyp Reference = None
    type EventSupport Reference = One
    rule_name' _  = label "reference"
    travRefs' f (Reference pid) = Reference <$> f pid
    travEvent' _ = pure
instance NFData Reference where

data Add = Add 
    deriving (Eq,Generic,Typeable,Show)
instance ZoomEq Add where
instance LivenessRule Add where
    type ProgressHyp Add = None
    type SafetyHyp Add = None
    rule_name' _ = label "add"
    travRefs' _ = pure
    travEvent' _ = pure
instance NFData Add where

data Ensure = Ensure (NonEmpty EventId) (RawTrHint) 
    deriving (Eq,Generic,Typeable,Show)
instance ZoomEq Ensure where
instance LivenessRule Ensure where
    type ProgressHyp Ensure = None
    type SafetyHyp Ensure = None
    type EventSupport Ensure = NonEmpty
    rule_name' _   = label "ensure"
    travRefs' f (Ensure es (TrHint ws pid)) = 
            Ensure es . TrHint ws <$> traverse f pid
    travEvent' f (Ensure es tr) = 
            Ensure <$> traverse f es <*> pure tr
instance NFData Ensure where

data Implication = Implication 
    deriving (Eq,Generic,Typeable,Show)
instance ZoomEq Implication where
instance LivenessRule Implication where
    type ProgressHyp Implication = None
    type SafetyHyp Implication = None
    rule_name' _  = label "implication"
    travRefs' _ = pure
    travEvent' _ = pure
instance NFData Implication where
instance Default Implication where
    def = genericDefault

data Disjunction = Disjunction 
    deriving (Eq,Generic,Typeable,Show)
instance ZoomEq Disjunction where
instance LivenessRule Disjunction where
    type ProgressHyp Disjunction = NonEmpty
    type SafetyHyp Disjunction = None
    rule_name' _  = label "disjunction"
    travRefs' _ = pure
    travEvent' _ = pure
    voidInference' _ _ _ _ = Nothing
instance NFData Disjunction where
instance Default Disjunction where
    def = genericDefault

data NegateDisjunct = NegateDisjunct 
    deriving (Eq,Generic,Typeable,Show)
instance ZoomEq NegateDisjunct where
instance LivenessRule NegateDisjunct where
    type ProgressHyp NegateDisjunct = One
    type SafetyHyp NegateDisjunct = None
    rule_name' _ = label "trading"
    travRefs' _ = pure
    travEvent' _ = pure
    voidInference' _ _ _ _ = Nothing
instance NFData NegateDisjunct where
instance Default NegateDisjunct where
    def = genericDefault

data Transitivity = Transitivity 
    deriving (Eq,Generic,Typeable,Show)
instance ZoomEq Transitivity where
instance LivenessRule Transitivity where
    type ProgressHyp Transitivity = NonEmpty
    type SafetyHyp Transitivity = None
    rule_name' _ = label "transitivity"
    travRefs' _ = pure
    travEvent' _ = pure
    voidInference' _ _ _ _ = Nothing
instance NFData Transitivity where
instance Default Transitivity where
    def = genericDefault

data PSP = PSP 
    deriving (Eq,Generic,Typeable,Show)
instance ZoomEq PSP where
instance LivenessRule PSP where
    type ProgressHyp PSP = One
    type SafetyHyp PSP = One
    rule_name' _ = label "PSP"
    travRefs' _ = pure
    travEvent' _ = pure
    voidInference' _ _ _ _ = Nothing
instance NFData PSP where
instance Default PSP where
    def = genericDefault

data Induction = Induction Variant
    deriving (Eq,Generic,Typeable,Show)
instance ZoomEq Induction where
instance LivenessRule Induction where
    type ProgressHyp Induction = One
    type SafetyHyp Induction = None
    rule_name' _  = label "induction"
    travRefs' _ = pure
    travEvent' _ = pure
    voidInference' _ _ _ _ = Nothing
instance NFData Induction where

data Monotonicity = Monotonicity 
    deriving (Eq,Generic,Typeable,Show)
instance ZoomEq Monotonicity where
instance LivenessRule Monotonicity where
    type ProgressHyp Monotonicity = One
    type SafetyHyp Monotonicity = None
    rule_name' _ = label "monotonicity"
    travRefs' _ = pure
    travEvent' _ = pure
    voidInference' _ _ _ _ = Nothing
instance NFData Monotonicity where
instance Default Monotonicity where
    def = genericDefault

data Discharge = Discharge
    deriving (Eq,Generic,Typeable,Show)
instance ZoomEq Discharge where
instance LivenessRule Discharge where
    type ProgressHyp Discharge = None
    type SafetyHyp Discharge = Maybe
    type TransientHyp Discharge = One
    rule_name' _ = label "discharge"
    travRefs' _ = pure
    travEvent' _ Discharge = pure Discharge
    voidInference' _ _ _ _ = Nothing
instance NFData Discharge where 

instance Serialize Discharge where
instance Serialize Reference where
instance Serialize Add where
instance Serialize Ensure where
instance Serialize Implication where
instance Serialize Disjunction where
instance Serialize NegateDisjunct where
instance Serialize Transitivity where
instance Serialize Monotonicity where
instance Serialize Induction where
instance Serialize PSP where
