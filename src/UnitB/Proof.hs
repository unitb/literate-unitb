{-# LANGUAGE KindSignatures
        , GADTs, TypeOperators
        , ScopedTypeVariables
        , ConstraintKinds
        , TypeFamilies
        #-}
module UnitB.Proof where

    -- Modules
import Logic.Expr hiding (Context,Const)
import Logic.Proof.POGenerator
import UnitB.Property

    -- Libraries
import Control.DeepSeq
import Control.Lens

import Data.Functor.Classes
import Data.Foldable as F
import Data.List.Ordered
import Data.Maybe
import Data.Typeable

import Text.Printf

import Utilities.Existential
import Utilities.Instances

type None = Const ()
type One  = Identity

class ( Eq rule,Eq1 (ProgressHyp rule),Eq1 (SafetyHyp rule)
      , Typeable (ProgressHyp rule), Typeable (SafetyHyp rule), Typeable rule
      , Show1 (ProgressHyp rule), Show1 (SafetyHyp rule), Show rule
      , NFData rule, NFData1 (ProgressHyp rule), NFData1 (SafetyHyp rule)
      , Traversable (ProgressHyp rule), Traversable (SafetyHyp rule) ) =>
        LivenessRule rule where
    type SafetyHyp rule :: * -> *
    type ProgressHyp rule :: * -> *
    rule_name :: rule -> Label
    travRefs' :: Traversal' rule ProgId
    travEvent' :: Traversal' rule EventId

class LivenessRule rule => LivenessRulePO rule  where
    liveness_po :: RawProgressProp 
                -> rule
                -> ProgressHyp rule RawProgressProp
                -> SafetyHyp rule RawSafetyProp
                -> POGen ()
    automaticSafety :: RawProgressProp -> rule -> [RawSafetyProp]
    automaticTransient :: RawProgressProp -> rule -> [RawTransient]
    automaticSafety _ _ = []
    automaticTransient _ _ = []

data ARule = ARule { _aRuleCell :: Cell LivenessRulePO }

makeFields ''ARule

data Reference = Reference (ProgId) 
    deriving (Eq,Generic,Typeable,Show)
instance LivenessRule Reference where
    type ProgressHyp Reference = None
    type SafetyHyp Reference = None
    rule_name (Reference _)  = label "reference"
    travRefs' f (Reference pid) = Reference <$> f pid
    travEvent' _ = pure
instance NFData Reference where

data Add = Add 
    deriving (Eq,Generic,Typeable,Show)
instance LivenessRule Add where
    type ProgressHyp Add = None
    type SafetyHyp Add = None
    rule_name (Add) = label "add"
    travRefs' _ = pure
    travEvent' _ = pure
instance NFData Add where

data Ensure = Ensure (NonEmpty EventId) (RawTrHint) 
    deriving (Eq,Generic,Typeable,Show)
instance LivenessRule Ensure where
    type ProgressHyp Ensure = None
    type SafetyHyp Ensure = None
    rule_name (Ensure _ _)   = label "ensure"
    travRefs' f (Ensure es (TrHint ws pid)) = 
            Ensure es . TrHint ws <$> traverse f pid
    travEvent' f (Ensure es tr) = 
            Ensure <$> traverse f es <*> pure tr
instance NFData Ensure where

data Implication = Implication 
    deriving (Eq,Generic,Typeable,Show)
instance LivenessRule Implication where
    type ProgressHyp Implication = None
    type SafetyHyp Implication = None
    rule_name (Implication)  = label "implication"
    travRefs' _ = pure
    travEvent' _ = pure
instance NFData Implication where

data Disjunction = Disjunction 
    deriving (Eq,Generic,Typeable,Show)
instance LivenessRule Disjunction where
    type ProgressHyp Disjunction = NonEmpty
    type SafetyHyp Disjunction = None
    rule_name (Disjunction)  = label "disjunction"
    travRefs' _ = pure
    travEvent' _ = pure
instance NFData Disjunction where

data NegateDisjunct = NegateDisjunct 
    deriving (Eq,Generic,Typeable,Show)
instance LivenessRule NegateDisjunct where
    type ProgressHyp NegateDisjunct = One
    type SafetyHyp NegateDisjunct = None
    rule_name (NegateDisjunct) = label "trading"
    travRefs' _ = pure
    travEvent' _ = pure
instance NFData NegateDisjunct where

data Transitivity = Transitivity 
    deriving (Eq,Generic,Typeable,Show)
instance LivenessRule Transitivity where
    type ProgressHyp Transitivity = NonEmpty
    type SafetyHyp Transitivity = None
    rule_name (Transitivity) = label "transitivity"
    travRefs' _ = pure
    travEvent' _ = pure
instance NFData Transitivity where

data PSP = PSP 
    deriving (Eq,Generic,Typeable,Show)
instance LivenessRule PSP where
    type ProgressHyp PSP = One
    type SafetyHyp PSP = One
    rule_name (PSP) = label "PSP"
    travRefs' _ = pure
    travEvent' _ = pure
instance NFData PSP where

data Induction = Induction  (Variant) 
    deriving (Eq,Generic,Typeable,Show)
instance LivenessRule Induction where
    type ProgressHyp Induction = One
    type SafetyHyp Induction = None
    rule_name (Induction _)  = label "induction"
    travRefs' _ = pure
    travEvent' _ = pure
instance NFData Induction where

data Monotonicity = Monotonicity 
    deriving (Eq,Generic,Typeable,Show)
instance LivenessRule Monotonicity where
    type ProgressHyp Monotonicity = One
    type SafetyHyp Monotonicity = None
    rule_name (Monotonicity)   = label "monotonicity"
    travRefs' _ = pure
    travEvent' _ = pure
instance NFData Monotonicity where

data Discharge = Discharge Label RawTransient
    deriving (Eq,Generic,Typeable,Show)
instance LivenessRule Discharge where
    type ProgressHyp Discharge = None
    type SafetyHyp Discharge = Maybe
    rule_name _ = label "discharge"
    travRefs' _ = pure
    travEvent' f (Discharge lbl tr) = Discharge lbl <$> traverseEvents f tr
instance NFData Discharge where 

travRefs :: Traversal' ARule ProgId
travRefs = cellLens' travRefs'

travEvent :: Traversal' ARule EventId
travEvent = cellLens' travEvent'

data ProofTree = forall rule. 
            LivenessRulePO rule =>
        ProofNode rule 
            ((ProgressHyp rule) (RawProgressProp,ProofTree)) 
            (SafetyHyp rule (RawSafetyProp,Maybe Label))

instance Eq ProofTree where
    ProofNode n0 p0 s0 == ProofNode n1 p1 s1 = fromMaybe False $ do
            Refl <- sameType n0 n1
            return $ n0 == n1 
                && (p0) `eq1` (p1) 
                && (s0) `eq1` (s1)
        where
            sameType :: ( LivenessRule rule0
                        , LivenessRule rule1 )
                     => rule0 -> rule1
                     -> Maybe (rule0 :~: rule1)
            sameType _ _ = eqT

instance Show ProofTree where
    show (ProofNode n p s) = printf "ProofNode (%s) (%s) (%s)" 
            (show n) (show1 p) (show1 s)

instance NFData ProofTree where
    rnf (ProofNode n p s) = n `deepseq` p `deepseq1` s `deepseq1` ()

foldProof :: Fold ProofTree ARule
foldProof f (ProofNode n ps _) = contramap (const ((),())) $ 
                                     (,) <$> (const () <$> f (makeCell n))
                                         <*> (const () <$> (traverse._2.foldProof) f ps) 

instance ReferencesProgress ProofTree where
    traverseProgId f (ProofNode n p s) = 
            ProofNode <$> travRefs' f n
                      <*> (traverse._2.traverseProgId) f p
                      <*> pure s

traverseSafetyRef :: Traversal' ProofTree Label
traverseSafetyRef f (ProofNode n p s) = 
        ProofNode n <$> (traverse._2.traverseSafetyRef) f p
                    <*> (traverse._2.traverse) f s

instance ReferencesEvents ProofTree where
    traverseEvents f (ProofNode n p s) = 
        ProofNode <$> travEvent' f n
                  <*> (traverse._2.traverseEvents) f p
                  <*> pure s

supporting_evts :: ProofTree
                -> [EventId]
supporting_evts = nubSort . view (partsOf traverseEvents)

traverseSubproofs :: Traversal' ProofTree ProofTree
traverseSubproofs f (ProofNode n p s) = 
        ProofNode n <$> (traverse._2) f p
                    <*> pure s

traverseProgress :: Traversal' ProofTree RawProgressProp
traverseProgress f (ProofNode n p s) = 
        ProofNode n <$> traverse g p
                    <*> pure s
    where
        g (p,t) = (,) <$> f p <*> traverseProgress f t

traverse' :: (Foldable t, Applicative f,Contravariant f) 
          => (a -> f b) -> t a -> f (t b)
traverse' f x = contramap (const ()) $ traverse_ f x

traverseSafety :: Traversal' ProofTree RawSafetyProp
traverseSafety f (ProofNode n p s) = 
        ProofNode n <$> (traverse._2.traverseSafety) f p
                    <*> (traverse._1) f s

makeRule :: ( LivenessRulePO rule
        , ProgressHyp rule ~ Const ()
        , SafetyHyp rule ~ Const ()) 
     => rule -> ProofTree
makeRule r = ProofNode r (Const ()) (Const ())

makeRule' :: ( LivenessRulePO rule
         , ProgressHyp rule ~ One
         , SafetyHyp rule ~ Const ()) 
      => rule -> ProgId -> RawProgressProp -> ProofTree
makeRule' r pid p = ProofNode r (Identity (p, makeRule $ Reference pid)) (Const ())

instance LivenessRulePO Reference where
    liveness_po _ (Reference _) (Const ()) (Const ()) = return ()
