{-# LANGUAGE KindSignatures
        , GADTs, TypeOperators
        , Arrows
        , PatternSynonyms
        , ScopedTypeVariables
        , ConstraintKinds
        , TypeFamilies
        , StandaloneDeriving
        #-}
module UnitB.Proof 
    ( module UnitB.Proof 
    , Proxy(..)
    , One,None,NonEmpty
    , HasGoal(..)
    )
where

    -- Modules
import Logic.Expr as E hiding (Context,Const)
import Logic.Proof
import Logic.Proof.POGenerator
import UnitB.Property

    -- Libraries
import Control.Applicative
import Control.Arrow
import Control.Arrow.Unfold
import Control.Category
import Control.DeepSeq
import Control.Lens 
import Control.Monad

import Data.Default
import Data.Existential
import Data.Functor.Compose
import Data.Functor.Classes
import Data.Foldable as F
import Data.List.Ordered
import Data.Maybe
import Data.Proxy.TH
import Data.Typeable
import Data.Unfoldable

import GHC.Generics.Instances

import Prelude hiding (id,(.))
import Text.Printf

import Utilities.Syntactic

type Builder r t = forall arr a b constr. ArrowUnfold arr 
               => (constr r :- Unfoldable t)
               -> arr b (Maybe a) 
               -> arr (b,Inst1 Proxy constr r,LineInfo) (Either [Error] (t a))

class ( Eq rule
      , Eq1 (ProgressHyp rule)
      , Eq1 (SafetyHyp rule)
      , Eq1 (TransientHyp rule)
      , Typeable (ProgressHyp rule)
      , Typeable (SafetyHyp rule)
      , Typeable rule
      , Show rule
      , Show1 (ProgressHyp rule)
      , Show1 (SafetyHyp rule)
      , Show1 (TransientHyp rule)
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
    voidInference :: HasExpr expr
                  => (LivenessRule rule :- constr rule)
                  -> ProgressProp' expr
                  -> Proxy rule
                  -> Maybe (Cell1 (Compose Inference Proxy) constr)
    default voidInference :: ( HasExpr expr
                             , ProgressHyp rule ~ None
                             , SafetyHyp rule ~ None
                             , TransientHyp rule ~ None )
                          => (LivenessRule rule :- constr rule)
                          -> ProgressProp' expr
                          -> Proxy rule
                          -> Maybe (Cell1 (Compose Inference Proxy) constr)
    voidInference (Sub D) g r = Just $ Cell $ Compose $ Inference (getExpr <$> g) r Proxy Proxy Proxy

instance LivenessRule rule => LivenessRule (Proxy rule) where
    type ProgressHyp (Proxy rule) = ProgressHyp rule
    type SafetyHyp (Proxy rule) = SafetyHyp rule
    type TransientHyp (Proxy rule) = TransientHyp rule
    rule_name' = rule_name' . reproxy
    travEvent' _ = pure
    travRefs' _ = pure
    voidInference _ _ _ = Nothing

reproxy :: proxy (Proxy rule) -> Proxy rule
reproxy _ = Proxy

rule_name :: LivenessRule rule => rule -> Label
rule_name = rule_name' . (id :: Proxy rule -> Proxy rule) . pure

buildProgress :: Builder rule (ProgressHyp rule)
buildProgress = build "liveness"

buildSafety :: Builder rule (SafetyHyp rule)
buildSafety = build "safety"

buildTransient :: Builder rule (TransientHyp rule)
buildTransient = build "transient"

useDict :: (constr => r) -> Dict constr -> r
useDict x D = x

build :: forall t r. String -> Builder r t
build kind _foo m = proc (st,_r,li) -> do
        let e = Left [Error (printf "expecting %s %s assumptions" expSize kind) li]
            unfInst = _foo^.entailsToDictFun $ dict _r
            expSize = (\D -> expectedSize [pr|t|]) unfInst
        xs <- fixExA' m -< (unfInst,st)
        returnA -< maybe e Right xs
    where

class LivenessRule rule => LivenessRulePO rule  where
    liveness_po :: RawProgressProp 
                -> rule
                -> ProgressHyp rule RawProgressProp
                -> TransientHyp rule RawTransient
                -> SafetyHyp rule RawSafetyProp
                -> POGen ()
    automaticSafety :: RawProgressProp -> rule -> [RawSafetyProp]
    automaticTransient :: RawProgressProp -> rule -> [RawTransient]
    automaticSafety _ _ = []
    automaticTransient _ _ = []

data Reference = Reference (ProgId) 
    deriving (Eq,Generic,Typeable,Show)
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
instance LivenessRule Add where
    type ProgressHyp Add = None
    type SafetyHyp Add = None
    rule_name' _ = label "add"
    travRefs' _ = pure
    travEvent' _ = pure
instance NFData Add where

data Ensure = Ensure (NonEmpty EventId) (RawTrHint) 
    deriving (Eq,Generic,Typeable,Show)
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
instance LivenessRule Disjunction where
    type ProgressHyp Disjunction = NonEmpty
    type SafetyHyp Disjunction = None
    rule_name' _  = label "disjunction"
    travRefs' _ = pure
    travEvent' _ = pure
    voidInference _ _ _ = Nothing
instance NFData Disjunction where
instance Default Disjunction where
    def = genericDefault

data NegateDisjunct = NegateDisjunct 
    deriving (Eq,Generic,Typeable,Show)
instance LivenessRule NegateDisjunct where
    type ProgressHyp NegateDisjunct = One
    type SafetyHyp NegateDisjunct = None
    rule_name' _ = label "trading"
    travRefs' _ = pure
    travEvent' _ = pure
    voidInference _ _ _ = Nothing
instance NFData NegateDisjunct where
instance Default NegateDisjunct where
    def = genericDefault

data Transitivity = Transitivity 
    deriving (Eq,Generic,Typeable,Show)
instance LivenessRule Transitivity where
    type ProgressHyp Transitivity = NonEmpty
    type SafetyHyp Transitivity = None
    rule_name' _ = label "transitivity"
    travRefs' _ = pure
    travEvent' _ = pure
    voidInference _ _ _ = Nothing
instance NFData Transitivity where
instance Default Transitivity where
    def = genericDefault

data PSP = PSP 
    deriving (Eq,Generic,Typeable,Show)
instance LivenessRule PSP where
    type ProgressHyp PSP = One
    type SafetyHyp PSP = One
    rule_name' _ = label "PSP"
    travRefs' _ = pure
    travEvent' _ = pure
    voidInference _ _ _ = Nothing
instance NFData PSP where
instance Default PSP where
    def = genericDefault

data Induction = Induction Variant
    deriving (Eq,Generic,Typeable,Show)
instance LivenessRule Induction where
    type ProgressHyp Induction = One
    type SafetyHyp Induction = None
    rule_name' _  = label "induction"
    travRefs' _ = pure
    travEvent' _ = pure
    voidInference _ _ _ = Nothing
instance NFData Induction where

data Monotonicity = Monotonicity 
    deriving (Eq,Generic,Typeable,Show)
instance LivenessRule Monotonicity where
    type ProgressHyp Monotonicity = One
    type SafetyHyp Monotonicity = None
    rule_name' _ = label "monotonicity"
    travRefs' _ = pure
    travEvent' _ = pure
    voidInference _ _ _ = Nothing
instance NFData Monotonicity where
instance Default Monotonicity where
    def = genericDefault

data Discharge = Discharge
    deriving (Eq,Generic,Typeable,Show)
instance LivenessRule Discharge where
    type ProgressHyp Discharge = None
    type SafetyHyp Discharge = Maybe
    type TransientHyp Discharge = One
    rule_name' _ = label "discharge"
    travRefs' _ = pure
    travEvent' _ Discharge = pure Discharge
    voidInference _ _ _ = Nothing
instance NFData Discharge where 

travRefs :: Traversal' ARule ProgId
travRefs = cellLens' travRefs'

travEvent :: Traversal' ARule EventId
travEvent = cellLens' travEvent'

newtype ARule = ARule { _aRuleCell :: Cell LivenessRulePO }

data Inference rule = Inference 
    { _inferenceGoal :: RawProgressProp
    , rule' :: rule 
    , _progressHyps :: ProgressHyp rule ProofTree
    , _transientHyps :: TransientHyp rule RawTransient
    , _safetyHyps :: SafetyHyp rule (RawSafetyProp,Maybe Label)
    }

instance LivenessRule rule => Show (Inference rule) where
    show (Inference x y z v w) = printf "%s (%s) (%s) (%s) (%s)" 
            (show x)
            (show y)
            (show1 z)
            (show1 v)
            (show1 w)

instance LivenessRule rule => Eq (Inference rule) where
    Inference x0 y0 z0 v0 w0 == Inference x1 y1 z1 v1 w1 = 
            x0  ==  x1 &&
            y0  ==  y1 &&
            z0 `eq1` z1 &&
            v0 `eq1` v1 &&
            w0 `eq1` w1

--data ProofTree = forall rule. LivenessRulePO rule => ProofNode (Inference rule)
newtype ProofTree = ProofTree { _proofTreeCell :: Cell1 Inference LivenessRulePO }

makeFields ''ARule
makeLenses ''Inference
makeFields ''Inference
makeFields ''ProofTree

instance HasGoal ProofTree RawProgressProp where
    goal f = traverseCell1' (goal f)

class HasRuleLens proof0 proof1 rule0 rule1 | proof0 -> rule0, proof1 -> rule1 where
     ruleLens :: Lens proof0 proof1 rule0 rule1

class HasRule proof rule | proof -> rule where
     rule :: Getter proof rule

instance 
        ( ProgressHyp rule0 ~ ProgressHyp rule1
        , SafetyHyp rule0 ~ SafetyHyp rule1
        , TransientHyp rule0 ~ TransientHyp rule1 )
    => HasRuleLens (Inference rule0) (Inference rule1) rule0 rule1 where
        ruleLens f (Inference g r ps ts safs) = (\r' -> Inference g r' ps ts safs) <$> f r

instance HasRule (Inference rule) rule where
    rule = ruleLens
instance HasRule ProofTree ARule where
    rule = to $ readCell1' $ makeCell . view rule

instance Show ProofTree where
    showsPrec n = readCell1' (showsPrec n)

instance NFData ProofTree where
    rnf = readCell1' $ \(Inference x y z v w) -> 
            x `deepseq` 
            y `deepseq` 
            z `deepseq1` 
            v `deepseq1` 
            w `deepseq1` ()

instance Eq ProofTree where
    (==) = cell1Equal' (==)

instance LivenessRule rule => PrettyPrintable (Inference rule) where
    pretty (Inference x y z v w) = printf "%s (%s) (%s) (%s) (%s)" 
            (pretty x)
            (show y)
            (show1 $ Pretty <$> z)
            (show1 $ Pretty <$> v)
            (show1 $ first Pretty <$> w)

instance LivenessRule rule => Tree (Inference rule) where
    rewriteM _ = pure
    as_tree' (Inference g r ps ts ss) = E.List <$> sequenceA 
        [ pure $ Str (pretty g)
        , pure $ Str (pretty $ rule_name r)
        , E.List . concat <$> sequenceA
            [ traverse as_tree' $ F.toList ps 
            , traverse (pure . Str . pretty) $ F.toList ts 
            , traverse (pure . Str . pretty . fst) $ F.toList ss ] ]

instance PrettyPrintable ProofTree where
    pretty = pretty_print'

instance Tree ProofTree where
    rewriteM = traverseSubproofs
    as_tree' = readCell1' as_tree'

foldProof :: Fold ProofTree ARule
foldProof f = traverseCell1' $ \(Inference _ n ps _ _) -> 
                                   contramap (const ((),())) $ 
                                     (,) <$> (const () <$> f (makeCell n))
                                         <*> (const () <$> (traverse.foldProof) f ps) 

instance ReferencesProgress ProofTree where
    traverseProgId f = traverseCell1' $ \(Inference g n p s t) ->
            Inference g <$> travRefs' f n
                        <*> (traverse.traverseProgId) f p
                        <*> pure s
                        <*> pure t

traverseSafetyRef :: Traversal' ProofTree Label
traverseSafetyRef f = traverseCell1' $ \(Inference g n p t s) ->
        Inference g n <$> (traverse.traverseSafetyRef) f p
                      <*> pure t
                      <*> (traverse._2.traverse) f s

instance ReferencesEvents ProofTree where
    traverseEvents f = traverseCell1' $ \(Inference g n p t s) ->
        Inference g <$> travEvent' f n
                    <*> (traverse.traverseEvents) f p
                    <*> (traverse.traverseEvents) f t
                    <*> pure s

supporting_evts :: ProofTree
                -> [EventId]
supporting_evts = nubSort . view (partsOf traverseEvents)

traverseSubproofs :: Traversal' ProofTree ProofTree
traverseSubproofs f = traverseCell1' $ \(Inference g n p t s) ->
        Inference g n <$> traverse f p
                      <*> pure t
                      <*> pure s

traverseProgress :: Traversal' ProofTree RawProgressProp
traverseProgress f = traverseCell1' $ \(Inference g n p t s) ->
        Inference <$> f g
                  <*> pure n 
                  <*> (traverse.traverseProgress) f p
                  <*> pure t
                  <*> pure s
    where
        --h t = (,) <$> f p <*> traverseProgress f t

traverse' :: (Foldable t, Applicative f,Contravariant f) 
          => (a -> f b) -> t a -> f (t b)
traverse' f x = contramap (const ()) $ traverse_ f x

traverseSafety :: Traversal' ProofTree RawSafetyProp
traverseSafety f = traverseCell1' $ \(Inference g n p t s) ->
        Inference g n <$> (traverse.traverseSafety) f p
                      <*> pure t
                      <*> (traverse._1) f s

proofNode :: (LivenessRulePO rule,HasExpr expr)
          => ProgressProp' expr
          -> rule 
          -> ProgressHyp  rule ProofTree
          -> TransientHyp rule RawTransient
          -> SafetyHyp rule (RawSafetyProp, Maybe Label)
          -> ProofTree
proofNode g r p t s = makeCell1 $ Inference (getExpr <$> g) r p t s

makeMonotonicity :: (HasExpr expr,LivenessRulePO Monotonicity)
                 => ProgressProp' expr -> ProofTree -> ProofTree
makeMonotonicity g proof = proofNode (getExpr <$> g) Monotonicity (Identity proof) Proxy Proxy

makeRule :: ( LivenessRulePO rule
        , ProgressHyp rule ~ None
        , TransientHyp rule ~ None
        , HasExpr expr
        , SafetyHyp rule ~ None) 
     => rule 
     -> ProgressProp' expr
     -> ProofTree
makeRule r g = proofNode (getExpr <$> g) r Proxy Proxy Proxy

makeRule' :: ( LivenessRulePO rule
         , ProgressHyp rule ~ One
         , TransientHyp rule ~ None
         , SafetyHyp rule ~ None
         , HasExpr expr0 
         , HasExpr expr1 ) 
      => rule 
      -> ProgressProp' expr0
      -> ProgId 
      -> ProgressProp' expr1
      -> ProofTree
makeRule' r g pid p = proofNode g r (Identity (makeRule (Reference pid) p)) Proxy Proxy

instance LivenessRulePO Reference where
    liveness_po _ (Reference _) Proxy Proxy Proxy = return ()
