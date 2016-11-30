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
module UnitB.Proof 
    ( module UnitB.Proof 
    , module UnitB.Proof.Rules
    , module UnitB.Proof.PO
    , Proxy(..)
    , One,None,NonEmpty
    , HasGoal(..)
    )
where

    -- Modules
import Logic.Expr as E hiding (Context)
import Logic.Proof

import UnitB.Proof.Rules
import UnitB.Proof.PO
import UnitB.Property

    -- Libraries
import Control.Applicative
import Control.Arrow
import Control.Arrow.Unfold
import Control.Category
import Control.DeepSeq
import Control.Lens 
import Control.Monad

import Data.Constraint
import Data.Existential
import Data.Factory
import Data.ForallInstances
import Data.Functor.Compose
#if MIN_VERSION_transformers(0,5,0)
import Prelude.Extras hiding (Lift1)
#else
import Data.Functor.Classes
#endif
import Data.Foldable as F
import Data.List.Ordered
import Data.Maybe
import Data.Proxy.TH
import Data.Serialize hiding (label)
import Data.Typeable
import Data.Unfoldable

import GHC.Generics.Instances

import Prelude hiding (id,(.))

import Test.QuickCheck.ZoomEq

import Text.Printf

import Utilities.Syntactic

rule_name :: LivenessRule rule => rule -> Label
rule_name = rule_name' . (id :: Proxy rule -> Proxy rule) . pure

buildProgress :: Builder rule (ProgressHyp rule)
buildProgress = build "liveness"

buildSafety :: Builder rule (SafetyHyp rule)
buildSafety = build "safety"

buildTransient :: Builder rule (TransientHyp rule)
buildTransient = build "transient"

build :: forall t r. String -> Builder r t
build kind _foo m = proc (st,_r,li) -> do
        let e = Left [Error (printf "expecting %s %s assumptions" expSize kind) li]
            unfInst = _foo^.entailsToDictFun $ dict _r
            expSize = (\Dict -> expectedSize [pr|t|]) unfInst
        xs <- fixExA' m -< (unfInst,st)
        returnA -< maybe e Right xs
    where

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
    } deriving (Generic)

instance LivenessRule rule => Show (Inference rule) where
    show (Inference x y z v w) = printf "%s (%s) (%s) (%s) (%s)" 
            (show x)
            (show y)
            (show1 z)
            (show1 v)
            (show1 w)

#if MIN_VERSION_transformers(0,5,0)
eq1 :: (Eq1 f,Eq a) => f a -> f a -> Bool
eq1 = (==#)
#endif

instance LivenessRule rule => Eq (Inference rule) where
    Inference x0 y0 z0 v0 w0 == Inference x1 y1 z1 v1 w1 = 
            x0  ==  x1 &&
            y0  ==  y1 &&
            z0 `eq1` z1 &&
            v0 `eq1` v1 &&
            w0 `eq1` w1

--data ProofTree = forall rule. LivenessRulePO rule => ProofNode (Inference rule)
newtype ProofTree = ProofTree { _proofTreeCell :: Cell1 Inference LivenessRulePO }
    deriving Generic

makeFactory ''LivenessRulePO
makeFields ''ARule
makeLenses ''Inference
makeFields ''Inference
makeFields ''ProofTree

instance ZoomEq ProofTree where
    (.==) = cell1ZoomEqual' (.==)

instance Serialize ProofTree where
    put = putCell1 put . view cell
    get = view (from cell) <$> getCell1 get

instance HasGoal ProofTree RawProgressProp where
    goal f = traverseCell1' (goal f)

class HasRuleLens proof0 proof1 rule0 rule1 | proof0 -> rule0, proof1 -> rule1 where
     ruleLens :: Lens proof0 proof1 rule0 rule1

class HasRule proof rule | proof -> rule where
     rule :: Getter proof rule

voidInference :: (HasExpr expr,LivenessRule rule)
              => LivenessRule rule :- constr rule
              -> ProgressProp' expr
              -> Proxy rule
              -> Maybe (Cell1 (Compose Inference Proxy) constr)
voidInference d prog rule = voidInference' d prog rule 
    (\p r -> Compose $ Inference p r Proxy Proxy Proxy)

instance 
        ( ProgressHyp rule0 ~ ProgressHyp rule1
        , SafetyHyp rule0 ~ SafetyHyp rule1
        , TransientHyp rule0 ~ TransientHyp rule1 )
    => HasRuleLens (Inference rule0) (Inference rule1) rule0 rule1 where
        ruleLens f (Inference g r ps ts safs) = (\r' -> Inference g r' ps ts safs) <$> f r

instance (LivenessRule rule) 
      => ZoomEq (Inference rule) where
    (.==) = useInst x $ useInst y $ useInst z $ genericZoomEq
      where
        x = Proxy :: Proxy (ZoomEq (ProgressHyp rule ProofTree))
        y = Proxy :: Proxy (ZoomEq (SafetyHyp rule (RawSafetyProp, Maybe Label)))
        z = Proxy :: Proxy (ZoomEq (TransientHyp rule RawTransient))

instance HasRule (Inference rule) rule where
    rule = ruleLens
instance HasRule ProofTree ARule where
    rule = to $ readCell1' $ makeCell . view rule

instance Show ProofTree where
    showsPrec n = readCell1' (showsPrec n)

instance NFData ProofTree where
    rnf = readCell1' $ \(Inference x y z v w) -> 
            x `deepseq` 
            y `deepseq` 
            z `deepseq1` 
            v `deepseq1` 
            w `deepseq1` ()

instance Eq ProofTree where
    (==) = cell1Equal' (==)

instance LivenessRule rule => PrettyPrintable (Inference rule) where
    pretty (Inference x y z v w) = printf "%s (%s) (%s) (%s) (%s)" 
            (pretty x)
            (show y)
            (show1 $ Pretty <$> z)
            (show1 $ Pretty <$> v)
            (show1 $ first Pretty <$> w)

instance LivenessRule rule => Tree (Inference rule) where
    rewriteM _ = pure
    as_tree' (Inference g r ps ts ss) = E.List <$> sequenceA 
        [ pure $ Str (pretty g)
        , pure $ Str (pretty $ rule_name r)
        , E.List . concat <$> sequenceA
            [ traverse as_tree' $ F.toList ps 
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

instance (Serialize a,LivenessRule a) => Serialize (Inference a) where
    put (Inference p r x y z) = do
          put p
          put r
          put1 x
          put1 y
          put1 z
    get = Inference <$> get <*> get <*> get1 <*> get1 <*> get1
