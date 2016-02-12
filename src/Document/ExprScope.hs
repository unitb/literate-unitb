{-# LANGUAGE ExistentialQuantification
        , TypeOperators
        , OverloadedStrings
        , TypeFamilies           
        #-}
module Document.ExprScope where

    -- Modules
import Document.Scope
import Document.Phase.Types

import UnitB.Expr hiding (Const)
import UnitB.Syntax 

    -- Libraries
import Control.Lens
import Control.Monad.Reader

import Data.Hashable
import Data.List.NonEmpty as NE (toList)
import Data.Maybe as M
import Data.Typeable

import Test.QuickCheck

import Utilities.Existential
import Utilities.HeterogenousEquality
import Utilities.Instances
import Utilities.Regression
import Utilities.Syntactic
import Utilities.Table

data CoarseSchedule = CoarseSchedule 
        { _coarseScheduleInhStatus :: EventInhStatus Expr
        , _coarseScheduleDeclSource :: DeclSource
        , _coarseScheduleLineInfo :: LineInfo
        } deriving (Eq,Ord,Typeable,Show,Generic)
data FineSchedule = FineSchedule 
        { _fineScheduleInhStatus :: EventInhStatus Expr
        , _fineScheduleDeclSource :: DeclSource
        , _fineScheduleLineInfo :: LineInfo
        } deriving (Eq,Ord,Typeable,Show,Generic)
data Guard = Guard 
        { _guardInhStatus :: EventInhStatus Expr
        , _guardDeclSource :: DeclSource
        , _guardLineInfo :: LineInfo
        } deriving (Eq,Ord,Typeable,Show,Generic)
data Witness = Witness 
        { _witnessVar :: Var
        , _witnessEvtExpr :: Expr 
        , _witnessDeclSource :: DeclSource
        , _witnessLineInfo :: LineInfo
        } deriving (Eq,Ord,Typeable,Show,Generic)
data IndexWitness = IndexWitness 
        { _indexWitnessVar :: Var
        , _indexWitnessEvtExpr :: Expr 
        , _indexWitnessDeclSource :: DeclSource
        , _indexWitnessLineInfo :: LineInfo
        } deriving (Eq,Ord,Typeable,Show,Generic)
data ActionDecl = Action 
        { _actionDeclInhStatus :: EventInhStatus Action
        , _actionDeclDeclSource :: DeclSource
        , _actionDeclLineInfo :: LineInfo
        } deriving (Eq,Ord,Typeable,Show,Generic)


makeFields ''CoarseSchedule
makePrisms ''CoarseSchedule
makeFields ''FineSchedule
makeFields ''Guard
makeFields ''ActionDecl
makeFields ''Witness
makeFields ''IndexWitness

newtype ExprScope = ExprScope { _exprScopeCell :: Cell IsExprScope }
    deriving Typeable

class ( Scope a, Typeable a, Show a, PrettyPrintable a )
        => IsExprScope a where
    toMchExpr :: Label -> a 
              -> Reader MachineP2 [Either Error (MachineP3'Field ae ce t)]
    toThyExpr :: Label -> a -> Reader TheoryP2 [Either Error TheoryP3Field]
    toNewEvtExpr :: Label -> a 
                 -> Reader MachineP2 [Either Error (EventId, [EventP3Field])]
    toNewEvtExprDefault :: Label -> a 
                 -> Reader MachineP2 [Either Error (EventId, [EventP3Field])]
    toOldEvtExpr :: Label -> a 
                 -> Reader MachineP2 [Either Error (EventId, [EventP3Field])]
    toOldPropSet :: Label -> a 
                 -> Reader MachineP2 [Either Error PropertySetField]
    toNewPropSet :: Label -> a 
                 -> Reader MachineP2 [Either Error PropertySetField]

makeFields ''ExprScope
makePrisms ''ExprScope

newtype EvtExprScope = EvtExprScope { _evtExprScopeCell :: Cell IsEvtExpr } 
    deriving (Typeable)

instance Eq EvtExprScope where
    (==) = read2CellsWith' (==) False

instance Ord EvtExprScope where
    compare = read2CellsH' h_compare

instance Show EvtExprScope where
    show = readCell' show

instance PrettyPrintable EvtExprScope where
    pretty = readCell' pretty

newtype LensT a b = LensT { getLens :: Lens' a b }


class ( Eq a, Ord a, Typeable a
      , Show a, Scope a
      , PrettyPrintable a
      , HasLineInfo a LineInfo
      , HasDeclSource a DeclSource ) => IsEvtExpr a where
    toMchScopeExpr :: Label -> a 
                   -> Reader MachineP2 [Either Error (MachineP3'Field ae ce t)]
    toEvtScopeExpr :: RefScope -> EventId -> Label -> a
                   -> Reader MachineP2 [Either Error (EventId,[EventP3Field])]
    defaultEvtWitness :: EventId -> a 
                      -> Reader MachineP2 [Either Error (EventId,[EventP3Field])]
    setSource :: EventId -> a -> a
    default setSource :: HasInhStatus a (EventInhStatus b)
                      => EventId -> a -> a
    setSource ev x = x & inhStatus.traverse._1 .~ (ev :| [])
    inheritedFrom :: a -> [EventId]
    default inheritedFrom :: HasInhStatus a (EventInhStatus b) => a -> [EventId]
    inheritedFrom = fromMaybe [].fmap (NE.toList.fst).contents

makeFields ''EvtExprScope
makePrisms ''EvtExprScope

instance IsEvtExpr EvtExprScope where
    toMchScopeExpr lbl x = readCell' (toMchScopeExpr lbl) x
    toEvtScopeExpr ref e lbl x = readCell' (toEvtScopeExpr ref e lbl) x
    defaultEvtWitness ev x = readCell' (defaultEvtWitness ev) x
    setSource ev x = mapCell' (setSource ev) x
    inheritedFrom x = readCell' inheritedFrom x

instance HasDeclSource EvtExprScope DeclSource where
    declSource f = traverseCell' (declSource f)

instance HasLineInfo EvtExprScope LineInfo where
    lineInfo f = traverseCell' (lineInfo f)

type InitOrEvent = Either InitEventId EventId

data InitEventId = InitEvent
    deriving (Show,Ord,Eq,Generic)

data EventExpr = EventExpr { _eventExprs :: Table InitOrEvent EvtExprScope }
    deriving (Eq,Ord,Typeable,Show)

makeLenses ''EventExpr
makePrisms ''EventExpr

instance Hashable InitEventId where

data Invariant = Invariant 
        { _invariantMchExpr :: Expr
        , _invariantDeclSource :: DeclSource
        , _invariantLineInfo :: LineInfo
        } deriving (Eq,Ord,Typeable,Show,Generic)
data InvTheorem = InvTheorem 
        { _invTheoremMchExpr :: Expr
        , _invTheoremDeclSource :: DeclSource
        , _invTheoremLineInfo :: LineInfo
        } deriving (Eq,Ord,Typeable,Show,Generic)
data TransientProp = TransientProp
        { _transientPropMchExpr :: Transient
        , _transientPropDeclSource :: DeclSource
        , _transientPropLineInfo :: LineInfo
        } deriving (Eq,Ord,Typeable,Show,Generic)
data ConstraintProp = ConstraintProp
        { _constraintPropMchExpr :: Constraint
        , _constraintPropDeclSource :: DeclSource
        , _constraintPropLineInfo :: LineInfo
        } deriving (Eq,Ord,Typeable,Show,Generic)
data SafetyDecl = SafetyProp
        { _safetyDeclMchExpr :: SafetyProp
        , _safetyDeclDeclSource :: DeclSource
        , _safetyDeclLineInfo :: LineInfo
        } deriving (Eq,Ord,Typeable,Show,Generic)
data ProgressDecl = ProgressProp
        { _progressDeclMchExpr :: ProgressProp
        , _progressDeclDeclSource :: DeclSource
        , _progressDeclLineInfo :: LineInfo
        } deriving (Eq,Ord,Typeable,Show,Generic)
data Initially = Initially
            { _initiallyInhStatus  :: InhStatus Expr
            , _initiallyDeclSource :: DeclSource
            , _initiallyLineInfo   :: LineInfo
            } deriving (Eq,Ord,Typeable,Show,Generic)
data Axiom = Axiom
        { _axiomMchExpr :: Expr
        , _axiomDeclSource :: DeclSource
        , _axiomLineInfo :: LineInfo
        } deriving (Eq,Ord,Typeable,Show,Generic)

makeFields ''Axiom
makeFields ''ProgressDecl
makeFields ''Initially
makeFields ''SafetyDecl
makeFields ''ConstraintProp
makeFields ''TransientProp
makeFields ''Invariant
makeFields ''InvTheorem

pCast :: (Typeable a, Typeable b) => Traversal' a b
pCast f x = maybe (pure x) (pCast_aux f x) eqT

pCast_aux :: (a -> f a) -> b -> (a :~: b) -> f b
pCast_aux f x Refl = f x

delegate :: (forall a. IsExprScope a => lbl -> a -> b) -> lbl -> ExprScope -> b
delegate f lbl x = readCell' (f lbl) x

instance IsExprScope ExprScope where
    toMchExpr = delegate toMchExpr
    toThyExpr = delegate toThyExpr
    toNewPropSet = delegate toNewPropSet
    toOldPropSet = delegate toOldPropSet
    toNewEvtExpr = delegate toNewEvtExpr
    toNewEvtExprDefault = delegate toNewEvtExprDefault
    toOldEvtExpr = delegate toOldEvtExpr

instance Eq ExprScope where
    (==) = read2CellsWith' (==) False

instance Ord ExprScope where
    compare = read2CellsH' h_compare

instance PrettyPrintable ExprScope where
    pretty = readCell' pretty

instance Scope CoarseSchedule where
    type Impl CoarseSchedule = Redundant Expr (WithDelete CoarseSchedule)
    kind x = case x ^. inhStatus of
                InhDelete _ -> "deleted coarse schedule"
                InhAdd _ -> "coarse schedule"
    rename_events' _ e = [e]

instance Scope FineSchedule where
    type Impl FineSchedule = Redundant Expr (WithDelete FineSchedule)
    kind x = case x ^. inhStatus of
                InhDelete _ -> "deleted fine schedule"
                InhAdd _ -> "fine schedule"
    rename_events' _ e = [e]

instance Scope Guard where
    type Impl Guard = Redundant Expr (WithDelete Guard)
    kind x = case x ^. inhStatus of
                InhDelete _ -> "deleted guard"
                InhAdd _ -> "guard"    
    rename_events' _ e = [e]

instance Scope Witness where
    kind _ = "witness"
    rename_events' _ e = [e]

instance Scope IndexWitness where
    kind _ = "witness (index)"
    rename_events' _ e = [e]

instance Scope ActionDecl where
    type Impl ActionDecl = Redundant Action (WithDelete ActionDecl)
    kind x = case x ^. inhStatus of
                InhDelete _ -> "delete action"
                InhAdd _ -> "action"
    rename_events' _ e = [e]

instance Scope EvtExprScope where
    keep_from s = traverseCell' (keep_from s)
    make_inherited = traverseCell' make_inherited
    error_item = readCell' error_item
    merge_scopes' = apply2Cells' merge_scopes' Nothing
    rename_events' m = traverseCell' (rename_events' m)
    kind = readCell' kind


instance Scope ExprScope where
    keep_from s = traverseCell' (keep_from s)
    make_inherited = traverseCell' make_inherited
    error_item = readCell' error_item
    merge_scopes' = apply2Cells' merge_scopes' Nothing
    rename_events' m = traverseCell' (rename_events' m)
    kind = readCell' kind

instance Show ExprScope where
    show = readCell' show

instance Arbitrary CoarseSchedule where
    arbitrary = genericArbitrary

instance Arbitrary FineSchedule where
    arbitrary = genericArbitrary

instance Arbitrary Guard where
    arbitrary = genericArbitrary

instance Arbitrary ActionDecl where
    arbitrary = genericArbitrary

instance Arbitrary Witness where
    arbitrary = genericArbitrary

instance Arbitrary IndexWitness where
    arbitrary = genericArbitrary

instance Arbitrary TransientProp where
    arbitrary = genericArbitrary

instance Arbitrary Invariant where
    arbitrary = genericArbitrary
instance Arbitrary InvTheorem where
    arbitrary = genericArbitrary
instance Arbitrary ConstraintProp where
    arbitrary = genericArbitrary
instance Arbitrary SafetyDecl where
    arbitrary = genericArbitrary
instance Arbitrary ProgressDecl where
    arbitrary = genericArbitrary
instance Arbitrary Initially where
    arbitrary = genericArbitrary
instance Arbitrary Axiom where
    arbitrary = genericArbitrary
instance Arbitrary InitEventId where
    arbitrary = genericArbitrary

prop_axiom_Scope_mergeCommutative :: Property
prop_axiom_Scope_mergeCommutative = regression (uncurry axiom_Scope_mergeCommutative) [(g0,g1)]
    where
        g0 = Guard {_guardInhStatus = InhAdd ("i" :| [],zfalse), _guardDeclSource = Inherited, _guardLineInfo = (LI "file" 0 0)}
        g1 = Guard {_guardInhStatus = InhAdd ("e" :| [],zfalse), _guardDeclSource = Local, _guardLineInfo = (LI "file" 0 0)}

return []

run_tests :: IO Bool
run_tests = $quickCheckAll
