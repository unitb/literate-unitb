{-# LANGUAGE ExistentialQuantification      #-}
{-# LANGUAGE RankNTypes,DeriveDataTypeable  #-}
{-# LANGUAGE TemplateHaskell,MultiParamTypeClasses   #-}
{-# LANGUAGE FunctionalDependencies,FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances,FlexibleInstances  #-}
{-# LANGUAGE TypeFamilies, DefaultSignatures  #-}
module Document.ExprScope where

    -- Modules
import Document.Scope
import Document.Phase

import UnitB.AST 
import UnitB.Expr hiding (Const)

    -- Libraries
import Control.Applicative
import Control.Lens
import Control.Monad.Reader

import Data.List.NonEmpty as NE (NonEmpty(..),toList)
import Data.Map as M hiding (mapMaybe)
import Data.Maybe as M
import Data.Typeable

import Utilities.HeterogenousEquality
import Utilities.Syntactic
import Utilities.TH

data CoarseSchedule = CoarseSchedule 
        { _coarseScheduleInhStatus :: EventInhStatus Expr
        , _coarseScheduleDeclSource :: DeclSource
        , _coarseScheduleLineInfo :: LineInfo
        } deriving (Eq,Ord,Typeable,Show)
data FineSchedule = FineSchedule 
        { _fineScheduleInhStatus :: EventInhStatus Expr
        , _fineScheduleDeclSource :: DeclSource
        , _fineScheduleLineInfo :: LineInfo
        } deriving (Eq,Ord,Typeable,Show)
data Guard = Guard 
        { _guardInhStatus :: EventInhStatus Expr
        , _guardDeclSource :: DeclSource
        , _guardLineInfo :: LineInfo
        } deriving (Eq,Ord,Typeable,Show)
data Witness = Witness 
        { _witnessVar :: Var
        , _witnessEvtExpr :: Expr 
        , _witnessDeclSource :: DeclSource
        , _witnessLineInfo :: LineInfo
        } deriving (Eq,Ord,Typeable,Show)
data ActionDecl = Action 
        { _actionDeclInhStatus :: EventInhStatus Action
        , _actionDeclDeclSource :: DeclSource
        , _actionDeclLineInfo :: LineInfo
        } deriving (Eq,Ord,Typeable,Show)


makeFields ''CoarseSchedule
makeFields ''FineSchedule
makeFields ''Guard
makeFields ''ActionDecl
makeFields ''Witness


data EvtExprScope = forall a. IsEvtExpr a => EvtExprScope a
    deriving (Typeable)

instance Eq EvtExprScope where
    EvtExprScope x == EvtExprScope y = h_equal x y

instance Ord EvtExprScope where
    compare (EvtExprScope x) (EvtExprScope y) = h_compare x y

instance Show EvtExprScope where
    show (EvtExprScope x) = show x


newtype LensT a b = LensT { getLens :: Lens' a b }


data RefScope = Old | New

class ( Eq a, Ord a, Typeable a
      , Show a, Scope a
      , HasLineInfo a LineInfo
      , HasDeclSource a DeclSource ) => IsEvtExpr a where
    toMchScopeExpr :: Label -> a 
                   -> Reader MachineP2 [Either Error (MachineP3'Field b c)]
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

instance IsEvtExpr EvtExprScope where
    toMchScopeExpr lbl (EvtExprScope x) = toMchScopeExpr lbl x
    toEvtScopeExpr ref e lbl (EvtExprScope x) = toEvtScopeExpr ref e lbl x
    defaultEvtWitness ev (EvtExprScope x) = defaultEvtWitness ev x
    setSource ev (EvtExprScope x) = EvtExprScope $ setSource ev x
    inheritedFrom (EvtExprScope x) = inheritedFrom x

instance HasDeclSource EvtExprScope DeclSource where
    declSource f (EvtExprScope x) = EvtExprScope <$> declSource f x

instance HasLineInfo EvtExprScope LineInfo where
    lineInfo f (EvtExprScope x) = EvtExprScope <$> lineInfo f x

data InitEventId = InitEvent
    deriving (Show,Ord,Eq)

data EventExpr = EventExpr (Map (Either InitEventId EventId) EvtExprScope)
    deriving (Eq,Ord,Typeable,Show)



data Invariant = Invariant 
        { _invariantMchExpr :: Expr
        , _invariantDeclSource :: DeclSource
        , _invariantLineInfo :: LineInfo
        } deriving (Eq,Ord,Typeable,Show)
data InvTheorem = InvTheorem 
        { _invTheoremMchExpr :: Expr
        , _invTheoremDeclSource :: DeclSource
        , _invTheoremLineInfo :: LineInfo
        } deriving (Eq,Ord,Typeable,Show)
data TransientProp = TransientProp
        { _transientPropMchExpr :: Transient
        , _transientPropDeclSource :: DeclSource
        , _transientPropLineInfo :: LineInfo
        } deriving (Eq,Ord,Typeable,Show)
data ConstraintProp = ConstraintProp
        { _constraintPropMchExpr :: Constraint
        , _constraintPropDeclSource :: DeclSource
        , _constraintPropLineInfo :: LineInfo
        } deriving (Eq,Ord,Typeable,Show)
data SafetyDecl = SafetyProp
        { _safetyDeclMchExpr :: SafetyProp
        , _safetyDeclDeclSource :: DeclSource
        , _safetyDeclLineInfo :: LineInfo
        } deriving (Eq,Ord,Typeable,Show)
data ProgressDecl = ProgressProp
        { _progressDeclMchExpr :: ProgressProp
        , _progressDeclDeclSource :: DeclSource
        , _progressDeclLineInfo :: LineInfo
        } deriving (Eq,Ord,Typeable,Show)
data Initially = Initially
            { _initiallyInhStatus  :: InhStatus Expr
            , _initiallyDeclSource :: DeclSource
            , _initiallyLineInfo   :: LineInfo
            } deriving (Eq,Ord,Typeable,Show)
data Axiom = Axiom
        { _axiomMchExpr :: Expr
        , _axiomDeclSource :: DeclSource
        , _axiomLineInfo :: LineInfo
        } deriving (Eq,Ord,Typeable,Show)

makeFields ''Axiom
makeFields ''ProgressDecl
makeFields ''Initially
makeFields ''SafetyDecl
makeFields ''ConstraintProp
makeFields ''TransientProp
makeFields ''Invariant
makeFields ''InvTheorem

class ( Scope a, Typeable a, Show a )
        => IsExprScope a where
    -- parseExpr :: [(Label, a)] -> RWS () [Error] MachineP3 ()
    toMchExpr :: Label -> a 
              -> Reader MachineP2 [Either Error (MachineP3'Field b c)]
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

delegate :: (forall a. IsExprScope a => lbl -> a -> b) -> lbl -> ExprScope -> b
delegate f lbl (ExprScope x) = f lbl x

instance IsExprScope ExprScope where
    toMchExpr = delegate toMchExpr
    toThyExpr = delegate toThyExpr
    toNewPropSet = delegate toNewPropSet
    toOldPropSet = delegate toOldPropSet
    toNewEvtExpr = delegate toNewEvtExpr
    toNewEvtExprDefault = delegate toNewEvtExprDefault
    toOldEvtExpr = delegate toOldEvtExpr

data ExprScope = forall t. IsExprScope t => ExprScope t
    deriving Typeable

instance Eq ExprScope where
    ExprScope x == ExprScope y = h_equal x y

instance Ord ExprScope where
    compare (ExprScope x) (ExprScope y) = h_compare x y



existential ''ExprScope
existential ''EvtExprScope


instance Scope CoarseSchedule where
    type Impl CoarseSchedule = Redundant Expr (WithDelete CoarseSchedule)
    kind x = case x ^. inhStatus of
                InhDelete _ -> "deleted coarse schedule"
                InhAdd _ -> "coarse schedule"
    rename_events _ x = [x]

instance Scope FineSchedule where
    type Impl FineSchedule = Redundant Expr (WithDelete FineSchedule)
    kind x = case x ^. inhStatus of
                InhDelete _ -> "deleted fine schedule"
                InhAdd _ -> "fine schedule"
    rename_events _ x = [x]

instance Scope Guard where
    type Impl Guard = Redundant Expr (WithDelete Guard)
    kind x = case x ^. inhStatus of
                InhDelete _ -> "deleted guard"
                InhAdd _ -> "guard"    
    rename_events _ x = [x]

instance Scope Witness where
    kind _ = "witness"
    rename_events _ x = [x]

instance Scope ActionDecl where
    type Impl ActionDecl = Redundant Action (WithDelete ActionDecl)
    kind x = case x ^. inhStatus of
                InhDelete _ -> "delete action"
                InhAdd _ -> "action"
    rename_events _ x = [x]

instance Scope EvtExprScope where
    keep_from s x = applyEvtExprScope (keep_from s) x
    make_inherited e = applyEvtExprScope make_inherited e
    error_item e = readEvtExprScope error_item e
    clashes x y = fromMaybe True $ getConst <$> apply2EvtExprScope (fmap Const <$> clashes) x y
    merge_scopes x y = fromMaybe err $ runIdentity <$> apply2EvtExprScope (fmap Identity <$> merge_scopes) x y
        where
            err = error "EvtExprScope Scope.merge_scopes: _, _"
    rename_events m = applyEvtExprScope (rename_events m)
    kind (EvtExprScope e) = kind e

instance Scope ExprScope where
    keep_from s x = applyExprScope (keep_from s) x
    make_inherited e = applyExprScope make_inherited e
    error_item e = readExprScope (error_item) e
    clashes x y = fromMaybe True $ getConst <$> apply2ExprScope (fmap Const <$> clashes) x y
    merge_scopes x y = fromMaybe err $ runIdentity <$> apply2ExprScope (fmap Identity <$> merge_scopes) x y
        where
            err = error "ExprScope Scope.merge_scopes: _, _"
    rename_events m = applyExprScope (rename_events m)
    kind _ = "event"

instance Show ExprScope where
    show (ExprScope x) = show x
