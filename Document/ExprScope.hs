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

import Logic.Expr hiding (Const)

import UnitB.AST 

    -- Libraries
import Control.Applicative
import Control.Lens
import Control.Monad.Reader

import Data.Map as M hiding (mapMaybe)
import Data.Maybe as M
import Data.Typeable

import Utilities.HeterogenousEquality
import Utilities.Syntactic
import Utilities.TH

data CoarseSchedule = CoarseSchedule 
        { _coarseScheduleInhStatus :: InhStatus Expr
        , _coarseScheduleDeclSource :: DeclSource
        , _coarseScheduleLineInfo :: LineInfo
        , _coarseScheduleExprStore :: [(Expr,[String])] }
    deriving (Eq,Ord,Typeable)
data FineSchedule = FineSchedule 
        { _fineScheduleInhStatus :: InhStatus Expr
        , _fineScheduleDeclSource :: DeclSource
        , _fineScheduleLineInfo :: LineInfo
        , _fineScheduleExprStore :: [(Expr,[String])] }
    deriving (Eq,Ord,Typeable)
data Guard = Guard 
        { _guardInhStatus :: InhStatus Expr
        , _guardDeclSource :: DeclSource
        , _guardLineInfo :: LineInfo
        , _guardExprStore :: [(Expr,[String])] }
    deriving (Eq,Ord,Typeable)
data Witness = Witness 
        { _witnessVar :: Var
        , _witnessEvtExpr :: Expr 
        , _witnessDeclSource :: DeclSource
        , _witnessLineInfo :: LineInfo
        , _witnessExprStore :: [(Expr,[String])] }
    deriving (Eq,Ord,Typeable)
data ActionDecl = Action 
        { _actionDeclInhStatus :: InhStatus Action
        , _actionDeclDeclSource :: DeclSource
        , _actionDeclLineInfo :: LineInfo
        , _actionDeclExprStore :: [(Expr,[String])] }
    deriving (Eq,Ord,Typeable)

class HasExprStore a b where
    exprStore :: Getter a b 

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

data EvtExprGroup = forall a. IsEvtExpr a => EvtExprGroup [(Maybe EventId,[(Label,a)])]

class ( Eq a, Ord a, Typeable a
      , Show a, Scope a
      , HasLineInfo a LineInfo
      , HasExprStore a [(Expr,[String])]
      , HasDeclSource a DeclSource ) => IsEvtExpr a where
    toMchScopeExpr :: Label -> a 
                   -> Reader MachineP2 [Either Error (MachineP3'Field b c)]
    toEvtScopeExpr :: EventId -> Label -> a 
                   -> Reader MachineP2 [Either Error [EventP3Field]]

instance IsEvtExpr EvtExprScope where
    toMchScopeExpr lbl (EvtExprScope x) = toMchScopeExpr lbl x
    toEvtScopeExpr e lbl (EvtExprScope x) = toEvtScopeExpr e lbl x

instance HasDeclSource EvtExprScope DeclSource where
    declSource f (EvtExprScope x) = EvtExprScope <$> declSource f x

instance HasLineInfo EvtExprScope LineInfo where
    lineInfo f (EvtExprScope x) = EvtExprScope <$> lineInfo f x

instance Show CoarseSchedule where
    show x = case x ^. inhStatus of
                InhDelete _ -> "deleted coarse schedule"
                InhAdd _ -> "coarse schedule"
instance Show FineSchedule where
    show x = case x ^. inhStatus of
                InhDelete _ -> "deleted fine schedule"
                InhAdd _ -> "fine schedule"
instance Show Witness where
    show (Witness _ _ _ _ _) = "witness"
instance Show Guard where
    show x = case x ^. inhStatus of
                InhDelete _ -> "deleted guard"
                InhAdd _ -> "guard"    
instance Show ActionDecl where
    show x = case x ^. inhStatus of
                InhDelete _ -> "delete action"
                InhAdd _ -> "action"

data EventExpr = EventExpr (Map (Maybe EventId) EvtExprScope)
    deriving (Eq,Ord,Typeable,Show)

instance HasExprStore EvtExprScope [(Expr,[String])] where
    exprStore f (EvtExprScope x) = coerce $ exprStore f x

instance HasExprStore EventExpr [(Expr,[String])] where
    exprStore = to $ \(EventExpr m) -> concatMap (view exprStore) $ M.elems m

data Invariant = Invariant 
        { _invariantMchExpr :: Expr
        , _invariantDeclSource :: DeclSource
        , _invariantLineInfo :: LineInfo
        , _invariantExprStore :: [(Expr,[String])] }
    deriving (Eq,Ord,Typeable)
data InvTheorem = InvTheorem 
        { _invTheoremMchExpr :: Expr
        , _invTheoremDeclSource :: DeclSource
        , _invTheoremLineInfo :: LineInfo
        , _invTheoremExprStore :: [(Expr,[String])] }
    deriving (Eq,Ord,Typeable)
data TransientProp = TransientProp
        { _transientPropMchExpr :: Transient
        , _transientPropDeclSource :: DeclSource
        , _transientPropLineInfo :: LineInfo
        , _transientPropExprStore :: [(Expr,[String])] }
    deriving (Eq,Ord,Typeable)
data ConstraintProp = ConstraintProp
        { _constraintPropMchExpr :: Constraint
        , _constraintPropDeclSource :: DeclSource
        , _constraintPropLineInfo :: LineInfo
        , _constraintPropExprStore :: [(Expr,[String])] }
    deriving (Eq,Ord,Typeable,Show)
data SafetyDecl = SafetyProp
        { _safetyDeclMchExpr :: SafetyProp
        , _safetyDeclDeclSource :: DeclSource
        , _safetyDeclLineInfo :: LineInfo
        , _safetyDeclExprStore :: [(Expr,[String])] }
    deriving (Eq,Ord,Typeable,Show)
data ProgressDecl = ProgressProp
        { _progressDeclMchExpr :: ProgressProp
        , _progressDeclDeclSource :: DeclSource
        , _progressDeclLineInfo :: LineInfo
        , _progressDeclExprStore :: [(Expr,[String])] }
    deriving (Eq,Ord,Typeable,Show)
data Initially = Initially
            { _initiallyInhStatus  :: InhStatus Expr
            , _initiallyDeclSource :: DeclSource
            , _initiallyLineInfo   :: LineInfo
            , _initiallyExprStore  :: [(Expr,[String])] }
    deriving (Eq,Ord,Typeable)
data Axiom = Axiom
        { _axiomMchExpr :: Expr
        , _axiomDeclSource :: DeclSource
        , _axiomLineInfo :: LineInfo
        , _axiomExprStore :: [(Expr,[String])] }
    deriving (Eq,Ord,Typeable,Show)

makeFields ''Axiom
makeFields ''ProgressDecl
makeFields ''Initially
makeFields ''SafetyDecl
makeFields ''ConstraintProp
makeFields ''TransientProp
makeFields ''Invariant
makeFields ''InvTheorem

instance Show Invariant where
    show _ = "invariant"

instance Show InvTheorem where
    show _ = "theorem"

instance Show TransientProp where
    show _ = "transient predicate"

instance Show Initially where
    show (Initially (InhAdd _) _ _ _) = "initialization"
    show (Initially (InhDelete _) _ _ _) = "deleted initialization"

class ( Scope a, Typeable a, Show a
      , HasExprStore a [(Expr,[String])] ) 
        => IsExprScope a where
    toMchExpr :: Label -> a -> Reader MachineP2 [Either Error (MachineP3'Field b c)]
    toThyExpr :: Label -> a -> Reader TheoryP2 [Either Error TheoryP3Field]
    toNewEvtExpr :: Label -> a -> Reader MachineP2 [Either Error (EventId, [EventP3Field])]
    toOldEvtExpr :: Label -> a -> Reader MachineP2 [Either Error (EventId, [EventP3Field])]
    toOldPropSet :: Label -> a -> Reader MachineP2 [Either Error PropertySetField]
    toNewPropSet :: Label -> a -> Reader MachineP2 [Either Error PropertySetField]

delegate :: (forall a. IsExprScope a => lbl -> a -> b) -> lbl -> ExprScope -> b
delegate f lbl (ExprScope x) = f lbl x

instance IsExprScope ExprScope where
    toMchExpr = delegate toMchExpr
    toThyExpr = delegate toThyExpr
    toNewPropSet = delegate toNewPropSet
    toOldPropSet = delegate toOldPropSet
    toNewEvtExpr = delegate toNewEvtExpr
    toOldEvtExpr = delegate toOldEvtExpr

data ExprScope = forall t. IsExprScope t => ExprScope t
    deriving Typeable

instance Eq ExprScope where
    ExprScope x == ExprScope y = h_equal x y

instance Ord ExprScope where
    compare (ExprScope x) (ExprScope y) = h_compare x y

instance HasExprStore ExprScope [(Expr,[String])] where
    exprStore f (ExprScope x) = coerce $ exprStore f x

data ExprGroup = forall a. IsExprScope a => ExprGroup [(Label,a)]

existential ''EvtExprGroup
existential ''ExprGroup
existential ''ExprScope
existential ''EvtExprScope


instance Scope CoarseSchedule where
    type Impl CoarseSchedule = WithDelete CoarseSchedule

instance Scope FineSchedule where
    type Impl FineSchedule = WithDelete FineSchedule

instance Scope Guard where
    type Impl Guard = WithDelete Guard

instance Scope Witness where

instance Scope ActionDecl where
    type Impl ActionDecl = WithDelete ActionDecl

instance Scope EvtExprScope where
    keep_from s x = applyEvtExprScope (keep_from s) x
    make_inherited e = applyEvtExprScope make_inherited e
    error_item e = readEvtExprScope error_item e
    clashes x y = fromMaybe True $ getConst <$> apply2EvtExprScope (fmap Const <$> clashes) x y
    merge_scopes x y = fromMaybe err $ runIdentity <$> apply2EvtExprScope (fmap Identity <$> merge_scopes) x y
        where
            err = error "EvtExprScope Scope.merge_scopes: _, _"
    rename_events m = applyEvtExprScope (rename_events m)

instance Scope ExprScope where
    keep_from s x = applyExprScope (keep_from s) x
    make_inherited e = applyExprScope make_inherited e
    error_item e = readExprScope (error_item) e
    clashes x y = fromMaybe True $ getConst <$> apply2ExprScope (fmap Const <$> clashes) x y
    merge_scopes x y = fromMaybe err $ runIdentity <$> apply2ExprScope (fmap Identity <$> merge_scopes) x y
        where
            err = error "ExprScope Scope.merge_scopes: _, _"
    rename_events m = applyExprScope (rename_events m)

instance Show ExprScope where
    show (ExprScope x) = show x
