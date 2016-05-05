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
import Control.Arrow
import Control.Lens as L hiding ((|>),(<.>),(<|),indices,Context)
import Control.Monad.Reader
import Control.Precondition

import Data.Either
import Data.Existential
import Data.Hashable
import Data.List as L
import Data.List.NonEmpty as NE (toList,fromList)
import Data.Map.Class as M
import Data.Semigroup
import Data.Typeable

import GHC.Generics.Instances

import Text.Printf.TH

import Test.QuickCheck
import Test.QuickCheck.Regression

import Utilities.String
import Utilities.Syntactic
import Utilities.Table

data CoarseSchedule = CoarseSchedule 
        { _coarseScheduleInhStatus :: EventInhStatus Expr
        , _coarseScheduleDeclSource :: DeclSource
        , _coarseScheduleLineInfo :: NonEmpty LineInfo
        } deriving (Eq,Ord,Typeable,Show,Generic)
data FineSchedule = FineSchedule 
        { _fineScheduleInhStatus :: EventInhStatus Expr
        , _fineScheduleDeclSource :: DeclSource
        , _fineScheduleLineInfo :: NonEmpty LineInfo
        } deriving (Eq,Ord,Typeable,Show,Generic)
data Guard = Guard 
        { _guardInhStatus :: EventInhStatus Expr
        , _guardDeclSource :: DeclSource
        , _guardLineInfo :: NonEmpty LineInfo
        } deriving (Eq,Ord,Typeable,Show,Generic)
data Witness = Witness 
        { _witnessVar :: Var
        , _witnessEvtExpr :: Expr 
        , _witnessDeclSource :: DeclSource
        , _witnessLineInfo :: NonEmpty LineInfo
        } deriving (Eq,Ord,Typeable,Show,Generic)
data IndexWitness = IndexWitness 
        { _indexWitnessVar :: Var
        , _indexWitnessEvtExpr :: Expr 
        , _indexWitnessDeclSource :: DeclSource
        , _indexWitnessLineInfo :: NonEmpty LineInfo
        } deriving (Eq,Ord,Typeable,Show,Generic)
data ActionDecl = Action 
        { _actionDeclInhStatus :: EventInhStatus Action
        , _actionDeclDeclSource :: DeclSource
        , _actionDeclLineInfo :: NonEmpty LineInfo
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
    (==) = cellEqual' (==)

instance Ord EvtExprScope where
    compare = cellCompare' compare

instance Show EvtExprScope where
    show = readCell' show

instance PrettyPrintable EvtExprScope where
    pretty = readCell' pretty



class ( Eq a, Ord a, Typeable a
      , Show a, Scope a
      , PrettyPrintable a
      , HasLineInfo a (NonEmpty LineInfo)
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

instance HasLineInfo EvtExprScope (NonEmpty LineInfo) where
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
    compare = cellCompare' compare

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

instance Arbitrary EventExpr where
    arbitrary = EventExpr . M.fromList <$> listOf1 arbitrary

instance Scope Initially where
    type Impl Initially = WithDelete Initially
    kind x = case x^.inhStatus of 
            InhAdd _ -> "initialization"
            InhDelete _ -> "deleted initialization"
    rename_events' _ x = [x]

instance IsExprScope Initially where
    toNewEvtExprDefault _ _ = return []
    toMchExpr lbl i  = do
        vs <- view pDelVars
        return $ case (i^.inhStatus,i^.declSource) of
            (InhAdd x,_)
                | L.null lis' -> [Right $ PInit lbl x]
                | otherwise   -> [Left $ MLError msg $ ([printf|predicate %s|] $ show lbl,li):lis']
                where
                    lis = L.map (_1 %~ view name) $ M.ascElems $ vs `M.intersection` used_var' x
                    lis' = L.map (_1 %~ ([printf|deleted variable %s|] . render)) lis
                    msg  = [printf|initialization predicate '%s' refers to deleted variables|] $ show lbl
            (InhDelete (Just x),Local) -> [Right $ PDelInits lbl x]
            (InhDelete (Just _),Inherited) -> []
            (InhDelete Nothing,_) -> [Left $ Error msg li]
                where
                    msg = [printf|initialization predicate '%s' was deleted but does not exist|] $ show lbl
        where
            li = i^.lineInfo
    toThyExpr _ _  = return []
    toNewPropSet _ _ = return []
    toOldPropSet _ _ = return []
    toNewEvtExpr _ _ = return []
    toOldEvtExpr _ _ = return []

instance Scope EventExpr where
    kind (EventExpr m) = showWith kind m
    keep_from s (EventExpr m) = Just $ EventExpr $ M.mapMaybe (keep_from s) m
    make_inherited (EventExpr m) = Just $ EventExpr (M.map f m)
        where
            f x = set declSource Inherited x
    error_item (EventExpr m) = sconcat $ NE.fromList $ L.map sequence $ ascElems $ mapWithKey msg m
        where
            msg (Right k) sc 
                | inheritedFrom sc `elem` [[],[k]]
                    = ([printf|%s (event '%s')|] (kind sc) (show k) :: String, view lineInfo sc)
                | otherwise
                    = ([printf|%s (event '%s', from '%s')|] (kind sc) (show k) parents :: String, view lineInfo sc)
                where
                    parents = intercalate "," $ L.map show $ inheritedFrom sc
            msg (Left _) sc = ([printf|%s (initialization)|] (kind sc) :: String, view lineInfo sc)
    merge_scopes' (EventExpr m0) (EventExpr m1) = EventExpr <$> scopeUnion merge_scopes' m0 m1
    rename_events' lookup (EventExpr es) = L.map EventExpr $ concatMap f $ M.toList es
        where
            f (Right eid,x) = [ singleton (Right e) $ setSource eid x | e <- lookup eid ]
            f (Left InitEvent,x) = [singleton (Left InitEvent) x]

instance PrettyPrintable Initially where
    pretty = kind

instance IsEvtExpr CoarseSchedule where
    toMchScopeExpr _ _  = return []
    defaultEvtWitness _ _ = return []
    toEvtScopeExpr = parseEvtExpr "coarse schedule" ECoarseSched

instance PrettyPrintable CoarseSchedule where
    pretty = kind

instance IsEvtExpr FineSchedule where
    toMchScopeExpr _ _  = return []
    defaultEvtWitness _ _ = return []
    toEvtScopeExpr = parseEvtExpr "fine schedule" EFineSched

instance PrettyPrintable FineSchedule where
    pretty = kind

instance IsEvtExpr Guard where
    toMchScopeExpr _ _  = return []
    defaultEvtWitness _ _ = return []
    toEvtScopeExpr = parseEvtExpr "guard" EGuards

instance PrettyPrintable Guard where
    pretty = kind

parseEvtExpr :: ( HasInhStatus decl (EventInhStatus Expr)
                , HasLineInfo decl (NonEmpty LineInfo)
                , HasDeclSource decl DeclSource)
             => String 
             -> (Label -> Expr -> field)
             -> RefScope
             -> EventId -> Label -> decl
             -> Reader MachineP2 [Either Error (EventId,[field])]
parseEvtExpr expKind = parseEvtExpr' expKind used_var'


parseEvtExpr' :: ( HasInhStatus decl (EventInhStatus expr)
                 , HasLineInfo decl (NonEmpty LineInfo)
                 , HasDeclSource decl DeclSource)
              => String 
              -> (expr -> Table Name Var)
              -> (Label -> expr -> field)
              -> RefScope
              -> EventId -> Label -> decl
              -> Reader MachineP2 [Either Error (EventId,[field])]
parseEvtExpr' expKind fvars field scope evt lbl decl = 
    (++) <$> check
         <*>
        -- (old_xs, del_xs, new_xs)
        case (decl^.inhStatus, decl^.declSource) of
            (InhAdd e, Inherited) -> return $ old e ++ new e 
            (InhAdd e, Local)     -> return $ new e
            (InhDelete _, Inherited) -> return [] 
            (InhDelete (Just e), Local) -> return $ old e
            (InhDelete Nothing, Local)  -> return [] 
    where
        check = case scope of
                    Old -> return []
                    New -> checkLocalExpr' expKind (fvars.snd) evt lbl decl
        old = case scope of
            Old -> \(evts,e) -> [Right (ev,[field lbl e]) | ev <- NE.toList evts]
            New -> const []
        new = case scope of
            Old -> const []
            New -> \(_,e) -> [Right (evt,[field lbl e])]

checkLocalExpr' :: ( HasInhStatus decl (InhStatus expr)
                  , HasLineInfo decl (NonEmpty LineInfo) )
               => String -> (expr -> Table Name Var)
               -> EventId -> Label -> decl
               -> Reader MachineP2 [Either Error a]
checkLocalExpr' expKind free eid lbl sch = do
            vs <- view pDelVars 
            return $ case sch^.inhStatus of
                InhAdd expr -> 
                    let msg = [printf|event '%s', %s '%s' refers to deleted variables|] (show eid) expKind (show lbl)
                        errs   = vs `M.intersection` free expr
                        schLI  = ([printf|%s '%s'|] expKind $ show lbl,) <$> sch^.lineInfo
                        varsLI = L.map (_1 %~ [printf|deleted variable '%s'|] . render . view name) (M.ascElems errs)
                    in if M.null errs then []
                       else [Left $ MLError msg $ NE.toList schLI ++ varsLI]
                InhDelete Nothing -> 
                    let msg = [printf|event '%s', %s '%s' was deleted but does not exist|] (show eid) expKind (show lbl)
                        li  = isOne $ ([printf|%s '%s'|] expKind $ show lbl,) <$> sch^.lineInfo
                    in [Left $ either (MLError msg) (Error msg.snd) li]
                _ -> []
    where
        isOne (x:|[]) = Right x
        isOne (x:|xs) = Left (x:xs)

instance Scope Axiom where
    kind _ = "axiom"
    merge_scopes' _ _ = Nothing -- error "Axiom Scope.merge_scopes: _, _"
    keep_from s x = guard (s == view declSource x) >> return x
    rename_events' _ x = [x]

instance IsExprScope Axiom where
    toNewEvtExprDefault _ _ = return []
    toMchExpr _ _    = return []
    toThyExpr lbl x  = return [Right $ PAssumptions lbl $ x^.mchExpr]
    toNewPropSet _ _ = return []
    toOldPropSet _ _ = return []
    toNewEvtExpr _ _ = return []
    toOldEvtExpr _ _ = return []

instance PrettyPrintable Axiom where
    pretty = kind

instance PrettyPrintable Invariant where
    pretty = kind

instance Scope Invariant where
    kind _ = "invariant"
    rename_events' _ x = [x]

instance IsExprScope Invariant where
    toNewEvtExprDefault _ _ = return []
    toMchExpr lbl e = return [Right $ PInvariant lbl $ e^.mchExpr]
    toThyExpr _ _   = return []
    toNewPropSet lbl x = return $ if x^.declSource == Local 
            then [Right $ Inv lbl $ x^.mchExpr] 
            else []
    toOldPropSet lbl x = return $ if x^.declSource == Inherited 
            then [Right $ Inv lbl $ x^.mchExpr] 
            else []
    toNewEvtExpr _ _ = return []
    toOldEvtExpr _ _ = return []

instance Scope InvTheorem where
    kind _ = "theorem"
    rename_events' _ x = [x]

instance IsExprScope InvTheorem where
    toNewEvtExprDefault _ _ = return []
    toMchExpr lbl e = return [Right $ PInvariant lbl $ e^.mchExpr]
    toThyExpr _ _   = return []
    toNewPropSet lbl x = return $ if x^.declSource == Local 
            then [Right $ Inv_thm lbl $ x^.mchExpr] 
            else []
    toOldPropSet lbl x = return $ if x^.declSource == Inherited 
            then [Right $ Inv_thm lbl $ x^.mchExpr] 
            else []
    toNewEvtExpr _ _ = return []
    toOldEvtExpr _ _ = return []

instance PrettyPrintable InvTheorem where
    pretty = kind

instance Scope TransientProp where
    kind _ = "transient predicate"
    rename_events' _ x = [x]
instance IsExprScope TransientProp where
    toNewEvtExprDefault _ _ = return []
    toMchExpr lbl e = return [Right $ PTransient lbl $ e^.mchExpr]
    toThyExpr _ _   = return []
    toNewPropSet lbl x = return $ if x^.declSource == Local 
            then [Right $ Transient lbl $ x^.mchExpr] 
            else []
    toOldPropSet lbl x = return $ if x^.declSource == Inherited 
            then [Right $ Transient lbl $ x^.mchExpr] 
            else []
    toNewEvtExpr _ _ = return []
    toOldEvtExpr _ _ = return []

instance PrettyPrintable TransientProp where
    pretty = kind

instance IsExprScope ConstraintProp where
    toNewEvtExprDefault _ _ = return []
    toMchExpr _ _ = return []
    toThyExpr _ _ = return []
    toNewPropSet lbl x = return $ if x^.declSource == Local 
            then [Right $ Constraint lbl $ x^.mchExpr] 
            else []
    toOldPropSet lbl x = return $ if x^.declSource == Inherited 
            then [Right $ Constraint lbl $ x^.mchExpr] 
            else []
    toNewEvtExpr _ _ = return []
    toOldEvtExpr _ _ = return []

instance Scope ConstraintProp where
    kind _ = "co property"
    rename_events' _ x = [x]

instance PrettyPrintable ConstraintProp where
    pretty = kind

instance IsExprScope SafetyDecl where
    toNewEvtExprDefault _ _ = return []
    toMchExpr lbl e = return [Right $ PSafety lbl $ e^.mchExpr]
    toThyExpr _ _    = return []
    toNewPropSet lbl x = return $ if x^.declSource == Local 
            then [Right $ Safety lbl $ x^.mchExpr] 
            else []
    toOldPropSet lbl x = return $ if x^.declSource == Inherited 
            then [Right $ Safety lbl $ x^.mchExpr] 
            else []
    toNewEvtExpr _ _ = return []
    toOldEvtExpr _ _ = return []

instance Scope SafetyDecl where
    kind _ = "safety property"
    rename_events' _ x = [x]

instance PrettyPrintable SafetyDecl where
    pretty = kind

instance IsExprScope ProgressDecl where
    toNewEvtExprDefault _ _ = return []
    toMchExpr lbl e = return [Right $ PProgress (PId lbl) $ e^.mchExpr]
    toThyExpr _ _   = return []
    toNewPropSet lbl x = return $ if x^.declSource == Local 
            then [Right $ Progress (PId lbl) $ x^.mchExpr] 
            else []
    toOldPropSet lbl x = return $ if x^.declSource == Inherited 
            then [Right $ Progress (PId lbl) $ x^.mchExpr] 
            else []
    toNewEvtExpr _ _ = return []
    toOldEvtExpr _ _ = return []

instance Scope ProgressDecl where
    kind _ = "progress property"
    rename_events' _ x = [x]

instance PrettyPrintable ProgressDecl where
    pretty = kind


instance IsEvtExpr IndexWitness where
    defaultEvtWitness _ _ = return []
    toMchScopeExpr _ _ = return []
    toEvtScopeExpr Old evt _ w
        | w^.declSource == Local = return [Right (evt,[EIndWitness (v^.name) (v, getExpr $ w^.evtExpr)])]
        | otherwise              = return []
        where v = w^.var
    toEvtScopeExpr New _ _ _ = return []
    setSource _ x = x
    inheritedFrom _ = []

instance PrettyPrintable IndexWitness where
    pretty = kind

instance IsEvtExpr Witness where
    defaultEvtWitness _ _ = return []
    toMchScopeExpr _ w   
        | w^.declSource == Local = return [Right $ PInitWitness (v^.name) (v, w^.evtExpr)]
        | otherwise              = return []
        where v = w^.var
    toEvtScopeExpr Old _ _ _ = return []
    toEvtScopeExpr New evt _ w
        | w^.declSource == Local = return [Right (evt,[EWitness (v^.name) (v, getExpr $ w^.evtExpr)])]
        | otherwise              = return []
        where v = w^.var
    setSource _ x = x
    inheritedFrom _ = []

instance PrettyPrintable Witness where
    pretty = kind

instance IsEvtExpr ActionDecl where
    defaultEvtWitness ev scope = case (scope^.inhStatus, scope^.declSource) of 
        (InhDelete (Just (_,act)),Local) -> do
            vs <- view pDelVars
            return [Right $ (ev,[EWitness (v^.name) (v, ba_pred act) 
                                         | v <- M.ascElems $ frame' act `M.intersection` vs ])]
        _ -> return []
    toMchScopeExpr _ _  = return []
    toEvtScopeExpr scope eid lbl decl = do
            x <- parseEvtExpr' "action"
                (uncurry M.union . (frame' &&& used_var'.ba_pred))
                EActions scope eid lbl decl
            return x

instance PrettyPrintable ActionDecl where
    pretty = kind

instance IsExprScope EventExpr where
    toNewEvtExprDefault _ (EventExpr m) = 
          fmap (concat.M.ascElems) 
        $ M.traverseWithKey defaultEvtWitness 
        $ M.mapKeysMonotonic fromRight' 
        $ M.filterWithKey (const.isRight) m
    toMchExpr lbl (EventExpr m) = 
            fmap concat $ mapM (toMchScopeExpr lbl) $ M.ascElems 
                $ M.filterWithKey (const.isLeft) m
    toThyExpr _ _  = return []
    toNewPropSet _ _ = return []
    toOldPropSet _ _ = return []
    toNewEvtExpr lbl (EventExpr m) =
            fmap concat $ mapM g $ rights $ L.map f $ M.toList m
        where f (x,y) = (,y) <$> x
              g (x,y) = toEvtScopeExpr New x lbl y
    toOldEvtExpr lbl (EventExpr m) = do
            concat <$> mapM fields (rights $ L.map f $ M.toList m)
        where f (x,y) = (,y) <$> x
              fields :: (EventId, EvtExprScope)
                     -> Reader MachineP2 [Either Error (EventId, [EventP3Field])]
              fields (x,y) = toEvtScopeExpr Old x lbl y

instance PrettyPrintable EventExpr where
    pretty = show . M.map Pretty . view eventExprs

prop_axiom_Scope_mergeCommutative :: Property
prop_axiom_Scope_mergeCommutative = regression (uncurry axiom_Scope_mergeCommutative) [(g0,g1)]
    where
        g0 = Guard {_guardInhStatus = InhAdd ("i" :| [],zfalse), _guardDeclSource = Inherited, _guardLineInfo = pure (LI "file" 0 0)}
        g1 = Guard {_guardInhStatus = InhAdd ("e" :| [],zfalse), _guardDeclSource = Local, _guardLineInfo = pure (LI "file" 0 0)}

return []

run_tests :: IO Bool
run_tests = $quickCheckAll

instance Arbitrary EvtExprScope where
    arbitrary = do
        s <- $(arbitraryCell' ''IsEvtExpr [ [t| EvtExprScope |] ])
        return $ EvtExprScope s

instance Arbitrary ExprScope where
    arbitrary = ExprScope <$> $(arbitraryCell' ''IsExprScope [ [t| ExprScope |] ])
