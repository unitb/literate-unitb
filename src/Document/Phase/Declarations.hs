{-# LANGUAGE TypeOperators
        , RecursiveDo
        , LambdaCase
        , ConstraintKinds #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Document.Phase.Declarations where

    --
    -- Modules
    --
import Document.Pipeline
import Document.Phase as P
import Document.Phase.Parameters
import Document.Phase.Types
import Document.Scope
import Document.VarScope
import Document.Visitor

import Latex.Parser hiding (contents,source)

import Logic.Expr.Parser

import UnitB.Expr
import UnitB.Syntax as AST

    --
    -- Libraries
    --
import Control.Arrow hiding (left,app) -- (Arrow,arr,(>>>))
import Control.CoApplicative
import qualified Control.Category as C
import Control.Lens as L hiding ((|>),(<.>),(<|),indices,Context)

import           Control.Monad
import           Control.Monad.Fix
import           Control.Monad.Reader.Class 
import           Control.Monad.Trans
import           Control.Monad.Trans.Maybe

import Control.Precondition

import           Data.List.NonEmpty as NE (toList)
import           Data.Either
import           Data.Either.Validation
import           Data.Existential
import           Data.Map as M hiding ( map, (\\) )
import qualified Data.Map as M
import           Data.List as L hiding ( union, insert, inits )
import qualified Data.Traversable as T

import Test.QuickCheck hiding (Result(..),label)

import Text.Printf.TH as Printf

import Utilities.Syntactic
  
run_phase2_vars :: Pipeline MM SystemP1 SystemP2
run_phase2_vars = C.id &&& symbols >>> liftP wrapup
    where
        err_msg = [s|Multiple symbols with the name %s|] . render
        wrap = L.map (second $ makeCell . uncurry3 TheoryDef)
        symbols = arr (view mchMap) >>> run_phase
            [ variable_decl
            , definition
            , constant_decl
            , dummy_decl
            , index_decl
            , param_decl
            , arr $ Just . M.map (wrap . L.view pSetDecl)
            , promote_param
            , remove_ind
            , remove_var ]
        wrapup (SystemP r_ord p1,vs) = do
            let vs' = inherit2 p1 r_ord . unionsWith (++) <$> vs
            vars <- triggerM
                =<< make_all_tables' err_msg 
                =<< triggerM vs'
            let _  = vars :: MMap (Map Name VarScope)
            SystemP r_ord <$> T.sequence (make_phase2 <$> p1 <.> vars)

newMch :: [(Name,VarScope)] 
       -> MachineP1' EventP1 EventP1 TheoryP2
       -> MachineP2' EventP1 EventP1 TheoryP2 
       -> MM' c (MachineP2' EventP1 EventP1 TheoryP2)
newMch vars' m _ = parseDefs =<< mfix (newMch' vars' m)

newMch' :: [(Name,VarScope)] 
        -> MachineP1' EventP1 EventP1 TheoryP2
        -> MachineP2RawDef' EventP1 EventP1 TheoryP2 
        -> MM' c (MachineP2RawDef' EventP1 EventP1 TheoryP2)
newMch' vars' m m' = makeMachineP2'' m _pMchSynt <$> liftField toMchDecl vars'
    where
        _pMchSynt  = (m^.pCtxSynt & primed_vars .~ refVars & decls %~ M.union refVars)
        refVars   = M.unions [m'^.pAbstractVars, m'^.pStateVars]

parseDef :: MachineP2RawDef' ae ce thy
         -> StringLi -> MM' c Expr
parseDef m = liftEither . parse_expr (m^.pMchSynt & expected_type .~ Nothing)

parseDefs :: MachineP2RawDef' ae ce thy
          -> MM' c (MachineP2' ae ce thy )
parseDefs m = do
        m' <- m & pDefs (\defs -> triggerM =<< sequence 
                             <$> (defs & traverse (unfail . parseDef m)))
        let defs = M.mapWithKey (\n -> Var n.type_of.getExpr) $ m'^.pMchDef
        return $ m' & pMchSynt.decls %~ M.union defs

unfail :: MM' c a -> MM' c (Maybe a)
unfail (MM (MaybeT cmd)) = MM $ lift cmd

make_phase2 :: MachineP1
            -> Map Name VarScope
            -> MM' c MachineP2 
make_phase2 p1 vars = join $
        layeredUpgradeRecM newThy (newMch vars')
                    <$> oldEvent 
                    <*> newEvent 
                    <*> pure p1
    where
        vars' = M.toList vars
        newThy t t' = makeTheoryP2 t _pNotation _pCtxSynt <$> liftField toThyDecl vars'
            where
                _pNotation = th_notation' $ t'^.pImports
                _pCtxSynt  = mkSetting _pNotation (p1 ^. pTypes) constants M.empty (t'^.pDummyVars)
                constants = (t'^.pConstants) `M.union` (M.mapMaybe defToVar $ t'^.pDefinitions)
        newEvent = liftEvent toNewEventDecl
        oldEvent = liftEvent toOldEventDecl
        liftEvent :: (Name -> VarScope -> [Either Error (EventId, [EventP2Field])])
                  -> MM' c (MachineP2' EventP1 EventP1 TheoryP2
                            -> SkipOrEvent -> EventP1 -> EventP2 -> MM' c EventP2)
        liftEvent f = do
            table <- M.fromListWith (++) <$> liftField f vars'
            let _ = table :: Map EventId [EventP2Field] 
            return $ \m eid -> do
                let _pSchSynt ::  EventP2 -> ParserSetting
                    _pSchSynt e = parser $ e^.eIndices

                    _pEvtSynt :: EventP2 -> ParserSetting
                    _pEvtSynt e = parser $ e^.eIndParams

                    parser :: Map Name Var
                           -> ParserSetting
                    parser table    = m^.pMchSynt & decls %~ union table
                case eid of 
                    Right eid -> \e e' -> return $ makeEventP2 e (_pSchSynt e') (_pEvtSynt e') (findWithDefault [] eid table)  -- (m ! eid)
                    Left SkipEvent -> \e e' -> return $ makeEventP2 e (_pEvtSynt e') (_pSchSynt e') []

instance IsVarScope TheoryDef where
    toOldEventDecl _ _ = []
    toNewEventDecl _ _ = []
    toThyDecl s th = [Right $ PDefinitions s $ thDef th]
    toMchDecl _ _  = []

variable_decl :: MPipeline MachineP1
                    [(Name,VarScope)]
variable_decl = machine_var_decl MchVar "\\variable"

instance IsVarScope TheoryConst where
    toOldEventDecl _ _ = []
    toNewEventDecl _ _ = []
    toThyDecl s th = [Right $ PConstants s $ thCons th]
    toMchDecl _ _  = []

definition :: MPipeline MachineP1 
                  [(Name,VarScope)]
definition = machineCmd "\\definition" 
                $ \(VarName n,Expr xp) _m _p1 -> do
            li <- ask
            return [(n,makeCell $ MchDef n xp Local li)]

constant_decl :: MPipeline MachineP1
                    [(Name,VarScope)]
constant_decl = machine_var_decl TheoryConst "\\constant"

instance IsVarScope MachineVar where
    toOldEventDecl _ _ = []
    toNewEventDecl _ _ = []
    toThyDecl _ _ = []
    toMchDecl s (MchVar v Local _)     = [Right $ PStateVars s v]
    toMchDecl s (MchVar v Inherited _) = map Right [PAbstractVars s v,PStateVars s v]
    toMchDecl s (DelMchVar (Just v) Local li)     = map Right [PDelVars s (v,li),PAbstractVars s v]
    toMchDecl s (DelMchVar (Just v) Inherited li) = [Right $ PDelVars s (v,li)]
    toMchDecl s (DelMchVar Nothing _ li)    = [Left $ Error ([Printf.s|deleted variable '%s' does not exist|] $ render s) li]

instance IsVarScope MachineDef where
    toOldEventDecl _ _ = []
    toNewEventDecl _ _ = []
    toThyDecl _ _ = []
    toMchDecl _s (MchDef v term Local _) 
            = [Right $ PMchDef v term]
    toMchDecl _s (MchDef v term Inherited _) 
            = [Right $ PMchDef v term,Right $ PMchOldDef v term]

remove_ind :: MPipeline MachineP1 [(Name,VarScope)]
remove_ind = machineCmd "\\removeind" $ \(Conc evt,xs) _m _p1 -> do
        li <- ask
        _  <- get_concrete_event _p1 evt
        return [ (x,makeCell $ Evt $ M.singleton (Right evt) 
                $ EventDecl (Index $ InhDelete Nothing) (pure (Right evt)) Local li) 
            | IndName x <- xs ]

remove_var :: MPipeline MachineP1 [(Name,VarScope)]
remove_var = machineCmd "\\removevar" $ \(Identity xs) _m _p1 -> do
        li <- ask
        return $ map ((\x -> (x,makeCell $ DelMchVar Nothing Local li)) . getVarName) xs

dummy_decl :: MPipeline MachineP1 [(Name,VarScope)]
dummy_decl = machine_var_decl
        (\v source li -> Evt $ singleton (Left DummyDecl) (EventDecl (Param v) dummy source li)) 
        "\\dummy"
    where
        dummy = Left DummyDecl :| []

machine_var_decl :: IsVarScope var
                 => (Var -> DeclSource -> LineInfo -> var)
                 -> String
                 -> MPipeline MachineP1
                        [(Name,VarScope)]
machine_var_decl scope kw = machineCmd kw $ \(Identity (PlainText xs)) _m p1 -> do
            li <- ask
            vs <- hoistEither $ get_variables' (p1 ^. pAllTypes) xs li
            return $ map (\(x,y) -> (x,makeCell $ scope y Local li)) vs

promote_param :: MPipeline MachineP1 [(Name,VarScope)]
promote_param = machineCmd "\\promote" $ \(Conc lbl,VarName n) _m p1 -> do
            let _    = lbl :: EventId
                evts = L.view pEventIds p1 
            evt <- bind
                ([s|event '%s' is undeclared|] $ pretty lbl)
                $ as_label lbl `M.lookup` evts
            li <- ask
            return $ [(n,makeCell $ Evt $ M.singleton (Right evt) 
                        (EventDecl (Promoted Nothing) (Right evt :| []) Local li))]

index_decl :: MPipeline MachineP1 [(Name,VarScope)]
index_decl = event_var_decl (Index . InhAdd) "\\indices"

param_decl :: MPipeline MachineP1 [(Name,VarScope)]
param_decl = event_var_decl Param "\\param"

type EventSym = (EventId,[(Name,Var)])

toEventDecl :: RefScope 
            -> Name 
            -> EvtDecls 
            -> [Either Error (EventId,[EventP2Field])]
toEventDecl ref s (Evt m) = concatMap (concatMap fromValidation . uncurry f)
                                     $ rights $ view distrLeft <$> M.toList m
         where 
            fromValidation (Success x) = [Right x]
            fromValidation (Failure xs) = Left <$> xs
            f :: EventId -> EventDecl -> [Validation [Error] (EventId, [EventP2Field])]
            f eid x = case ref of
                        Old -> [ _2 id (e,g x) | e <- rights $ NE.toList $ x^.source ]
                        New -> [ _2 id (eid,g x)]
            g :: EventDecl -> Validation [Error] [EventP2Field]
            g x = case x^.scope of 
                        Index (InhAdd v) -> case (ref,x^.declSource) of
                            (Old,Local) -> Success []
                            _           -> Success [EIndices s v]
                        Param v -> case (ref,x^.declSource) of
                            (Old,Local) -> Success []
                            _           -> Success [EParams s v]
                        Promoted Nothing  -> case (ref,x^.declSource) of
                            (Old,Local) -> Success []
                            _           -> Failure [Error "Promoting a non-existing parameter" $ x^.lineInfo]
                        Index (InhDelete Nothing)  -> case (ref,x^.declSource) of
                            (Old,Local) -> Success []
                            _           -> Failure [Error "Deleting a non-existing index" $ x^.lineInfo]
                        Index (InhDelete (Just v)) -> 
                                            case (ref,x^.declSource) of
                                                (Old,Local)     -> Success [EIndices s v]
                                                (New,Local)     -> Success [EDelIndices s (v,x^.lineInfo)]
                                                (_,Inherited)   -> Success []
                        Promoted (Just v) -> case ref of
                                                Old -> case x^.declSource of 
                                                        Inherited -> Success [EIndices s v]
                                                        Local     -> Success [EParams s v]
                                                New -> Success [EIndices s v]

instance IsVarScope EvtDecls where
    toOldEventDecl = toEventDecl Old
    toNewEventDecl = toEventDecl New
    toMchDecl _ _  = []
    toThyDecl n (Evt m) = L.map (Right . PDummyVars n . fromJust' . view varDecl) $ M.elems 
                                $ M.filterWithKey (const.isLeft) m

event_var_decl :: (Var -> EvtScope Var)
               -> String
               -> MPipeline MachineP1
                    [(Name,VarScope)]
event_var_decl escope kw = machineCmd kw $ \(Conc lbl,PlainText xs) _m p1 -> do
            let _    = lbl :: EventId
                ts   = L.view pAllTypes p1
                evts = L.view pEventIds p1 
            evt <- bind
                ([s|event '%s' is undeclared|] $ pretty lbl)
                $ as_label lbl `M.lookup` evts
            li <- ask
            vs <- hoistEither $ get_variables' ts xs li
            return $ map (\(n,v) -> ((n,makeCell $ Evt $ M.singleton (Right evt) 
                    (EventDecl (escope v) (Right evt :| []) Local li)))) vs

return []

instance Arbitrary VarScope where
    arbitrary = VarScope <$> $(arbitraryCell' ''IsVarScope [[t| VarScope |]])
