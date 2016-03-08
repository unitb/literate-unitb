{-# LANGUAGE TypeOperators
        , RecursiveDo
        , LambdaCase
        , ConstraintKinds #-}
module Document.Phase.Declarations where

    --
    -- Modules
    --
import Document.Expression
import Document.Pipeline
import Document.Phase as P
import Document.Phase.Parameters
import Document.Phase.Types
import Document.Proof
import Document.Scope
import Document.VarScope
import Document.Visitor

import Latex.Parser hiding (contents,source)

import Logic.Expr

import UnitB.Syntax as AST

    --
    -- Libraries
    --
import Control.Arrow hiding (left,app) -- (Arrow,arr,(>>>))
import qualified Control.Category as C
import Control.Lens as L hiding ((|>),(<.>),(<|),indices,Context)

import           Control.Monad
import           Control.Monad.Reader.Class 

import Control.Precondition

import           Data.List.NonEmpty as NE (toList)
import           Data.Either.Validation
import           Data.Existential
import Data.Map.Class as M hiding ( map, (\\) )
import qualified Data.Map.Class as M
import qualified Data.Maybe as MM
import           Data.List as L hiding ( union, insert, inits )
import qualified Data.Traversable as T

import Test.QuickCheck hiding (Result(..),label)

import Text.Printf.TH

import Utilities.Syntactic
import Utilities.Table
  
run_phase2_vars :: Pipeline MM SystemP1 SystemP2
run_phase2_vars = C.id &&& symbols >>> liftP wrapup
    where
        err_msg = [printf|Multiple symbols with the name %s|] . render
        wrap = L.map (second $ makeCell . uncurry3 TheoryDef)
        symbols = arr (view mchTable) >>> run_phase
            [ variable_decl
            , constant_decl
            , dummy_decl
            , index_decl
            , param_decl
            , promote_param
            , arr $ Just . M.map (wrap . L.view pSetDecl)
            , remove_var ]
        wrapup (SystemP r_ord p1,vs) = do
            let vs' = inherit2 p1 r_ord 
                        <$> unionsWith (++)
                        <$> vs
            vars <- triggerM
                =<< make_all_tables' err_msg 
                =<< triggerM vs'
            let _  = vars :: MTable (Table Name VarScope)
            SystemP r_ord <$> T.sequence (make_phase2 <$> p1 <.> vars)

newMch :: [(Name,VarScope)] 
       -> MachineP1' EventP1 EventP1 TheoryP2
       -> MachineP2' EventP1 EventP1 TheoryP2 
       -> MM' c (MachineP2' EventP1 EventP1 TheoryP2)
newMch vars' m m' = makeMachineP2' m _pMchSynt <$> liftField toMchDecl vars'
    where
        _pMchSynt = (m^.pCtxSynt & primed_vars .~ refVars & decls %~ M.union refVars)
        refVars   = (m'^.pAbstractVars) `M.union` (m'^.pStateVars)

make_phase2 :: MachineP1
            -> Table Name VarScope
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
            let _ = table :: Table EventId [EventP2Field] 
            return $ \m eid -> do
                let _pSchSynt ::  EventP2 -> ParserSetting
                    _pSchSynt e = parser $ e^.eIndices

                    _pEvtSynt :: EventP2 -> ParserSetting
                    _pEvtSynt e = parser $ e^.eIndParams

                    parser :: Table Name Var
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

instance PrettyRecord TheoryDef where
    recordFields = genericRecordFields []
instance PrettyPrintable TheoryDef where
    pretty = prettyRecord

variable_decl :: MPipeline MachineP1
                    [(Name,VarScope)]
variable_decl = machine_var_decl Machine "\\variable"

instance IsVarScope TheoryConst where
    toOldEventDecl _ _ = []
    toNewEventDecl _ _ = []
    toThyDecl s th = [Right $ PConstants s $ thCons th]
    toMchDecl _ _  = []

instance PrettyRecord TheoryConst where
    recordFields = genericRecordFields []
instance PrettyPrintable TheoryConst where
    pretty = prettyRecord

constant_decl :: MPipeline MachineP1
                    [(Name,VarScope)]
constant_decl = machine_var_decl TheoryConst "\\constant"

instance IsVarScope MachineVar where
    toOldEventDecl _ _ = []
    toNewEventDecl _ _ = []
    toThyDecl _ _ = []
    toMchDecl s (Machine v Local _)     = [Right $ PStateVars s v]
    toMchDecl s (Machine v Inherited _) = map Right [PAbstractVars s v,PStateVars s v]
    toMchDecl s (DelMch (Just v) Local li)     = map Right [PDelVars s (v,li),PAbstractVars s v]
    toMchDecl s (DelMch (Just v) Inherited li) = [Right $ PDelVars s (v,li)]
    toMchDecl s (DelMch Nothing _ li)    = [Left $ Error ([printf|deleted variable '%s' does not exist|] $ render s) li]

instance PrettyRecord MachineVar where
    recordFields = genericRecordFields []
instance PrettyPrintable MachineVar where
    pretty = prettyRecord

remove_var :: MPipeline MachineP1 [(Name,VarScope)]
remove_var = machineCmd "\\removevar" $ \(Identity xs) _m _p1 -> do
        li <- ask
        return $ map ((\x -> (x,makeCell $ DelMch Nothing Local li)) . getVarName) xs

dummy_decl :: MPipeline MachineP1
                    [(Name,VarScope)]
dummy_decl = machine_var_decl 
        (\v source li -> Evt $ singleton Nothing (EventDecl (Param v) dummy source li)) 
        "\\dummy"
    where
        dummy = EventId (label "dummy") :| []

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
                ([printf|event '%s' is undeclared|] $ show lbl)
                $ as_label lbl `M.lookup` evts
            li <- ask
            return $ [(n,makeCell $ Evt $ M.singleton (Just evt) 
                        (EventDecl (Promoted Nothing) (evt :| []) Local li))]

index_decl :: MPipeline MachineP1 [(Name,VarScope)]
index_decl = event_var_decl Index "\\indices"

param_decl :: MPipeline MachineP1 [(Name,VarScope)]
param_decl = event_var_decl Param "\\param"

type EventSym = (EventId,[(Name,Var)])

toEventDecl :: RefScope -> Name -> EvtDecls -> [Either Error (EventId,[EventP2Field])]
toEventDecl ref s (Evt m) = concatMap (concatMap fromValidation . uncurry f)
                                     $ MM.mapMaybe distr $ M.toList m
         where 
            fromValidation (Success x) = [Right x]
            fromValidation (Failure xs) = Left <$> xs
            distr (x,y) = (,y) <$> x
            f :: EventId -> EventDecl -> [Validation [Error] (EventId, [EventP2Field])]
            f eid x = case (ref,x^.declSource) of
                        (Old,Inherited) -> [ (_2.traverse) id (e,[g x]) | e <- NE.toList $ x^.source ]
                        (Old,Local) -> []
                        (New,_) -> [ (_2.traverse) id (eid,[g x])]
            g :: EventDecl -> Validation [Error] EventP2Field
            g x = case x^.scope of 
                        Index v  -> Success $ EIndices s v
                        Param v  -> Success $ EParams s v
                        Promoted Nothing -> Failure [Error "Promoting a non-existing parameter" $ x^.lineInfo]
                        Promoted (Just v) -> case ref of
                                                Old -> Success $ EParams s v
                                                New -> Success $ EIndices s v

instance IsVarScope EvtDecls where
    toOldEventDecl = toEventDecl Old
    toNewEventDecl = toEventDecl New
    toMchDecl _ _  = []
    toThyDecl n (Evt m) = L.map (Right . PDummyVars n . fromJust' . view varDecl) $ M.ascElems 
                                $ M.filterWithKey (const.MM.isNothing) m

instance PrettyRecord EvtDecls where
    recordFields = genericRecordFields []
instance PrettyPrintable EvtDecls where
    pretty = prettyRecord

instance PrettyRecord EventDecl where
    recordFields = genericRecordFields []
instance PrettyPrintable EventDecl where
    pretty = prettyRecord

event_var_decl :: (Var -> EvtScope Var)
               -> String
               -> MPipeline MachineP1
                    [(Name,VarScope)]
event_var_decl escope kw = machineCmd kw $ \(Conc lbl,PlainText xs) _m p1 -> do
            let _    = lbl :: EventId
                ts   = L.view pAllTypes p1
                evts = L.view pEventIds p1 
            evt <- bind
                ([printf|event '%s' is undeclared|] $ show lbl)
                $ as_label lbl `M.lookup` evts
            li <- ask
            vs <- hoistEither $ get_variables' ts xs li
            return $ map (\(n,v) -> ((n,makeCell $ Evt $ M.singleton (Just evt) 
                    (EventDecl (escope v) (evt :| []) Local li)))) vs

return []

instance Arbitrary VarScope where
    arbitrary = VarScope <$> $(arbitraryCell' ''IsVarScope [[t| VarScope |]])
