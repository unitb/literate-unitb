{-# LANGUAGE TypeOperators, RecursiveDo, LambdaCase #-}
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

import           Control.Monad
import           Control.Monad.Reader.Class 
import           Control.Monad.Trans

import Control.Lens as L hiding ((|>),(<.>),(<|),indices,Context)

import           Data.List.NonEmpty as NE (NonEmpty(..),toList)
import           Data.Map   as M hiding ( map, foldl, (\\) )
import qualified Data.Map   as M
import qualified Data.Maybe as MM
import           Data.List as L hiding ( union, insert, inits )
import qualified Data.Traversable as T

import Test.QuickCheck

import Utilities.Existential
import Utilities.Format
import Utilities.Syntactic
  
run_phase2_vars :: Pipeline MM SystemP1 SystemP2
run_phase2_vars = C.id &&& symbols >>> liftP wrapup
    where
        err_msg = format "Multiple symbols with the name {0}"
        wrap = L.map (second $ makeCell . uncurry3 TheoryDef)
        symbols = arr (view mchTable) >>> run_phase
            [ variable_decl
            , constant_decl
            , dummy_decl
            , index_decl
            , arr $ Just . M.map (wrap . L.view pSetDecl)
            , param_decl
            , remove_var ]
        wrapup (SystemP r_ord p1,vs) = do
            let vs' = inherit2 p1 r_ord 
                        <$> unionsWith (++)
                        <$> vs
            vars <- triggerM
                =<< make_all_tables' err_msg 
                =<< triggerM vs'
                    
            let _  = vars :: MTable (Map String VarScope)
            SystemP r_ord <$> T.sequence (make_phase2 <$> p1 <.> vars)

newMch :: [(String,VarScope)] 
       -> MachineP1' EventP1 EventP1 TheoryP2
       -> MachineP2' EventP1 EventP1 TheoryP2 
       -> MM' c (MachineP2' EventP1 EventP1 TheoryP2)
newMch vars' m m' = makeMachineP2' m _pMchSynt <$> liftField toMchDecl vars'
    where
        _pMchSynt = (m^.pCtxSynt & primed_vars .~ refVars & decls %~ M.union refVars)
        refVars   = (m'^.pAbstractVars) `M.union` (m'^.pStateVars)

make_phase2 :: MachineP1
            -> Map String VarScope
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
                _pNotation = th_notation $ empty_theory { _extends = t'^.pImports }
                _pCtxSynt  = mkSetting _pNotation (p1 ^. pTypes) constants M.empty (t'^.pDummyVars)
                constants = (t'^.pConstants) `M.union` (M.mapMaybe defToVar $ t'^.pDefinitions)
        newEvent = liftEvent toNewEventDecl
        oldEvent = liftEvent toOldEventDecl
        liftEvent :: (String -> VarScope -> [Either Error (EventId, [EventP2Field])])
                  -> MM' c (MachineP2' EventP1 EventP1 TheoryP2
                            -> SkipOrEvent -> EventP1 -> EventP2 -> MM' c EventP2)
        liftEvent f = do
            table <- M.fromListWith (++) <$> liftField f vars'
            return $ \m eid -> do
                let _pSchSynt ::  EventP2 -> ParserSetting
                    _pSchSynt e = parser $ e^.eIndices

                    _pEvtSynt :: EventP2 -> ParserSetting
                    _pEvtSynt e = parser $ e^.eIndParams

                    parser :: Map String Var
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
                    [(String,VarScope)]
variable_decl = machine_var_decl Machine "\\variable"

instance IsVarScope TheoryConst where
    toOldEventDecl _ _ = []
    toNewEventDecl _ _ = []
    toThyDecl s th = [Right $ PConstants s $ thCons th]
    toMchDecl _ _  = []

constant_decl :: MPipeline MachineP1
                    [(String,VarScope)]
constant_decl = machine_var_decl TheoryConst "\\constant"

instance IsVarScope MachineVar where
    toOldEventDecl _ _ = []
    toNewEventDecl _ _ = []
    toThyDecl _ _ = []
    toMchDecl s (Machine v Local _)     = [Right $ PStateVars s v]
    toMchDecl s (Machine v Inherited _) = map Right [PAbstractVars s v,PStateVars s v]
    toMchDecl s (DelMch (Just v) Local li)     = map Right [PDelVars s (v,li),PAbstractVars s v]
    toMchDecl s (DelMch (Just v) Inherited li) = [Right $ PDelVars s (v,li)]
    toMchDecl s (DelMch Nothing _ li)    = [Left $ Error (format "deleted variable '{0}' does not exist" s) li]

remove_var :: MPipeline MachineP1 [(String,VarScope)]
remove_var = machineCmd "\\removevar" $ \(Identity xs) _m _p1 -> do
        li <- lift ask
        return $ map ((\x -> (x,makeCell $ DelMch Nothing Local li)) . getVarName) xs

dummy_decl :: MPipeline MachineP1
                    [(String,VarScope)]
dummy_decl = machine_var_decl 
        (\v source li -> Evt $ singleton Nothing (EventDecl v Param undefined source li)) 
        "\\dummy"

machine_var_decl :: IsVarScope var
                 => (Var -> DeclSource -> LineInfo -> var)
                 -> String
                 -> MPipeline MachineP1
                        [(String,VarScope)]
machine_var_decl scope kw = machineCmd kw $ \(Identity (PlainText xs)) _m p1 -> do
            vs <- get_variables' (p1 ^. pAllTypes) xs
            li <- lift ask
            return $ map (\(x,y) -> (x,makeCell $ scope y Local li)) vs

index_decl :: MPipeline MachineP1 [(String,VarScope)]
index_decl = event_var_decl Index "\\indices"

param_decl :: MPipeline MachineP1 [(String,VarScope)]
param_decl = event_var_decl Param "\\param"

type EventSym = (EventId,[(String,Var)])

toEventDecl :: RefScope -> String -> EvtDecls -> [Either a (EventId,[EventP2Field])]
toEventDecl ref s (Evt m) = map Right $ concatMap (uncurry f)
                                     $ MM.mapMaybe distr $ M.toList m
         where 
            distr (x,y) = (,y) <$> x
            f :: EventId -> EventDecl -> [(EventId, [EventP2Field])]
            f eid x = case (ref,x^.declSource) of
                        (Old,Inherited) -> [ (e,[g x]) | e <- NE.toList $ x^.source ]
                        (Old,Local) -> []
                        (New,_) -> [(eid,[g x])]

            g x = case x^.scope of 
                        Index -> EIndices s $ x^.varDecl
                        Param -> EParams s $ x^.varDecl

instance IsVarScope EvtDecls where
    toOldEventDecl = toEventDecl Old
    toNewEventDecl = toEventDecl New
    toMchDecl _ _  = []
    toThyDecl n (Evt m) = L.map (Right . PDummyVars n . view varDecl) $ M.elems 
                                $ M.filterWithKey (const.MM.isNothing) m

event_var_decl :: EvtScope
               -> String
               -> MPipeline MachineP1
                    [(String,VarScope)]
event_var_decl escope kw = machineCmd kw $ \(Conc lbl,PlainText xs) _m p1 -> do
            let _    = lbl :: EventId
                ts   = L.view pAllTypes p1
                evts = L.view pEventIds p1 
            evt <- bind
                (format "event '{0}' is undeclared" lbl)
                $ as_label lbl `M.lookup` evts
            li <- lift ask
            vs <- get_variables' ts xs
            return $ map (\(n,v) -> ((n,makeCell $ Evt $ M.singleton (Just evt) 
                    (EventDecl v escope (evt :| []) Local li)))) vs

return []

instance Arbitrary VarScope where
    arbitrary = VarScope <$> $(arbitraryCell' ''IsVarScope [[t| VarScope |]])
