{-# LANGUAGE TypeOperators, RecursiveDo, LambdaCase #-}
module Document.Phase.Declarations where

    --
    -- Modules
    --
import Document.Expression
import Document.Pipeline
import Document.Phase as P
import Document.Proof
import Document.Scope
import Document.VarScope
import Document.Visitor

import Latex.Parser hiding (contents,source)

import Logic.Expr

import UnitB.AST as AST

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
  
run_phase2_vars :: Pipeline MM 
                        SystemP1
                        SystemP2
run_phase2_vars = C.id &&& symbols >>> liftP wrapup
    where
        err_msg = format "Multiple symbols with the name {0}"
        wrap = L.map (second $ VarScope . uncurry3 TheoryDef)
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

make_phase2 :: MachineP1
            -> Map String VarScope
            -> MM' c MachineP2 
make_phase2 p1 vars = join $
        layeredUpgradeRecM newThy newMch 
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
        newMch m m' = makeMachineP2' m _pMchSynt <$> liftField toMchDecl vars'
            where
                _pMchSynt = (m^.pCtxSynt & primed_vars .~ refVars & decls %~ M.union refVars)
                refVars   = (m'^.pAbstractVars) `M.union` (m'^.pStateVars)
        newEvent = liftEvent toNewEventDecl
        oldEvent = liftEvent toOldEventDecl
        liftEvent :: (String -> VarScope -> [Either Error (EventId, [EventP2Field])])
                  -> MM' c (MachineP2' EventP1 TheoryP2
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
            where
                        -- mkSetting _pNotation (p2' ^. pTypes) (constants `union` table e) refVars (p2' ^. pDummyVars)
        -- tell err
        -- unless (L.null err) $ MaybeT $ return Nothing
        -- let 
        -- p2  <- p1 & pContext newThy
        -- p2' <- p2 & pEventRef (mapEvents (liftEvent toOldEventDecl) (liftEvent toNewEventDecl))
        -- let 
        --     _ = p2' :: MachineP1' EventP2 TheoryP2
        -- p2'' <- makeMachineP2' p2' _pMchSynt 
        --         <$> liftField toMchDecl (M.toList vars)
        --              -- & pEventRef %~ G.mapBothWithKey (liftEvent toOldEventDecl) 
        --              --                                 (liftEvent toNewEventDecl)
        -- let 
        --     ind_param :: EventId -> Map String Var
        --     ind_param eid = M.union (p2''^.getEvent eid.eIndices) (p2''^.getEvent eid.eParams)
            
        -- -- | L.null err = 
        -- return p2''  -- & (pNotation .~ _pNotation)
        --              -- & (pMchSynt .~ _pMchSynt)
        --              -- & (pCtxSynt .~ _pCtxSynt)
        --              -- & (pSchSynt .~ _pSchSynt)
        --              -- & (pEvtSynt .~ _pEvtSynt)
    -- where
        -- varGroup n (VarScope x) = VarGroup [(n,x)]
        -- vars' = groupVars $ L.map (uncurry varGroup) $ M.toList vars
        -- err = []
        -- (p2',err) = execRWS (mapM_ f vars') () p2
        --     where
        --         p2 =   pContext `over` makeTheoryP2
        --              $ pEvents `over` M.map makeEventP2
        --              $ makeMachineP2' p1

        -- f (VarGroup vs) = processDecl vs

        -- evts  = M.map (const ()) (p1 ^. pEvents)

        -- findE m e = findWithDefault M.empty e m :: Map String Var
        
        -- event_namespace :: Map EventId (Map String Var) -> EventId -> ParserSetting
        -- event_namespace table = 
        --     _ $ M.mapWithKey (const . parser table) evts 

instance IsVarScope TheoryDef where
    toOldEventDecl _ _ = []
    toNewEventDecl _ _ = []
    toThyDecl s th = [Right $ PDefinitions s $ thDef th]
    toMchDecl _ _  = []
    -- processDecl xs = do
    --     let xs' = M.fromList $ L.map (second thDef) xs
    --     pDefinitions %= M.union xs'

variable_decl :: MPipeline MachineP1
                    [(String,VarScope)]
variable_decl = machine_var_decl Machine "\\variable"

instance IsVarScope TheoryConst where
    toOldEventDecl _ _ = []
    toNewEventDecl _ _ = []
    toThyDecl s th = [Right $ PConstants s $ thCons th]
    toMchDecl _ _  = []
    -- processDecl xs = do
    --     let xs' = M.fromList $ L.map (second thCons) xs
    --     pConstants %= M.union xs'

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
    -- toMchDecl _ _ = Nothing
    -- processDecl xs = do
    --     let f :: (String,MachineVar) 
    --           -> Either Error ( [(String,(Var,LineInfo))]
    --                           , [(String,Var)]
    --                           , [(String,Var)])
    --         f (n,Machine v Local _) = Right ([],[],[(n,v)])
    --         f (n,Machine v Inherited _) = Right ([],[(n,v)],[(n,v)])
    --         f (n,DelMch (Just v) Local li) = Right ([(n,(v,li))],[(n,v)],[])
    --         f (n,DelMch (Just v) Inherited li) = Right ([(n,(v,li))],[],[])
    --         f (n,DelMch Nothing _ li) = Left $ Error (format "deleted variable '{0}' does not exist" n) li
    --         ys = map f xs
    --         (del,abst,st) = (_1 `over` M.fromList)
    --                         $ (both `over` M.fromList) 
    --                         $ mconcat $ rights ys
    --         zs = lefts ys
    --     tell zs
    --     pAbstractVars %= M.union abst
    --     pDelVars   %= M.union del
    --     pStateVars %= M.union st


remove_var :: MPipeline MachineP1 [(String,VarScope)]
remove_var = machineCmd "\\removevar" $ \(One xs) _m _p1 -> do
        li <- lift ask
        return $ map ((\x -> (x,VarScope $ DelMch Nothing Local li)) . toString) xs

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
machine_var_decl scope kw = machineCmd kw $ \(One xs) _m p1 -> do
            vs <- get_variables' (p1 ^. pAllTypes) xs
            li <- lift ask
            return $ map (\(x,y) -> (x,VarScope $ scope y Local li)) vs

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
    -- processDecl xs = do
    --     let f (n,Evt m) = mconcat $ M.elems $ M.mapWithKey (g n) m
    --         g :: String -> Maybe EventId 
    --           -> (Var,EvtScope,DeclSource,LineInfo)
    --           -> ([EventSym],[EventSym],[(String,Var)])
    --         g n (Just eid) (v,Index,_,_) = ([(eid,[(n,v)])],[],[])  
    --         g n (Just eid) (v,Param,_,_) = ([],[(eid,[(n,v)])],[])  
    --         g n Nothing (v,_,_,_) = ([],[],[(n,v)])
    --         (is,ps,ds) = 
    --                   _1 `over` (M.map M.fromList . M.fromListWith (++)) 
    --                 $ _2 `over` (M.map M.fromList . M.fromListWith (++)) 
    --                 $ _3 `over` M.fromList
    --                 $ mconcat $ map f xs
    --     pIndices %= M.unionWith M.union is
    --     pParams  %= M.unionWith M.union ps
    --     pDummyVars %= M.union ds

event_var_decl :: EvtScope
               -> String
               -> MPipeline MachineP1
                    [(String,VarScope)]
event_var_decl escope kw = machineCmd kw $ \(lbl,xs) _m p1 -> do
            let ts   = L.view pTypes p1
                evts = L.view pEventIds p1 
            evt <- bind
                (format "event '{0}' is undeclared" lbl)
                $ lbl `M.lookup` evts
            li <- lift ask
            vs <- get_variables' ts xs
            return $ map (\(n,v) -> ((n,VarScope $ Evt $ M.singleton (Just evt) 
                    (EventDecl v escope (evt :| []) Local li)))) vs

return []

instance Arbitrary VarScope where
    arbitrary = $(arbitraryInstanceOf' 'VarScope ''IsVarScope [[t| VarScope |]])
