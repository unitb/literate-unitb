{-# LANGUAGE TypeOperators
    , Arrows
    , OverloadedStrings
    , RecordWildCards #-}
module Document.Phase.Proofs where

    --
    -- Modules
    --
import Document.Pipeline
import Document.Phase as P
import Document.Phase.Parameters
import Document.Phase.Transient
import Document.Phase.Types
import Document.Proof
import Document.Refinement as Ref
import Document.Scope
import Document.Visitor

import Latex.Parser hiding (contents)

import Logic.Proof
import Logic.Proof.Tactics hiding ( with_line_info )

import UnitB.Expr
import UnitB.Syntax as AST

    --
    -- Libraries
    --
import Control.Arrow hiding (left,app) -- (Arrow,arr,(>>>))
import Control.DeepSeq

import           Control.Monad 
import           Control.Monad.Reader.Class 
import           Control.Monad.Writer.Class 
import           Control.Monad.Trans
import           Control.Monad.Trans.Either
import           Control.Monad.Trans.Reader ( runReaderT )
import           Control.Monad.Trans.RWS as RWS ( mapRWST )

import Control.Lens as L hiding ((|>),(<.>),(<|),indices,Context)

import           Data.Char
import           Data.Either.Combinators
import qualified Data.Maybe as MM
import           Data.List as L hiding ( union, insert, inits )
import qualified Data.Set as S
import qualified Data.Traversable as T
import           Data.Witherable  as W

import GHC.Generics (Generic)

import qualified Utilities.BipartiteGraph as G
import Utilities.Format
import           Utilities.Map   as M hiding ( map, (\\) )
import qualified Utilities.Map   as M
import Utilities.Relation (type(<->),(|>),(<|))
import qualified Utilities.Relation as R
import Utilities.Syntactic
import Utilities.Table

type LiveEvtId = Either EventId ProgId

run_phase4_proofs :: Pipeline MM SystemP3 SystemP4
run_phase4_proofs = proc (SystemP r_ord p3) -> do
        refs   <- run_phase 
            [ ref_replace_csched
            , ref_replace_fsched ] -< p3
        ref_p  <- refine_prog_prop -< p3
        comm   <- all_comments -< p3
        prfs   <- all_proofs   -< p3
        let c_evt_refs :: Maybe (MTable (Table EventId [((Label,ScheduleChange),LineInfo)]))
            c_evt_refs = M.map (M.fromListWith (++)) 
                     <$> M.unionsWith (++) 
                     <$> L.map (M.map coarseRef) <$> refs 
            f_evt_refs' :: Maybe (MTable (Table EventId [((ProgId,ProgressProp),LineInfo)]))
            f_evt_refs' = M.map (M.fromListWith (++)) 
                     <$> M.unionsWith (++)
                     <$> L.map (M.map fineRef) <$> refs
        f_evt_refs <- liftP' $ fmap Just . T.mapM (M.traverseWithKey only_one)
            -< f_evt_refs'
        prog_ref <- liftP' (make_all_tables refClash)   -< ref_p
        proofs   <- liftP' (make_all_tables proofClash) -< prfs
        comments <- liftP' (make_all_tables commClash)  -< inherit r_ord <$> comm
        let 
        f_evt_refs <- triggerP -< f_evt_refs
        c_evt_refs <- triggerP -< c_evt_refs
        prog_ref   <- triggerP -< prog_ref
        proofs     <- triggerP -< proofs
        comments   <- triggerP -< comments
        let _ = c_evt_refs :: MTable (Table EventId [((Label,ScheduleChange),LineInfo)])
            _ = f_evt_refs :: MTable (Table EventId (Maybe ((ProgId,ProgressProp),LineInfo)))
            _ = prog_ref :: MTable (Table ProgId ((Rule,[(ProgId,ProgId)]),LineInfo))
            evt_ref_props :: MTable (Table EventId [(ProgId,LineInfo)])
            evt_ref_props = M.unionWith (M.unionWith (++)) 
                        (M.map (M.map $ L.map $ first $ hyps_label . snd) c_evt_refs) 
                        (M.map (M.map $ L.map (first fst) . MM.maybeToList) f_evt_refs)
            evt_live :: MTable (EventId <-> ProgId)
            evt_live  = M.map R.fromListMap $ M.map (M.map $ L.map fst) evt_ref_props
            live_evt :: MTable (ProgId <-> EventId)
            live_evt  = M.map (R.fromListMap . M.map (supporting_evts . fst . fst)) prog_ref
                -- 
            evt_evt :: MTable (Table EventId EventId)
            evt_evt   = M.map (view $ pOldEvents . to (M.mapWithKey const)) p3 -- evt_refs 
            live_live :: MTable (LiveEvtId <-> LiveEvtId)
            live_live = M.map (R.bimap Right Right) $
                        M.map (R.fromListMap . M.map (L.map snd . snd . fst)) prog_ref
            uncurryMap m = M.fromList [((eid,p),li) | (eid,xs) <- M.toList m, (p,li) <- xs ]
            live_struct = LiveStruct <$> (M.map (view pMachineId) p3) 
                   <.> evt_live <.> live_live 
                   <.> live_evt <.> evt_evt 
                   <.> M.mapWithKey (\k -> M.map (k,)) (M.map (M.map snd) prog_ref) 
                   <.> M.mapWithKey (\k -> M.map (k,)) 
                            (M.map uncurryMap evt_ref_props) --evt_refs)
        struct <- liftP' $ fmap Just . T.mapM (fromEither' . raiseStructError)
            -< Just $ inheritWith 
                        Conc (Abs . getConcrete)
                        mergeLiveness 
                        r_ord live_struct
                    -- >>= make_all_tables' _
        _struct <- triggerP -< struct
        let p4 = make_phase4 <$> p3 
                             <.> c_evt_refs <.> f_evt_refs -- evt_refs 
                             <.> prog_ref <.> comments 
                             <.> proofs 
        returnA -< SystemP r_ord p4
    where
        refClash   = format "Multiple refinement of progress property {0}"
        commClash  = format "Multiple comments for {0}"
        proofClash = format "Multiple proofs labeled {0}"
        only_one _ []   = return Nothing
        only_one _ [x]  = return (Just x)
        only_one eid xs = tell [MLError (format "Multiple refinement provided for the fine schedule of {0}" eid) 
                                    $ L.map (first $ show . fst) xs] >> return Nothing

make_phase4 :: MachineP3 
            -> Table EventId [((Label, ScheduleChange), LineInfo)]
            -> Table EventId (Maybe ((ProgId,ProgressProp),LineInfo))
            -> Table ProgId ((Rule,[(ProgId,ProgId)]),LineInfo) 
            -> Table DocItem (String,LineInfo)
            -> Table Label (Tactic Proof, LineInfo) 
            -> MachineP4
make_phase4 p3 coarse_refs fine_refs prog_ref comments proofs 
        = -- makeMachineP4' p3 _ 
            MachineP4 { .. }
    where
        updateEvt :: SkipOrEvent -> EventP3 -> EventP4
        updateEvt (Right eid) e = EventP4 e 
                (findWithDefault [] eid _pCoarseRef) 
                (findWithDefault Nothing eid _pFineRef) 
        updateEvt (Left SkipEvent) e = EventP4 e [] Nothing
        _p3 = p3 & pEventRef %~ G.mapLeftWithKey updateEvt
        _pProofs = proofs
        _pCoarseRef = M.map (L.map fst) coarse_refs
        _pFineRef   = M.map (fmap fst) fine_refs
        _pLiveRule  = M.map (fst . fst) prog_ref
        _pComments  = M.map fst comments

raiseStructError :: Conc LiveStruct -> Either [Error] LiveStruct
raiseStructError (Conc ls@(LiveStruct { .. }))
        | L.null es = Right ls
        | otherwise = Left es
    where
        cycles = R.cycles live_live
        edges  = L.map ((\s -> s <| live_live |> s) . S.fromList) cycles
        es = L.map (MLError (msg $ show machine_id) . L.map err_item . R.toList) edges
        err_item :: (LiveEvtId, LiveEvtId) -> (String, LineInfo)
        err_item = uncurry (\les -> first $ name les) . (id &&& uncurry li)
        msg = format "A cycle exists in the liveness proof"
        name (Left e,_) m = format "Event {0} (refined in {1})" e m
        name (Right e,_) m = format "Progress property {0} (refined in {1})" e m
        li (Left e) (Right l) = evt_info ! (e,l)
        li (Left _) (Left _)  = error "raiseStructError: event refined by event"
        li (Right l) _ = live_info ! l

data LiveStruct = LiveStruct 
    { machine_id :: MachineId
    , evt_live  :: EventId <-> ProgId
    , live_live :: LiveEvtId  <-> LiveEvtId
    , live_evt  :: ProgId  <-> EventId
    , evt_evt   :: Table EventId EventId
    , live_info :: Table ProgId (MachineId,LineInfo)
    , evt_info  :: Table (EventId,ProgId) (MachineId,LineInfo)
    } 

mergeLiveness :: Conc LiveStruct -> Abs LiveStruct -> Conc LiveStruct
mergeLiveness (Conc cl) (Abs al) = Conc LiveStruct
        { machine_id = machine_id cl
        , evt_live  = evt_live cl
        , live_live =           live_live cl 
                      `R.union` remove_old_evt (live_live al)
                      `R.union` R.bimap Right Left (live_evt al)
                      `R.union` R.bimap Left Right (evt_live cl)
        , live_evt  = live_evt cl
        , evt_evt   = evt_evt cl
        , live_info = live_info cl `M.union` live_info al
        , evt_info  = evt_info  cl
        }
    where
        remove_old_evt r = (            R.bimapMaybe as_live as_event r 
                            `R.compose` R.bimapMaybe as_event as_live r )
                    `R.union` R.bimapMaybe as_live as_live r
        as_event :: LiveEvtId -> Maybe EventId
        as_event = leftToMaybe
        as_live :: LiveEvtId -> Maybe LiveEvtId
        as_live = fmap Right . rightToMaybe

refine_prog_prop :: MPipeline MachineP3
                [(ProgId,(Rule,[(ProgId,ProgId)]),LineInfo)]
refine_prog_prop = machineCmd "\\refine" $ \(goal, RuleName rule, hyps, PlainText hint) m p3 -> do
        let p2   = (p3 ^. machineP2') 
                        & pEventRef %~ G.mapBoth (view e2) (view e2)
                        & pContext %~ view t2
            prog = p3 ^. pProgress
            saf  = p3 ^. pSafety
            tr   = p3 ^. pTransient
            parser = p3 ^. pMchSynt
            rule' = map toLower rule
            goal' = as_label goal
            hyps' = map as_label hyps
            dep = map (goal,) hyps
        r <- parse_rule' rule'
            (RuleParserDecl p2 m (M.mapKeys as_label prog) saf tr goal' hyps' hint parser)
        li <- ask
        return [(goal,(r,dep),li)]

ref_replace_csched :: MPipeline MachineP3 EventRefA
ref_replace_csched = machineCmd "\\replace" $ \(Abs evt_lbl,del',added',kept',prog) m p3 -> do
        -- let lbls  = (S.elems $ add `S.union` del `S.union` keep)
        let del   = map (getCoarseSchLbl . getAbstract) del'
            added = map (getCoarseSchLbl . getConcrete) added'
            kept  = map (getCoarseSchLbl . getCommon) kept'
        (pprop,evt) <- toEither $ do
            pprop <- fromEither (error "replace_csched: prog") 
                        $ get_progress_prop p3 m prog
            evt   <- fromEither (error "replace_csched: evt")
                        $ get_abstract_event p3 evt_lbl
            return (pprop,evt)
        toEither $ do
            _ <- fromEither undefined $ bind_all del 
                    (format "'{1}' is not the label of a coarse schedule of '{0}' deleted during refinement" evt) 
                    (`M.lookup` (M.unions $ p3^.evtSplitDel AST.assert evt eCoarseSched))
            _ <- fromEither undefined $ bind_all added 
                    (format "'{1}' is not the label of a coarse schedule of '{0}' added during refinement" evt) 
                    (`M.lookup` (M.unions $ p3^.evtSplitAdded AST.assert evt eCoarseSched))
            _ <- fromEither undefined $ bind_all kept 
                    (format "'{1}' is not the label of a coarse schedule of '{0}' kept during refinement" evt) 
                    (`M.lookup` (M.unions $ p3^.evtSplitKept AST.assert evt eCoarseSched))
            return ()
        let rule = replace (as_label prog,pprop)
                        & remove .~ fromList' del
                        & add  .~ fromList' added
                        & keep .~ fromList' kept
            po_lbl = composite_label ["SCH",as_label m]            
        li <- lift ask
        return $ EventRef [(evt,[((po_lbl,rule),li)])] []

ref_replace_fsched :: MPipeline MachineP3 EventRefA
ref_replace_fsched = machineCmd "\\replacefine" $ \(Abs evt_lbl,prog) m p3 -> do
        evt <- get_abstract_event p3 evt_lbl
        pprop <- get_progress_prop p3 m prog
        let rule      = (prog,pprop)
        li <- lift ask
        return $ EventRef [] [(evt,[(rule,li)])]


all_comments :: MPipeline MachineP3 [(DocItem, String, LineInfo)]
all_comments = machineCmd "\\comment" $ \(PlainText item',PlainText cmt') _m p3 -> do
                li <- lift ask
                let item = L.filter (/= '$') $ remove_ref $ flatten' item'
                    cmt = flatten' cmt'
                    -- prop = props m
                    invs = p3^.pInvariant
                    is_inv = label item `member` invs
                    progs = p3^.pProgress
                    is_prog = PId (label item) `member` progs
                    evts = p3^.pEventIds
                    is_event = label item `member` evts
                    vars = p3^.pStateVars
                let item' = isName' item
                    is_var = W.filter (`member` vars) item'
                    lbl = label item
                    conds = [is_inv,is_prog,is_event, MM.isJust is_var]
                unless (length (L.filter id conds) <= 1)
                    $ fail "all_comments: conditional not mutually exclusive"
                key <- if is_inv then do
                    return $ DocInv lbl
                else if is_prog then do
                    return $ DocProg lbl
                else if is_event then do
                    return $ DocEvent (EventId lbl)
                else case is_var of
                    Just item -> return $ DocVar item
                    _ -> do
                        let msg = "`{0}` is not one of: a variable, an event, \
                                  \ an invariant or a progress property "
                        unless (not $ or conds)
                            $ fail "all_comments: conditional not exhaustive"
                        left [Error (format msg item) li]
                return [(key,cmt,li)]

all_proofs :: MPipeline MachineP3 [(Label,Tactic Proof,LineInfo)]
all_proofs = machineEnv "proof" $ \(Identity (PO po)) xs m p3 -> do
        li <- lift ask
        let notation = p3^.pNotation
            po_lbl = label $ remove_ref po
            lbl = composite_label [ as_label m, po_lbl ]
        proof <- mapEitherT 
            (\cmd -> runReaderT cmd notation) 
            $ run_visitor li xs collect_proof_step 
        return [(lbl,proof,li)]

get_progress_prop :: MachineP3 -> MachineId -> ProgId -> M ProgressProp
get_progress_prop p3 _m lbl =  
            bind
                (format "progress property '{0}' is undeclared" lbl)
                $ lbl `M.lookup` (L.view pProgress p3)

get_safety_prop :: MachineP3 -> MachineId -> Label -> M SafetyProp
get_safety_prop p3 _m lbl =  
            bind
                (format "safety property '{0}' is undeclared" lbl)
                $ lbl `M.lookup` (L.view pSafety p3)

get_guards :: MachineP3 -> EventId -> M (Table Label Expr)
get_guards p3 evt = 
        return $ p3^.getEvent evt.eGuards

parse_rule' :: String
            -> RuleParserParameter
            -> M Rule
parse_rule' rule param = do
    li <- lift ask
    case M.lookup rule refinement_parser of
        Just f -> EitherT $ mapRWST (\x -> return (runIdentity x)) $
            runEitherT $ f param
        Nothing -> raise $ Error (format "invalid refinement rule: {0}" rule) li

refinement_parser :: Map String (
                  RuleParserParameter
               -> M Rule)
refinement_parser = fromList 
    [   ("disjunction", parse Disjunction) -- parse (disjunction, ()))
    ,   ("discharge", parse_discharge)
    ,   ("monotonicity", parse Monotonicity) -- parse (Monotonicity, ()))
    ,   ("implication", parse Implication) -- parse (Implication, ()))
    ,   ("trading", parse NegateDisjunct) -- parse (NegateDisjunct, ()))
    ,   ("transitivity", parse Transitivity) -- parse (Transitivity, ()))
    ,   ("psp", parse PSP) -- parse (PSP, ()))
    ,   ("ensure", parse_ensure) -- parse (ensure, ()))
    ,   ("induction", parse_induction)
    ]

data HintBuilder = 
        HintBuilderDecl LatexDoc MachineId MachineP2

data EventRefA = EventRef 
        { coarseRef :: [(EventId,[((Label,ScheduleChange),LineInfo)])]
        , fineRef :: [(EventId,[((ProgId,ProgressProp),LineInfo)])] }
    deriving (Generic)

instance NFData EventRefA where

instance Monoid EventRefA where
    mempty = EventRef [] []
    mappend (EventRef xs0 xs1) (EventRef ys0 ys1) = 
            EventRef (xs0 ++ ys0) (xs1 ++ ys1)
