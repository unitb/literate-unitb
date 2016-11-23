{-# LANGUAGE TypeOperators
    , Arrows
    , ConstraintKinds
    , OverloadedStrings
    , RecordWildCards 
    , ScopedTypeVariables #-}
module Document.Phase.Proofs 
    (run_phase4_proofs,make_phase4)
where

    --
    -- Modules
    --
import Document.Pipeline
import Document.Phase as P
import Document.Phase.Expressions
import Document.Phase.Latex
import Document.Phase.Parameters
import Document.Phase.Transient
import Document.Phase.Types
import Document.Proof
import Document.Refinement as Ref
import Document.Scope  hiding (contents)
import Document.Visitor

import Latex.Parser 

import Logic.Expr.Parser

import Logic.Proof
import Logic.Proof.Tactics hiding ( with_line_info )

import UnitB.Expr
import UnitB.Syntax as AST

    --
    -- Libraries
    --
import Control.Applicative
import Control.Arrow hiding (left,app) -- (Arrow,arr,(>>>))
import Control.Category
import Control.DeepSeq
import Control.Precondition ((!))

import           Control.Monad 
import           Control.Monad.Reader.Class 
import           Control.Monad.Writer hiding ((<>))
import           Control.Monad.Trans.Either
import           Control.Monad.Trans.Reader ( runReaderT )
import           Control.Monad.Trans.RWS as RWS ( mapRWST )

import Control.Lens as L hiding ((|>),(<.>),(<|),indices,Context)

import           Data.Char
import           Data.Constraint (Dict(..),(:-)(..))
import           Data.Either.Combinators
import           Data.Either.Validation
import           Data.Existential
import           Data.Functor.Compose
import qualified Data.Graph.Bipartite as G
import qualified Data.Maybe as MM
import           Data.List as L hiding ( union, insert, inits )
import           Data.List.NonEmpty hiding ((<|),map,length,fromList)
import           Data.Map   as M hiding ( map, (\\), (!) )
import qualified Data.Map   as M
import           Data.Proxy.TH
import           Data.Relation (type(<->),(|>),(<|))
import qualified Data.Relation as R
import qualified Data.Set as S
import qualified Data.Traversable as T
import           Data.Witherable  as W

import GHC.Generics (Generic)

import Prelude hiding (id,(.))

import Text.Printf.TH

import Utilities.Syntactic

type LiveEvtId = Either EventId ProgId

run_phase4_proofs :: Pipeline MM SystemP3 SystemP4
run_phase4_proofs = proc (SystemP r_ord p3) -> do
        refs   <- run_phase 
            [ ref_replace_csched
            , ref_replace_fsched ] -< p3
        ref_p  <- refine_prog_prop &&& liveness_proofs 
                >>> arr (uncurry $ liftA2 (unionWith (++))) -< p3
        comm   <- all_comments -< p3
        prfs   <- all_proofs   -< p3
        let c_evt_refs :: Maybe (MMap (Map EventId [((Label,ScheduleChange),LineInfo)]))
            c_evt_refs = M.map (M.fromListWith (++)) 
                     <$> M.unionsWith (++) 
                     <$> L.map (M.map coarseRef) <$> refs 
            f_evt_refs' :: Maybe (MMap (Map EventId [((ProgId,ProgressProp),LineInfo)]))
            f_evt_refs' = M.map (M.fromListWith (++)) 
                     <$> M.unionsWith (++)
                     <$> L.map (M.map fineRef) <$> refs
        f_evt_refs <- liftP' $ fmap Just . T.mapM (M.traverseWithKey only_one)
            -< f_evt_refs'
        prog_ref <- liftP' (make_all_tables refClash)   -< ref_p
        proofs   <- liftP' (make_all_tables proofClash) -< prfs
        comments <- liftP' (make_all_tables commClash)  -< inherit r_ord <$> comm
        f_evt_refs <- triggerP -< f_evt_refs
        c_evt_refs <- triggerP -< c_evt_refs
        prog_ref   <- triggerP -< prog_ref
        proofs     <- triggerP -< proofs
        comments   <- triggerP -< comments
        let _ = c_evt_refs :: MMap (Map EventId [((Label,ScheduleChange),LineInfo)])
            _ = f_evt_refs :: MMap (Map EventId (Maybe ((ProgId,ProgressProp),LineInfo)))
            _ = prog_ref :: MMap (Map ProgId ((Rule,[(ProgId,ProgId)]),LineInfo))
            evt_ref_props :: MMap (Map EventId [(ProgId,LineInfo)])
            evt_ref_props = M.unionWith (M.unionWith (++)) 
                        (M.map (M.map $ L.map $ first $ hyps_label . snd) c_evt_refs) 
                        (M.map (M.map $ L.map (first fst) . MM.maybeToList) f_evt_refs)
            evt_live :: MMap (EventId <-> ProgId)
            evt_live  = M.map R.fromListMap $ M.map (M.map $ L.map fst) evt_ref_props
            live_evt :: MMap (ProgId <-> EventId)
            live_evt  = M.map (R.fromListMap . M.map (supporting_evts . fst . fst)) prog_ref
                -- 
            evt_evt :: MMap (Map EventId EventId)
            evt_evt   = M.map (view $ pOldEvents . to (M.mapWithKey const)) p3 -- evt_refs 
            live_live :: MMap (LiveEvtId <-> LiveEvtId)
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
        refClash :: ProgId -> String
        refClash   = [s|Multiple refinement of progress property %s|] . pretty
        commClash :: DocItem -> String
        commClash  = [s|Multiple comments for %s|] . pretty
        proofClash :: Label -> String
        proofClash = [s|Multiple proofs labeled %s|] . pretty
        only_one :: EventId -> [((ProgId, ProgressProp), LineInfo)] 
                 -> MM (Maybe ((ProgId, ProgressProp), LineInfo))
        only_one _ []   = return Nothing
        only_one _ [x]  = return (Just x)
        only_one eid (x:xs) = tell [MLError ([s|Multiple refinement provided for the fine schedule of %s|] $ pretty eid) 
                                    $ first (pretty . fst) <$> (x:|xs)] >> return Nothing

make_phase4 :: MachineP3 
            -> Map EventId [((Label, ScheduleChange), LineInfo)]
            -> Map EventId (Maybe ((ProgId,ProgressProp),LineInfo))
            -> Map ProgId ((Rule,[(ProgId,ProgId)]),LineInfo) 
            -> Map DocItem (String,LineInfo)
            -> Map Label (Tactic Proof, LineInfo) 
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
        cycles :: [[LiveEvtId]]
        cycles = R.cycles live_live
        edges :: [R.Relation LiveEvtId LiveEvtId]
        edges  = L.map ((\s -> s <| live_live |> s) . S.fromList) cycles
        es = W.mapMaybe (fmap (MLError $ msg machine_id) . nonEmpty . L.map err_item . R.toList) edges
        err_item :: (LiveEvtId, LiveEvtId) -> (String, LineInfo)
        err_item = uncurry (\les -> first $ name les) . (id &&& uncurry li)
        msg _ = "A cycle exists in the liveness proof"
        name :: (LiveEvtId,a) -> MachineId -> String
        name (Left e,_) m = [s|Event %s (refined in %s)|] (pretty e) (pretty m)
        name (Right prop,_) m = [s|Progress property %s (refined in %s)|] (pretty prop) (pretty m)
        li (Left e) (Right l) = evt_info ! (e,l)
        li (Left _) (Left _)  = error "raiseStructError: event refined by event"
        li (Right l) _ = live_info ! l

data LiveStruct = LiveStruct 
    { machine_id :: MachineId
    , evt_live  :: EventId <-> ProgId
    , live_live :: LiveEvtId  <-> LiveEvtId
    , live_evt  :: ProgId  <-> EventId
    , evt_evt   :: Map EventId EventId
    , live_info :: Map ProgId (MachineId,LineInfo)
    , evt_info  :: Map (EventId,ProgId) (MachineId,LineInfo)
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
refine_prog_prop = machineCmd "\\refine" $ \(goal, RuleName rule, hyps, PlainText hint) _m p3 -> do
        let rule' = map toLower rule
            goal' = as_label goal
            hyps' = map as_label hyps
            dep = map (goal,) hyps
        r <- parse_rule' rule'
            (RuleParserDecl p3 goal' hyps' hint)
        li <- ask
        return [(goal,(r,dep),li)]

ref_replace_csched :: MPipeline MachineP3 EventRefA
ref_replace_csched = machineCmd "\\replace" $ \(Abs evt_lbl,added',prog) m p3 -> do
        let 
            added = map (getCoarseSchLbl . getConcrete) added'
        (pprop,evt) <- toEither $ do
            pprop <- fromEither (error "replace_csched: prog") 
                        $ _unM $ get_progress_prop p3 m prog
            evt   <- fromEither (error "replace_csched: evt")
                        $ _unM $ get_abstract_event p3 evt_lbl
            return (pprop,evt)
        toEither $ do
            _ <- fromEither undefined $ _unM $ bind_all added 
                    (\lbl -> [s|'%s' is not the label of a coarse schedule of '%s' added during refinement|] (pretty lbl) (pretty evt)) 
                    (`M.lookup` (M.unions $ p3^.evtSplitConcrete evt eCoarseSched))
            return ()
        let rule = replace (as_label prog,pprop)
                        & add  .~ fromList' added
            po_lbl = composite_label ["SCH",as_label m]            
        li <- ask
        return $ EventRef [(evt,[((po_lbl,rule),li)])] []

ref_replace_fsched :: MPipeline MachineP3 EventRefA
ref_replace_fsched = machineCmd "\\replacefine" $ \(Abs evt_lbl,prog) m p3 -> do
        evt <- get_abstract_event p3 evt_lbl
        pprop <- get_progress_prop p3 m prog
        let rule      = (prog,pprop)
        li <- ask
        return $ EventRef [] [(evt,[(rule,li)])]


all_comments :: MPipeline MachineP3 [(DocItem, String, LineInfo)]
all_comments = machineCmd "\\comment" $ \(PlainText item',PlainText cmt') _m p3 -> do
                li <- ask
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
                        let msg = [s|`%s` is not one of: a variable, an event, an invariant or a progress property |]
                        unless (not $ or conds)
                            $ fail "all_comments: conditional not exhaustive"
                        raise $ Error (msg item) li
                return [(key,cmt,li)]

liveness_proofs :: MPipeline MachineP3 
                [(ProgId,(Rule,[(ProgId,ProgId)]),LineInfo)]
liveness_proofs = machineEnv "liveness" $ \(Identity (PO po)) xs _m p3 -> do
        li <- ask
        proof <- parseLatex (liveness p3) xs ()
        let dep = [ (goal,h) | h <- proof^.partsOf traverseProgId ]
            goal = PId $ label po
        prop <- bind ([s|'%s' is not the name of a progress property in this machine|] po)
            $ goal `M.lookup` (p3^.pProgress)
        return [(goal,(makeMonotonicity prop proof,dep),li)]

liveness :: MachineP3 -> LatexParser ProofTree
liveness m = withLineInfo $ proc () -> do
        (goal,evts,hint,rProxy) <- prop -< ()
        subTrees <- step <!> nostep -< (goal,rProxy)
        tree <- makeRule -< (evts,hint,subTrees)
        returnA -< tree
    where
        prop :: LatexParser (RawProgressProp,[EventOrRef],LatexDoc,RuleProxy)
        prop = withCommand "\\progstep" $ progStep m
        nostep :: LatexParserA (RawProgressProp,RuleProxy) VoidInference
        nostep = lift' $ \(prog,rule) -> maybe 
            (raise' $ Error $ [s|Expecting premises to rule: %s|] $ readCell1' (pretty . rule_name') rule) 
            return
            (readCell1' (voidInference (Sub Dict) prog) rule)
        makeRule :: LatexParserA ([EventOrRef],LatexDoc,VoidInference) ProofTree
        makeRule = lift' (uncurry3 $ \evts hint -> wrapUpTree . traverseCell1 (fillInRule evts hint . getCompose))
        uncurry3 f (x,y,z) = f x y z
        wrapUpTree :: M (Cell1 Inference RuleParser) -> M ProofTree
        wrapUpTree = fmap (ProofTree . rewriteCell (Sub Dict))
        fillInRule :: forall rule. RuleParser rule 
                   => [EventOrRef]
                   -> LatexDoc
                   -> Inference (Proxy rule) 
                   -> M (Inference rule)
        fillInRule evts hint inf = do
            es <- makeEventList [pr|rule|] $ getEventOrRef <$> evts
            r  <- promoteRule m inf es hint
            return $ inf & ruleLens .~ r
        step :: LatexParserA (RawProgressProp,RuleProxy) VoidInference
        step = insideOneEnvOf ["step","flatstep"] $ proc (goal,prxy) -> do 
                Cell prxy' <- arr (view cell) -< prxy
                stepList m -< (goal,Inst prxy')

type VoidInference = Cell1 (Compose Inference Proxy) RuleParser

expr :: MachineP3 -> StringLi -> Validation [Error] RawExpr
expr m = eitherToValidation . fmap asExpr . parse_expr (m^.pMchSynt & free_dummies .~ True)

liftA4 :: Applicative f 
       => (a -> b -> c -> d -> e)
       -> f a -> f b -> f c -> f d -> f e
liftA4 f x0 x1 x2 x3 = liftA3 f x0 x1 x2 <*> x3

trStep :: MachineP3
       -> (NonEmpty (Conc EventId),PlainText,ExprText)
       -> M RawTransient
trStep m (evts,PlainText hint,Expr p) = do
        tr <- triggerV $ expr m p
        let ds  = m^.pDummyVars
            dum = free_vars' ds tr
            evts' = getConcrete <$> evts 
        hint <- local (const $ line_info hint) 
              $ tr_hint m dum
                (as_label <$> evts') hint
        return $ transientProp m tr evts' (asExpr <$> hint)

safStep :: MachineP3
        -> (ExprText,ExprText)
        -> M (RawSafetyProp, Maybe Label)
safStep m (Expr p,Expr q) = hoistValidation $
        (,Nothing) <$> liftA2 (unlessProp m) (expr m p) (expr m q)

progStep :: MachineP3
         -> (ExprText,ExprText,RuleName,[EventOrRef],PlainText)
         -> M (RawProgressProp,[EventOrRef],LatexDoc,RuleProxy)
progStep m (Expr p,Expr q,RuleName r,evts,PlainText hint) = liftA4 (,,,)
        (hoistValidation $ liftA2 (leadsTo m) (expr m p) (expr m q))
        (pure evts)
        (pure hint)
        (parse_naked_rule r)

stepList :: MachineP3
         -> LatexParserA (RawProgressProp,Inst1 Proxy RuleParser rule) VoidInference
stepList m = arr (dict.snd) &&& stepList' m >>> arr (\(Dict,inf) -> Cell (Compose inf))


stepList' :: MachineP3
          -> LatexParserA 
                (RawProgressProp,Inst1 Proxy RuleParser rule) 
                (Inference (Proxy rule))
stepList' m = 
                arr (Inference . fst)
            <*> arr (view inst1 . snd)
            <*> (consume' <<< buildProgress (Sub Dict) (withLookAhead $ liveness m) <<< pre) 
            <*> (consume' <<< buildTransient (Sub Dict) (withLookAhead transient) <<< pre)
            <*> (consume' <<< buildSafety (Sub Dict) (withLookAhead safety) <<< pre)
    where
        pre = arr snd >>> (id &&& getLineInfo) >>> arr (\(r,li) -> ((),r,li))
        safety :: LatexParser (RawSafetyProp, Maybe Label)
        safety = withCommand "\\safstep" $ safStep m
        transient :: LatexParser RawTransient
        transient = withCommand "\\trstep" $ trStep m

parse_naked_rule :: String -> M RuleProxy
parse_naked_rule rule = do
    li <- ask
    case M.lookup rule ruleProxies of
        Just x -> return x
        Nothing -> raise $ Error ([s|invalid refinement rule: %s|] rule) li

ruleProxies :: Map String RuleProxy
ruleProxies = fromList $ execWriter $ do
        "discharge"    `with` [pr|Discharge|]
        "disjunction"  `with` [pr|Disjunction|]
        "monotonicity" `with` [pr|Monotonicity|]
        "transitivity" `with` [pr|Transitivity|]
        "implication"  `with` [pr|Implication|]
        "induction"    `with` [pr|Induction|]
        "trading" `with` [pr|NegateDisjunct|]
        "psp"     `with` [pr|PSP|]
        "ref"     `with` [pr|Reference|]
        "ensure"  `with` [pr|Ensure|]
    where
        x `with` y = tell [(x,makeCell1 y)]

all_proofs :: MPipeline MachineP3 [(Label,Tactic Proof,LineInfo)]
all_proofs = machineEnv "proof" $ \(Identity (PO po)) xs m p3 -> do
        li <- ask
        let notation = p3^.pNotation
            po_lbl = label $ remove_ref po
            lbl = composite_label [ as_label m, po_lbl ]
        proof <- M $ mapEitherT 
            (\cmd -> runReaderT cmd notation) 
            $ run_visitor li xs collect_proof_step 
        return [(lbl,proof,li)]

get_progress_prop :: MachineP3 -> MachineId -> ProgId -> M ProgressProp
get_progress_prop p3 _m lbl =  
            bind
                ([s|progress property '%s' is undeclared|] $ pretty lbl)
                $ lbl `M.lookup` (L.view pProgress p3)



parse_rule' :: String
            -> RuleParserParameter
            -> M Rule
parse_rule' rule param = do
    li <- ask
    case M.lookup rule refinement_parser of
        Just f -> M $ EitherT $ mapRWST (\x -> return (runIdentity x)) $
            runEitherT $ _unM $ f param
        Nothing -> raise $ Error ([s|invalid refinement rule: %s|] rule) li

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


data EventRefA = EventRef 
        { coarseRef :: [(EventId,[((Label,ScheduleChange),LineInfo)])]
        , fineRef :: [(EventId,[((ProgId,ProgressProp),LineInfo)])] }
    deriving (Generic)

instance NFData EventRefA where

instance Monoid EventRefA where
    mempty = EventRef [] []
    mappend (EventRef xs0 xs1) (EventRef ys0 ys1) = 
            EventRef (xs0 ++ ys0) (xs1 ++ ys1)
