{-# LANGUAGE BangPatterns, FlexibleContexts     #-}
{-# LANGUAGE TupleSections, ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances, Arrows          #-}
{-# LANGUAGE TypeOperators, TypeFamilies        #-}
{-# LANGUAGE MultiParamTypeClasses              #-}
{-# LANGUAGE TemplateHaskell, OverloadedStrings #-}
{-# LANGUAGE RecordWildCards, RankNTypes        #-}
module Document.Machine where

    --
    -- Modules
    --
import Document.Expression
import Document.ExprScope
import Document.Pipeline
import Document.Phase as P
import Document.Proof
import Document.Refinement as Ref
import Document.Scope
import Document.VarScope
import Document.Visitor

import Latex.Parser hiding (contents)

import Logic.Expr
import Logic.Operator (Notation)
import Logic.Proof hiding ( with_line_info )

import UnitB.AST as AST
import UnitB.PO

import Theories.Arithmetic
import Theories.FunctionTheory
import Theories.IntervalTheory
import Theories.PredCalc
import Theories.SetTheory

    --
    -- Libraries
    --
import Control.Arrow hiding (left,app) -- (Arrow,arr,(>>>))
import qualified Control.Category as C

import           Control.Monad 
import           Control.Monad.Reader.Class 
import           Control.Monad.State.Class 
import           Control.Monad.Writer.Class 
import           Control.Monad.Trans
import           Control.Monad.Trans.Either
import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans.Reader ( runReaderT )
import           Control.Monad.Trans.RWS as RWS ( execRWS, RWS, mapRWST )

import Control.Lens as L hiding ((|>),(<.>),(<|),indices,Context)

import           Data.Char
import           Data.Default
import           Data.Either
import           Data.Either.Combinators
import           Data.Functor
import           Data.Graph
import           Data.Map   as M hiding ( map, foldl, (\\) )
import qualified Data.Map   as M
import qualified Data.Maybe as MM
import           Data.Monoid
import           Data.List as L hiding ( union, insert, inits )
import           Data.List.NonEmpty ( NonEmpty(..) )
import qualified Data.List.NonEmpty as NE
import qualified Data.Set as S
import qualified Data.Traversable as T

import Utilities.Format
import Utilities.Relation (type(<->),(|>),(<|))
import qualified Utilities.Relation as R
import Utilities.Syntactic
import Utilities.Trace ()
        
parse_rule' :: String
            -> RuleParserParameter
            -> M Rule
parse_rule' rule param = do
    li <- lift ask
    case M.lookup rule refinement_parser of
        Just f -> EitherT $ mapRWST (\x -> return (runIdentity x)) $
            runEitherT $ f rule param
        Nothing -> raise $ Error (format "invalid refinement rule: {0}" rule) li

refinement_parser :: Map String (
                  String
               -> RuleParserParameter
               -> M Rule)
refinement_parser = fromList 
    [   ("disjunction", parse (disjunction, ()))
    ,   ("discharge", parse_discharge)
    ,   ("monotonicity", parse (Monotonicity, ()))
    ,   ("implication", parse (Implication, ()))
    ,   ("trading", parse (NegateDisjunct, ()))
    ,   ("transitivity", parse (Transitivity, ()))
    ,   ("psp", parse (PSP, ()))
    ,   ("ensure", parse (ensure, ()))
    ,   ("induction", parse_induction)
    ]

    -- Remove alternatives
data HintBuilder = 
        HintBuilderDecl [LatexDoc] MachineId MachineP2

ensure :: ProgressProp 
       -> HintBuilder
       -> [Label]
       -> M Ensure
ensure prog@(LeadsTo fv _ _) hint lbls = do
        let vs = symbol_table fv
        lbls' <- bind  "Expected non empty list of events"
                    $ NE.nonEmpty lbls
        let HintBuilderDecl thint m p2 = hint
        hint <- tr_hint p2 m vs lbls' thint
        _    <- get_events p2 lbls
        return $ Ensure prog lbls hint

instance RuleParser (a,()) => RuleParser (HintBuilder -> a,()) where
    parse_rule (f,_) xs rule param@(RuleParserDecl p2 m _ _ _ _ _ hint _) = do
        parse_rule (f (HintBuilderDecl hint m p2),()) xs rule param


topological_order :: Pipeline MM
                     (Map MachineId (MachineId,LineInfo)) 
                     (Hierarchy MachineId)
topological_order = Pipeline empty_spec empty_spec $ \es' -> do
        let es = M.map fst es'
            lis = M.map snd es'
            cs = cycles $ toList es
        vs <- MaybeT $ sequence <$> mapM (cycl_err_msg lis) cs
        return $ Hierarchy vs es
    where
        struct = "refinement structure" :: String
        cycle_msg = format msg struct -- $ intercalate ", " (map show ys)
        cycl_err_msg _ (AcyclicSCC v) = return $ Just v
        cycl_err_msg lis (CyclicSCC vs) = do
            -- li <- ask
            tell [MLError cycle_msg 
                $ L.map (first show) $ toList $ 
                lis `M.intersection` fromList' vs ] 
            return Nothing -- (error "topological_order")
        msg = "A cycle exists in the {0}"

inherit :: Hierarchy MachineId -> Map MachineId [b] -> Map MachineId [b]
inherit = inheritWith id id (++)

inherit2 :: Scope s
         => Hierarchy MachineId
         -> Map MachineId [(t, s)] 
         -> Map MachineId [(t, s)]
inherit2 = inheritWith 
            id
            (MM.mapMaybe $ second' make_inherited)
            (++)
    where
        second' = runKleisli . second . Kleisli
        _ = MM.mapMaybe :: (a -> Maybe a) -> [a] -> [a]

inherit3 :: Hierarchy MachineId
         -> Map MachineId [(t, t2, t1)]
         -> Map MachineId [(t, (t2, DeclSource), t1)]
inherit3 = inheritWith 
            (L.map $ \(x,y,z) -> (x,(y,Local),z))
            (L.map $ \(x,(y,_),z) -> (x,(y,Inherited),z))
            (++)

run_phase1_types :: Pipeline MM 
                        (MTable MachineP0)
                        ( Hierarchy MachineId
                        , MTable MachineP1)
run_phase1_types = proc p0 -> do
    -- traceA $ const "step A" -< ()
    ts <- set_decl      -< p0
    -- traceA $ const "step B" -< ()
    e  <- event_decl    -< p0
    -- traceA $ const "step C" -< ()
    r  <- refines_mch   -< p0
    -- traceA $ const "step D" -< ()
    it <- import_theory -< p0
    -- let refs  = r >>= make_all_tables (format "Multiple refinement clauses")
    -- let refs  = r >>= 
    -- _  <- traceA $ format "step {0}" -< (ts,r,e,it)
    refs <- triggerP <<< liftP' (make_all_tables refClash) -< r
    -- refs <- triggerP -< refs
    let _ = refs :: Map MachineId (Map () (MachineId,LineInfo))
    r_ord <- topological_order -< mapMaybe (M.lookup ()) refs
    let t = M.map fst <$> ts
        s = M.map snd <$> ts
    evts' <- liftP' $ make_all_tables evtClash -< inherit3 r_ord <$> e
    types <- liftP' $ make_all_tables setClash -< inherit r_ord  <$> t
    imp_th <- liftP' $ make_all_tables thyClash -< inherit r_ord  <$> it
    evts'   <- triggerP -< M.map (M.map fst) <$> evts'    
    types   <- triggerP -< types
    imp_th' <- triggerP -< imp_th
    s       <- triggerP -< s
    --     -- BIG FLAG
    --     -- the creation of p1 won't detect clashes between type names, it will merely overshadow
    --     -- some types with (hopefully) the most local types
    --     -- BIG FLAG
    let f th = M.unions $ map AST.types $ M.elems th
        basic = fromList [("arithmetic",arithmetic),("basic",basic_theory)]
        imp_th = M.map (union basic . M.map fst) imp_th'
        all_types = M.intersectionWith (\ts th -> M.map fst ts `union` f th) types imp_th
        p1 = make_phase1 <$> p0 <.> imp_th 
                         <.> (M.map (M.map fst) types) 
                         <.> all_types 
                         <.> s <.> evts'
    returnA -< (r_ord,p1)
  where
    evtClash = format "Multiple events with the name {0}"
    setClash = format "Multiple sets with the name {0}"
    thyClash = format "Theory imported multiple times"
    refClash = format "Multiple refinement clauses"

make_phase1 :: MachineP0
            -> Map String Theory
            -> Map String Sort
            -> Map String Sort
            -> [(String, PostponedDef)]
            -> Map Label (EventId, DeclSource)
            -> MachineP1
make_phase1 _p0 _pImports _pTypes _pAllTypes _pSetDecl evts = MachineP1 { .. }
    where
        _pEvents    = M.map (uncurry EventP1 . second (== Local)) evts ^. pFromEventId
        _pContext   = TheoryP1 { .. }
        _t0         = TheoryP0 ()
        -- _pImports
        -- _pNewEvents = M.map fst $ M.filter ((== Local) . snd) evts

run_phase :: [Pipeline MM a (Maybe b)]
          -> Pipeline MM a (Maybe [b])
run_phase xs = run_phase_aux xs >>> arr sequence

run_phase_aux :: [Pipeline MM a b] -> Pipeline MM a [b]
run_phase_aux [] = arr $ const []
run_phase_aux (cmd:cs) = proc x -> do
        y  <- cmd -< x
        ys <- run_phase_aux cs -< x
        returnA -< y:ys

run_phase2_vars :: Pipeline MM 
                        (Hierarchy MachineId,MTable MachineP1)
                        (MTable MachineP2)
run_phase2_vars = second (C.id &&& symbols) >>> liftP wrapup
    where
        err_msg = format "Multiple symbols with the name {0}"
        wrap = L.map (second $ VarScope . uncurry3 TheoryDef)
        symbols = run_phase
            [ variable_decl
            , constant_decl
            , dummy_decl
            , index_decl
            , arr $ Just . M.map (wrap . L.view pSetDecl)
            , param_decl
            , remove_var ]
        wrapup (r_ord,(p1,vs)) = do
            let vs' = inherit2 r_ord 
                        <$> unionsWith (++)
                        <$> vs
            vars <- triggerM
                =<< make_all_tables' err_msg 
                =<< triggerM vs'
                    
            let _  = vars :: MTable (Map String VarScope)
            T.sequence $ make_phase2 <$> p1 <.> vars

make_phase2 :: MachineP1
            -> Map String VarScope
            -> MM MachineP2 
make_phase2 p1 vars = do
        tell err
        unless (L.null err) $ MaybeT $ return Nothing
        -- | L.null err = 
        return $ p2' & (pNotation .~ _pNotation)
                     & (pMchSynt .~ _pMchSynt)
                     & (pCtxSynt .~ _pCtxSynt)
                     & (pSchSynt .~ _pSchSynt)
                     & (pEvtSynt .~ _pEvtSynt)
    where
        varGroup n (VarScope x) = VarGroup [(n,x)]
        vars' = groupVars $ L.map (uncurry varGroup) $ M.toList vars
        (p2',err) = execRWS (mapM_ f vars') () p2
            where
                p2 =   pContext `over` makeTheoryP2
                     $ pEvents `over` M.map makeEventP2
                     $ makeMachineP2' p1

        f (VarGroup vs) = processDecl vs

        evts  = M.map (const ()) (p1 ^. pEvents)

        ind_param :: Map EventId (Map String Var)
        ind_param   = M.unionWith M.union (p2' ^. pIndices) (p2' ^. pParams)

        _pNotation  = th_notation $ empty_theory { extends = p2' ^. pImports }

        constants = (p2' ^. pConstants) `M.union` (M.mapMaybe defToVar $ p2' ^. pDefinitions)

        _pCtxSynt   = mkSetting _pNotation (p2' ^. pTypes) constants M.empty (p2' ^. pDummyVars)
        _pMchSynt   = mkSetting _pNotation (p2' ^. pTypes) constants refVars (p2' ^. pDummyVars)
        
        refVars = (p2' ^. pAbstractVars) `M.union` (p2' ^. pStateVars)

        findE m e = findWithDefault M.empty e m :: Map String Var

        parser :: Map EventId (Map String Var)
               -> EventId -> ParserSetting
        parser table e    = mkSetting _pNotation (p2' ^. pTypes) (constants `union` findE table e) refVars (p2' ^. pDummyVars)
        
        event_namespace table = 
            M.mapWithKey (const . parser table) evts 

        _pSchSynt :: Map EventId ParserSetting
        _pSchSynt = event_namespace (p2' ^. pIndices)

        _pEvtSynt :: Map EventId ParserSetting
        _pEvtSynt = event_namespace ind_param

default_schedule_decl :: MPipeline MachineP2 [(Label,ExprScope)]
default_schedule_decl = arr $ \p2 -> 
        Just $ M.map (map default_sch . elems . M.map Just . M.map (^. eEventId)) 
              $ M.map (M.filter (^. eIsNew) . (^. pEvents)) p2
    where
        li = LI "default" 1 1
        default_sch e = ( label "default",
                          ExprScope $ EventExpr 
                            $ singleton e (EvtExprScope $ CoarseSchedule (InhAdd zfalse) Inherited li))

run_phase3_exprs :: Pipeline MM (Hierarchy MachineId,MTable MachineP2) (MTable MachineP3)
run_phase3_exprs = second (C.id &&& expressions) >>> liftP (uncurry wrapup)
    where
        err_msg :: Label -> String
        err_msg = format "Multiple expressions with the label {0}"
        wrapup r_ord (p2,es) = do
            let es' = inherit2 r_ord . unionsWith (++) <$> es
            exprs <- triggerM
                =<< make_all_tables' err_msg
                =<< triggerM es'
            T.sequence $ make_phase3 <$> p2 <.> exprs
        expressions = run_phase 
            [ assignment
            , bcmeq_assgn
            , bcmsuch_assgn
            , bcmin_assgn
            , guard_decl
            , guard_removal
            , coarse_removal
            , fine_removal
            , default_schedule_decl
            , fine_sch_decl
            , coarse_sch_decl
            , initialization
            , assumption
            , invariant
            , mch_theorem
            , transient_prop
            , transientB_prop
            , constraint_prop
            , progress_prop
            , safetyA_prop
            , safetyB_prop
            , remove_assgn
            , remove_init
            , init_witness_decl
            , witness_decl ]

old :: Scope s => Map a s -> Map a s
old = M.mapMaybe is_inherited

new :: Scope s => Map a s -> Map a s
new = M.mapMaybe is_local

make_phase3 :: MachineP2 -> Map Label ExprScope -> MM MachineP3
make_phase3 p2 exprs = do
        tell errs
        unless (L.null errs) $ fail ""
        return p3''
    where
        p3 =  over pContext makeTheoryP3
            $ over pEvents (M.map makeEventP3) 
              (makeMachineP3' p2)
        (p3',errs) = parseExprScope exprs p3
        skip = M.fromList [ (v,Word (prime v) `zeq` Word v) | v <- M.elems $ view newDelVars p3']
        p3'' = over pEvents (M.map $ over eWitness (`M.union` skip)) p3'

run_phase4_proofs :: Pipeline MM (Hierarchy MachineId,MTable MachineP3) (MTable MachineP4)
run_phase4_proofs = proc (r_ord,p3) -> do
        refs   <- run_phase 
            [ ref_replace_csched
            , ref_replace_fsched ] -< p3
        ref_p  <- refine_prog_prop -< p3
        comm   <- all_comments -< p3
        prfs   <- all_proofs   -< p3
        let c_evt_refs :: Maybe (MTable (Map EventId [((Label,ScheduleChange),LineInfo)]))
            c_evt_refs = M.map (M.fromListWith (++)) 
                     <$> M.unionsWith (++) 
                     <$> L.map (M.map coarseRef) <$> refs 
            f_evt_refs' :: Maybe (MTable (Map EventId [((ProgId,ProgressProp),LineInfo)]))
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
        let _ = c_evt_refs :: MTable (Map EventId [((Label,ScheduleChange),LineInfo)])
            _ = f_evt_refs :: MTable (Map EventId (Maybe ((ProgId,ProgressProp),LineInfo)))
            _ = prog_ref :: MTable (Map ProgId ((Rule,[(ProgId,ProgId)]),LineInfo))
            evt_ref_props :: MTable (Map EventId [(ProgId,LineInfo)])
            evt_ref_props = M.unionWith (M.unionWith (++)) 
                        (M.map (M.map $ L.map $ first $ hyps_label . snd) c_evt_refs) 
                        (M.map (M.map $ L.map (first fst) . MM.maybeToList) f_evt_refs)
            evt_live :: MTable (EventId <-> ProgId)
            evt_live  = M.map R.fromListMap $ M.map (M.map $ L.map fst) evt_ref_props
            live_evt :: MTable (ProgId <-> EventId)
            live_evt  = M.map (R.fromListMap . M.map (supporting_evts . fst . fst)) prog_ref
                -- 
            evt_evt :: MTable (Map EventId EventId)
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
        returnA -< p4
    where
        refClash   = format "Multiple refinement of progress property {0}"
        commClash  = format "Multiple comments for {0}"
        proofClash = format "Multiple proofs labeled {0}"
        only_one _ []   = return Nothing
        only_one _ [x]  = return (Just x)
        only_one eid xs = tell [MLError (format "Multiple refinement provided for the fine schedule of {0}" eid) 
                                    $ L.map (first $ show . fst) xs] >> return Nothing


type LiveEvtId = Either EventId ProgId

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
    , evt_evt   :: Map EventId EventId
    , live_info :: Map ProgId (MachineId,LineInfo)
    , evt_info  :: Map (EventId,ProgId) (MachineId,LineInfo)
    } 


make_phase4 :: MachineP3 
            -> Map EventId [((Label, ScheduleChange), LineInfo)]
            -> Map EventId (Maybe ((ProgId,ProgressProp),LineInfo))
            -> Map ProgId ((Rule,[(ProgId,ProgId)]),LineInfo) 
            -> Map DocItem (String,LineInfo)
            -> Map Label (Tactic Proof, LineInfo) 
            -> MachineP4
make_phase4 p3 coarse_refs fine_refs prog_ref comments proofs 
        = MachineP4 { .. }
    where
        _e3 = EventP4 <$> (p3 ^. pEvents) 
                      <.> _pCoarseRef `M.union` evtEmpty
                      <.> _pFineRef `M.union` evtEmpty
                       -- <.> old_sch' `M.union` evtEmpty
        evtEmpty :: Default a => Map EventId a
        evtEmpty = M.map (const def) (p3 ^. pEvents)
        _p3 = p3 & pEvents .~ _e3
        _pProofs = proofs
        _pCoarseRef = M.map (L.map fst) coarse_refs
        _pFineRef =  M.map (fmap fst) fine_refs
        _pLiveRule = M.map (fst . fst) prog_ref
        _pComments = M.map fst comments

make_machine :: MachineId -> MachineP4
             -> MM Machine
make_machine (MId m) p4 = mch'
    where
        types   = p4 ^. pTypes
        -- evtSet  = p4 ^. pEvents
        imp_th  = p4 ^. pImports
        ref_prog :: Map Label Rule
        ref_prog = M.mapKeys as_label $ p4 ^. pLiveRule
        proofs   = p4 ^. pProofs
        -- _ = evt_refs :: Map EventId [(Label,ScheduleChange,LineInfo)]
        ab_var = p4 ^. pAbstractVars
        ctx = empty_theory 
            { extends  = imp_th
            , types    = types
            , funs = M.empty
            , defs = p4 ^. pDefinitions
            , consts   = p4 ^. pConstants
            , theorems = M.empty
            , thm_depend = []
            , dummies  = p4 ^. pDummyVars
            -- , notation =  empty_notation
            , fact = p4 ^. pAssumptions }
        props = p4 ^. pNewPropSet
        mch = Mch 
            { _name  = label m
            , theory = ctx
            , variables = p4 ^. pStateVars
            , abs_vars = ab_var
            , del_vars = M.map fst $ p4 ^. pDelVars
            , init_witness = p4 ^. pInitWitness
            , del_inits = p4 ^. pDelInits
            , inits = p4 ^. pInit
            , props = props 
            , derivation = (ref_prog 
                    `union` M.map (const $ Rule Add) (_progress props)) 
            , inh_props = p4 ^. pOldPropSet
            , comments = p4 ^. pComments
            , events = M.mapKeys as_label evts 
                -- adep: in a abstract machine, prog_a <- evt_a
                -- live: in a concrete machine, prog_c <- prog_c
                -- cdep:                        prog_c <- evt_c
                -- eref: in a refinement, evt_a <- evt_c
                -- pref_a:                evt_a <- prog_a
                -- pref_c:                evt_a <- prog_c
                --   adep;eref \/ (live\/id);cdep
                --   (adep;pref_a)+ /\ id ⊆ {}

                -- = (live;adep \/ adep) ; eref \/ cdep
            -- , prog_evt = _ 
            } -- R.mapDomain getConcrete cdep' }

        pos = raw_machine_pos mch
        po_err = proofs `difference` pos
        mch' = do
            all_errors $ flip map (toList po_err) $ \(lbl,(_,li)) -> 
                Left [Error (format "proof obligation does not exist: {0}" lbl) li]
            xs <- all_errors $ flip map (toList proofs) $ \(k,(tac,li)) -> do
                p <- runTactic li (pos ! k) tac
                return (k,p)
            xs <- triggerM xs
            return mch 
                { AST.props = (AST.props mch) 
                    { _proofs = fromList xs } }
        events = p4 ^. pEvents
        evts = M.map g events 
        g :: EventP4 -> Event
        g evt
            = Event
                { indices = evt ^. eIndices
                , params  = evt ^. eParams
                , new_guard = evt ^. eNewGuards
                , witness = evt ^. eWitness
                , old_guard = evt ^. eOldGuards
                , actions = evt ^. eNewActions
                , del_acts = evt ^. eDelActions
                , eql_vars = keep' ab_var (evt ^. eOldActions)
                             `M.intersection` frame (evt ^. eNewActions)
                , old_sched = Schedule 
                                    { coarse = evt ^. eOldCoarseSched
                                    , fine   = evt ^. eOldFineSched }
                , new_sched = Schedule 
                                    { coarse = evt ^. eNewCoarseSched
                                    , fine   = evt ^. eNewFineSched }
                , c_sched_ref = map snd (evt ^. eCoarseRef)
                , f_sched_ref = (first as_label) <$> evt ^. eFineRef
                , old_acts = M.map (const ()) $ evt ^. eOldActions
                }

uncurryMap :: (Ord a,Ord b) => Map a (Map b c) -> Map (a,b) c
uncurryMap m = fromList $ do
        (x,ys) <- toList m
        (y,z)  <- toList ys
        return ((x,y),z)

flipMap :: (Ord a, Ord b) => Map a (Map b c) -> Map b (Map a c)
flipMap m = M.map fromList $ fromListWith (++) $ do
    (x,xs) <- toList $ M.map toList m
    (y,z)  <- xs
    return (y,[(x,z)])

-- type MM = R.ReaderT Input M

liftP :: (a -> MM b) 
      -> Pipeline MM a b
liftP = Pipeline empty_spec empty_spec

liftP' :: (a -> MM (Maybe b)) 
       -> Pipeline MM (Maybe a) (Maybe b)
liftP' f = Pipeline empty_spec empty_spec 
        $ maybe (return Nothing) f

class Ord k => WithMap k a m where
    type ElementOf k a m :: *
    -- type FunOf k a m :: *
    for_each :: Map k (ElementOf k a m) -> Map k a -> m

instance Ord k => WithMap k a (Map k b) where
    type ElementOf k a (Map k b) = a -> b
    -- type FunOf k a (Map k b) = Map k a
    for_each f m = M.intersectionWith id f m

instance (Monoid b, WithMap k b m) => WithMap k a (Map k b -> m) where
    type ElementOf k a (Map k b -> m) = a -> ElementOf k b m
    -- type FunOf k a (Map k b -> m) = Map k a -> FunOf k b m
    for_each f m0 m1 = M.intersectionWith id f m0 `for_each` (m1 `union` M.map (const mempty) m0)




defToVar :: Def -> Maybe Var
defToVar (Def _ n [] t _) = Just (Var n t)
defToVar (Def _ _ (_:_) _ _) = Nothing




-- trigger_errors 

type family ElementMap a :: *
type instance ElementMap (Map k ()) = ()
type instance ElementMap (Map k (x :+: xs) ) = Map k x :+: ElementMap (Map k xs)

-- type family MapOf a :: *
-- type instance MapOf [(a,b,LineInfo)] = Either [Error] (Map a b)


class ElementLists a where
    split_tables' :: Map k a -> ElementMap (Map k a)

instance ElementLists () where
    split_tables' _ = ()

instance ElementLists as => ElementLists (a:+:as) where
    split_tables' m = M.map f m :+: split_tables' (M.map g m)
        where
            f (x :+: _) = x
            g (_ :+: xs) = xs

type MPipeline ph a = Pipeline MM (MTable ph) (Maybe (MTable a))

instance IsVarScope TheoryDef where
    processDecl xs = do
        let xs' = M.fromList $ L.map (second thDef) xs
        pDefinitions %= M.union xs'

set_decl :: MPipeline MachineP0 
            ( [(String,Sort,LineInfo)]
            , [(String,PostponedDef)] )
set_decl = machineCmd "\\newset" $ \(One (String tag)) _m _ -> do
            let name     = tag 
                new_sort = Sort tag (z3_escape name) 0
                new_type = Gen $ USER_DEFINED new_sort []
                new_def = Def [] (z3_escape name) [] (set_type new_type)
                                    $ zlift (set_type new_type) ztrue
            li <- lift ask
            return ([(tag,new_sort,li)],[(tag,(new_def,Local,li))])

event_decl :: MPipeline MachineP0 [(Label, EventId, LineInfo)]
event_decl = machineCmd "\\newevent" $ \(One evt) _m _ -> do 
            li <- lift ask 
            return [(evt,EventId evt,li)]

refines_mch :: MPipeline MachineP0 [((), MachineId, LineInfo)]
refines_mch = machineCmd "\\refines" $ \(One amch) cmch (MachineP0 ms _) -> do
            li <- lift ask
            unless (amch `M.member` ms) 
                $ left [Error (format "Machine {0} refines a non-existant machine: {1}" cmch amch) li]
                -- check that mch is a machine
            return [((),amch,li)]


import_theory :: MPipeline MachineP0 [(String, Theory, LineInfo)]
import_theory = machineCmd "\\with" $ \(One (String th_name)) _m _ -> do
        let th = [ ("sets"       , set_theory)
                 , ("functions"  , function_theory)
                 , ("arithmetic" , arithmetic)
                 , ("predcalc"   , pred_calc)
                 , ("intervals"  , interval_theory) ]
            msg = "Undefined theory: {0} "
                -- add suggestions
        li <- lift ask
        case th_name `L.lookup` th of
            Nothing -> left [Error (format msg th_name) li]
            Just th -> return [(th_name,th,li)]


variable_decl :: MPipeline MachineP1
                    [(String,VarScope)]
variable_decl = machine_var_decl Machine "\\variable"

instance IsVarScope TheoryConst where
    processDecl xs = do
        let xs' = M.fromList $ L.map (second thCons) xs
        pConstants %= M.union xs'

constant_decl :: MPipeline MachineP1
                    [(String,VarScope)]
constant_decl = machine_var_decl TheoryConst "\\constant"

instance IsVarScope MachineVar where
    processDecl xs = do
        let f :: (String,MachineVar) 
              -> Either Error ( [(String,(Var,LineInfo))]
                              , [(String,Var)]
                              , [(String,Var)])
            f (n,Machine v Local _) = Right ([],[],[(n,v)])
            f (n,Machine v Inherited _) = Right ([],[(n,v)],[(n,v)])
            f (n,DelMch (Just v) Local li) = Right ([(n,(v,li))],[(n,v)],[])
            f (n,DelMch (Just v) Inherited li) = Right ([(n,(v,li))],[],[])
            f (n,DelMch Nothing _ li) = Left $ Error (format "deleted variable '{0}' does not exist" n) li
            ys = map f xs
            (del,abst,st) = (_1 `over` M.fromList)
                            $ (both `over` M.fromList) 
                            $ mconcat $ rights ys
            zs = lefts ys
        tell zs
        pAbstractVars %= M.union abst
        pDelVars   %= M.union del
        pStateVars %= M.union st


remove_var :: MPipeline MachineP1 [(String,VarScope)]
remove_var = machineCmd "\\removevar" $ \(One xs) _m _p1 -> do
        li <- lift ask
        return $ map ((\x -> (x,VarScope $ DelMch Nothing Local li)) . toString) xs

dummy_decl :: MPipeline MachineP1
                    [(String,VarScope)]
dummy_decl = machine_var_decl 
        (\v source li -> Evt $ singleton Nothing (v,Param,source,li)) 
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

instance IsVarScope EvtDecl where
    processDecl xs = do
        let f (n,Evt m) = mconcat $ M.elems $ M.mapWithKey (g n) m
            g :: String -> Maybe EventId 
              -> (Var,EvtScope,DeclSource,LineInfo)
              -> ([EventSym],[EventSym],[(String,Var)])
            g n (Just eid) (v,Index,_,_) = ([(eid,[(n,v)])],[],[])  
            g n (Just eid) (v,Param,_,_) = ([],[(eid,[(n,v)])],[])  
            g n Nothing (v,_,_,_) = ([],[],[(n,v)])
            (is,ps,ds) = 
                      _1 `over` (M.map M.fromList . M.fromListWith (++)) 
                    $ _2 `over` (M.map M.fromList . M.fromListWith (++)) 
                    $ _3 `over` M.fromList
                    $ mconcat $ map f xs
        pIndices %= M.unionWith M.union is
        pParams  %= M.unionWith M.union ps
        pDummyVars %= M.union ds

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
            return $ map (\(n,v) -> ((n,VarScope $ Evt $ M.singleton (Just evt) (v,escope,Local,li)))) vs

    -- Todo: detect when the same variable is declared twice
    -- in the same declaration block.
                        
tr_hint :: MachineP2
        -> MachineId
        -> Map String Var
        -> NonEmpty Label
        -> [LatexDoc]
        -> M TrHint
tr_hint p2 m vs lbls thint = do
    tr@(TrHint wit _)  <- toEither $ tr_hint' p2 m vs lbls thint empty_hint
    evs <- get_events p2 $ NE.toList lbls
    let vs = map (view pIndices p2 !) evs
        err e ind = ( not $ M.null diff
                    , format "A witness is needed for {0} in event '{1}'" 
                        (intercalate "," $ keys diff) e)
            where
                diff = ind `M.difference` wit
    toEither $ error_list 
        $ zipWith err evs vs
    return tr

tr_hint' :: MachineP2
         -> MachineId
         -> Map String Var
         -> NonEmpty Label
         -> [LatexDoc]
         -> TrHint
         -> RWS LineInfo [Error] () TrHint
tr_hint' p2 _m fv lbls = visit_doc []
        [ ( "\\index"
          , CmdBlock $ \(String x, texExpr) (TrHint ys z) -> do
                evs <- get_events p2 $ NE.toList lbls
                let inds = event_indices p2
                vs <- bind_all evs 
                    (format "'{0}' is not an index of '{1}'" x) 
                    (\e -> x `M.lookup` (inds ! e))
                let Var _ t = head vs
                    ind = prime $ Var x t
                    x'  = x ++ "'"
                expr <- hoistEither $ parse_expr' 
                    (machine_parser p2 `with_vars` insert x' ind fv) 
                        -- { expected_type = Just t }
                    texExpr
                return $ TrHint (insert x (t, expr) ys) z)
        , ( "\\lt"
          , CmdBlock $ \(One prog) (TrHint ys z) -> do
                let msg = "Only one progress property needed for '{0}'"
                toEither $ error_list 
                    [ ( not $ MM.isNothing z
                      , format msg lbls )
                    ]
                return $ TrHint ys (Just prog))
        ]


check_types :: Either [String] a -> EitherT [Error] (RWS LineInfo [Error] ()) a    
check_types c = EitherT $ do
    li <- ask
    return $ either (\xs -> Left $ map (`Error` li) xs) Right c

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

get_notation :: HasTheoryP2 phase => phase -> Notation
get_notation p2 = L.view pNotation p2

machine_events :: HasMachineP1 phase events => phase events thy -> Map Label EventId
machine_events p2 = L.view pEventIds p2

get_event :: HasMachineP1 phase events => phase events thy -> Label -> M EventId
get_event p2 ev_lbl = do
        let evts = machine_events p2
        bind
            (format "event '{0}' is undeclared" ev_lbl)
            $ ev_lbl `M.lookup` evts

get_events :: MachineP2 -> [Label] -> M [EventId]
get_events p2 ev_lbl = do
            let evts = machine_events p2
            bind_all ev_lbl
                (format "event '{0}' is undeclared")
                $ (`M.lookup` evts)


get_guards :: MachineP3 -> EventId -> M (Map Label Expr)
get_guards p3 evt = 
        return $ (p3 ^. pNewGuards) ! evt

get_invariants :: MachineP3 -> Map Label Expr
get_invariants p3 = (p3 ^. pInvariant)

progress_props :: MachineP3 -> Map ProgId ProgressProp
progress_props p3 = p3 ^. pProgress

event_parser :: HasMachineP2 phase events => phase events thy -> EventId -> ParserSetting
event_parser p2 ev = (p2 ^. pEvtSynt) ! ev

schedule_parser :: HasMachineP2 phase events => phase events thy -> EventId -> ParserSetting
schedule_parser p2 ev = (p2 ^. pSchSynt) ! ev

machine_parser :: HasMachineP2 phase events => phase events thy -> ParserSetting
machine_parser p2 = L.view pMchSynt p2

context_parser :: HasTheoryP2 phase => phase -> ParserSetting
context_parser p2 = p2 ^. pCtxSynt

state_variables :: HasMachineP2' phase => phase events thy -> Map String Var
state_variables p2 = p2 ^. pStateVars

abstract_variables :: HasMachineP2' phase => phase events thy -> Map String Var
abstract_variables p2 = p2 ^. pAbstractVars

dummy_vars :: HasTheoryP2 phase => phase -> Map String Var
dummy_vars p2 = p2 ^. pDummyVars

event_indices :: HasMachineP2 phase events => phase events thy -> Map EventId (Map String Var)
event_indices p2 = p2 ^. pIndices

free_vars' :: Map String Var -> Expr -> Map String Var
free_vars' ds e = vs `M.intersection` ds
    where
        vs = symbol_table $ S.elems $ used_var e

assignment :: MPipeline MachineP2
                    [(Label,ExprScope)]
assignment = machineCmd "\\evassignment" $ \(ev_lbl, lbl, xs) _m p2 -> do
            ev <- get_event p2 ev_lbl
            pred <- hoistEither $ parse_expr' 
                (event_parser p2 ev) 
                { is_step = True } 
                xs
            let frame = M.elems $ (state_variables p2) `M.difference` (abstract_variables p2) :: [Var] 
                act = BcmSuchThat frame pred
            li <- lift ask
            return [(lbl,ExprScope $ EventExpr $ M.singleton (Just ev) $ (EvtExprScope $ Action (InhAdd act) Local li))]

bcmeq_assgn :: MPipeline MachineP2
                    [(Label,ExprScope)]
bcmeq_assgn = machineCmd "\\evbcmeq" $ \(ev_lbl, lbl, String v, xs) _m p2 -> do
            let _ = lbl :: Label
            ev <- get_event p2 ev_lbl
            var@(Var _ t) <- bind
                (format "variable '{0}' undeclared" v)
                $ v `M.lookup` (state_variables p2)
            li <- lift ask
            xp <- hoistEither $ parse_expr' 
                (event_parser p2 ev) 
                { expected_type = Just t } 
                xs
            check_types
                $ Right (Word var :: Expr) `mzeq` Right xp
            let act = Assign var xp
            return [(lbl,ExprScope $ EventExpr $ M.singleton (Just ev) $ (EvtExprScope $ Action (InhAdd act) Local li))]

bcmsuch_assgn :: MPipeline MachineP2
                    [(Label,ExprScope)]
bcmsuch_assgn = machineCmd "\\evbcmsuch" $ \(evt, lbl, vs, xs) _m p2 -> do
            ev <- get_event p2 evt
            li <- lift ask
            xp  <- hoistEither $ parse_expr' (event_parser p2 ev)
                    { is_step = True } 
                    xs
            vars <- bind_all (map toString vs)
                (format "variable '{0}' undeclared")
                $ (`M.lookup` state_variables p2)
            let act = BcmSuchThat vars xp
            return [(lbl,ExprScope $ EventExpr $ M.singleton (Just ev) $ (EvtExprScope $ Action (InhAdd act) Local li))]

bcmin_assgn :: MPipeline MachineP2
                    [(Label,ExprScope)]
bcmin_assgn = machineCmd "\\evbcmin" $ \(evt, lbl, String v, xs) _m p2 -> do
            ev <- get_event p2 evt
            var@(Var _ t) <- bind
                (format "variable '{0}' undeclared" v)
                $ v `M.lookup` (state_variables p2)
            li  <- lift ask
            xp  <- hoistEither $ parse_expr' (event_parser p2 ev)
                    { expected_type = Just (set_type t) } 
                    xs
            let act = BcmIn var xp
            check_types $ Right (Word var) `zelem` Right xp
            return [(lbl,ExprScope $ EventExpr $ M.singleton (Just ev) $ (EvtExprScope $ Action (InhAdd act) Local li))]

instance Scope Initially where
    clashes (DelInit _ _ _) (Initially _ _ _) = False
    clashes (Initially _ _ _) (DelInit _ _ _) = False
    clashes _ _ = True
    error_item (Initially _ _ li) = ("initialization", li)
    error_item (DelInit _ _ li) = ("delete initialization", li)
    keep_from s x = guard (s == f x) >> return x
        where
            f (Initially _ s _) = s
            f (DelInit _ _ _) = Inherited
    merge_scopes (DelInit _ s li) (Initially e _ _) = DelInit (Just e) s li
    merge_scopes (Initially e _ _) (DelInit _ s li) = DelInit (Just e) s li
    merge_scopes _ _ = error "Initially Scope.merge_scopes: _, _"

used_var' :: Expr -> Map String Var
used_var' = symbol_table . S.toList . used_var

instance IsExprScope Initially where
    parseExpr xs = do
        xs <- forM xs $ \(lbl,x) -> do
            case x of
                Initially x _ li -> do
                    vs <- gets $ view pDelVars
                    let msg = format "initialization predicate '{0}' refers to deleted variables" lbl
                        lis = L.map (first name) $ M.elems $ vs `M.intersection` used_var' x
                        lis' = L.map (first (format "deleted variable {0}")) lis
                    unless (L.null lis')
                        $ tell [MLError msg $ (format "predicate {0}" lbl,li):lis']
                    return ([(lbl,x)],[],[])
                DelInit (Just x) Local _ -> 
                    return ([],[(lbl,x)],[(v,x) | v <- S.elems $ used_var x ])
                DelInit (Just _) Inherited _ -> 
                    return ([],[],[])
                DelInit Nothing _ li -> do
                    let msg = format "initialization predicate '{0}' was deleted but does not exist" lbl
                    tell [Error msg li]
                    return ([],[],[])
        let (ys,zs,ws) = mconcat xs 
        pInit     %= M.union (M.fromList ys)
        pDelInits %= M.union (M.fromList zs)
        pInitWitness %= flip M.union (M.fromList ws)

remove_init :: MPipeline MachineP2 [(Label,ExprScope)]
remove_init = machineCmd "\\removeinit" $ \(One lbls) _m _p2 -> do
            li <- lift ask
            return [(lbl,ExprScope $ DelInit Nothing Local li) | lbl <- lbls ]

remove_assgn :: MPipeline MachineP2 [(Label,ExprScope)]
remove_assgn = machineCmd "\\removeact" $ \(evt, lbls) _m p2 -> do
            ev <- get_event p2 evt
            li <- lift ask
            return [(lbl,ExprScope $ EventExpr $ M.singleton (Just ev) $ (EvtExprScope $ Action (InhDelete Nothing) Local li)) | lbl <- lbls ]

witness_decl :: MPipeline MachineP2 [(Label,ExprScope)]
witness_decl = machineCmd "\\witness" $ \(evt, String var, xp) _m p2 -> do
            ev <- get_event p2 evt
            li <- lift ask
            p  <- hoistEither $ parse_expr' (event_parser p2 ev) { is_step = True } xp
            v  <- bind (format "'{0}' is not a disappearing variable" var)
                (var `M.lookup` (L.view pAbstractVars p2 `M.difference` L.view pStateVars p2))
            return [(label var,ExprScope $ EventExpr $ M.singleton (Just ev) (EvtExprScope $ Witness v p Local li))]

instance Scope EventExpr where
    keep_from s (EventExpr m) = Just $ EventExpr $ M.mapMaybe (keep_from s) m
    make_inherited (EventExpr m) = Just $ EventExpr (M.map f m)
        where
            f x = set declSource Inherited x
    clashes (EventExpr m0) (EventExpr m1) = not $ M.null 
            $ M.filter id
            $ M.intersectionWith clashes m0 m1
    error_item (EventExpr m) = head' $ elems $ mapWithKey msg m
        where
            head' [x] = x
            head' _ = error "Scope ExprScope: head'"
            msg (Just k) sc = (format "{1} (event {0})" k sc :: String, view lineInfo sc)
            msg Nothing sc = (format "{0} (initialization)" sc :: String, view lineInfo sc)
    merge_scopes (EventExpr m0) (EventExpr m1) = EventExpr $ unionWith merge_scopes m0 m1

checkLocalExpr :: ( HasInhStatus decl (InhStatus expr)
                  , HasLineInfo decl LineInfo )
               => String -> (expr -> Map String Var)
               -> [(Maybe EventId, [(Label,decl)])] 
               -> RWS () [Error] MachineP3 ()
checkLocalExpr expKind free xs = do
        vs <- use pDelVars
        let xs' = [ (eid,lbl,sch) | (e,ss) <- xs, (lbl,sch) <- ss, eid <- MM.maybeToList e ]
        forM_ xs' $ \(eid,lbl,sch) -> do
            case (sch ^. inhStatus) of
                InhAdd expr -> do
                    let msg = format "event '{1}', {2} '{0}' refers to deleted variables" lbl eid expKind
                        errs   = vs `M.intersection` free expr
                        schLI  = (format "{1} '{0}'" lbl expKind, sch ^. lineInfo)
                        varsLI = L.map (first $ format "deleted variable '{0}'" . name) (M.elems errs)
                    unless (M.null errs) 
                        $ tell [MLError msg $ schLI : varsLI]
                InhDelete Nothing -> do
                    let msg = format "event '{1}', {2} '{0}' was deleted but does not exist" lbl eid expKind
                        li  = sch ^. lineInfo
                    tell [Error msg li]
                _ -> return ()

instance IsEvtExpr CoarseSchedule where
    parseEvtExpr xs = do
        parseEvtExprChoice' pOldCoarseSched pDelCoarseSched pNewCoarseSched fst xs
        checkLocalExpr "coarse schedule" used_var' xs

instance IsEvtExpr FineSchedule where
    parseEvtExpr xs = do
        parseEvtExprChoice' pOldFineSched pDelFineSched pNewFineSched fst xs
        checkLocalExpr "fine schedule" used_var' xs

instance IsEvtExpr Guard where
    parseEvtExpr xs = do
        parseEvtExprChoice' pOldGuards pDelGuards pNewGuards fst xs
        checkLocalExpr "guard" used_var' xs

type OneOrTwo a = Either (a,a) a

fieldA :: Lens' (OneOrTwo a) a
fieldA f (Left x) = Left <$> _1 f x
fieldA f (Right x) = (Left . (,x)) <$> f x

fieldB :: Lens' (OneOrTwo a) a
fieldB f (Left x) = Left <$> _2 f x
fieldB f (Right x) = (Left . (x,)) <$> f x

parseEvtExprChoice :: ( HasInhStatus decl (InhStatus expr)
                      , HasDeclSource decl DeclSource 
                      , Ord label)
              => Lens' MachineP3 (Map EventId (Map label expr))
              -> Lens' MachineP3 (Map EventId (Map label expr))
              -> ((Label,decl) -> label)
              -> [(Maybe EventId, [(Label, decl)])]
              -> RWS () [Error] MachineP3 ()
parseEvtExprChoice oldLn newLn f = parseEvtExprChoice' oldLn newLn newLn f

parseEvtExprChoice' :: ( HasInhStatus decl (InhStatus expr)
                      , HasDeclSource decl DeclSource 
                      , Ord label)
              => Lens' MachineP3 (Map EventId (Map label expr))
              -> Lens' MachineP3 (Map EventId (Map label expr))
              -> Lens' MachineP3 (Map EventId (Map label expr))
              -> ((Label,decl) -> label)
              -> [(Maybe EventId, [(Label, decl)])]
              -> RWS () [Error] MachineP3 ()
parseEvtExprChoice' oldLn delLn newLn = parseEvtExprChoiceImp 
        (Just (LensT oldLn)) 
        (Just (LensT delLn))
        (Just (LensT newLn))

parseEvtExprChoiceImp :: ( HasInhStatus decl (InhStatus expr)
                      , HasDeclSource decl DeclSource 
                      , Ord label)
              => Maybe (LensT MachineP3 (Map EventId (Map label expr)))
              -> Maybe (LensT MachineP3 (Map EventId (Map label expr)))
              -> Maybe (LensT MachineP3 (Map EventId (Map label expr)))
              -> ((Label,decl) -> label)
              -- -> (decl -> Bool)
              -> [(Maybe EventId, [(Label, decl)])]
              -> RWS () [Error] MachineP3 ()
parseEvtExprChoiceImp oldLn delLn newLn f xs = do
    let route (Just k) x@(_,decl) = case (decl ^. inhStatus, decl ^. declSource) of
                                (InhAdd _, Inherited) -> ([(k,[x])],[],[(k,[x])])
                                (InhAdd _, Local)     -> ([],[],[(k,[x])])
                                (InhDelete _, Inherited) -> ([],[],[])
                                (InhDelete _, Local)     -> ([(k,[x])],[(k,[x])],[])
        route Nothing _ = ([],[],[])
        -- is_new _ = True
        (old_xs, del_xs, new_xs) = mconcat $ L.map (uncurry $ \k -> mconcat . map (route k)) xs
        getLabelExpr = runKleisli $ arr f &&& Kleisli (contents . snd)
        g        = L.map (second $ MM.mapMaybe getLabelExpr)
            -- arr (map $ f &&& (view evtExpr . snd)))
        assign ln f = maybe (return ()) (\(LensT ln) -> ln %= f) ln
    oldLn `assign` doubleUnion (g old_xs)
    delLn `assign` doubleUnion (g del_xs)
    newLn `assign` doubleUnion (g new_xs)



doubleUnion :: (Ord k0,Ord k1)
            => [(k0,[(k1,a)])]
            -> Map k0 (Map k1 a)
            -> Map k0 (Map k1 a)
doubleUnion xs = M.unionWith M.union (M.map M.fromList $ M.fromListWith (++) xs)


parseEvtExprDefault :: (HasEvtExpr decl expr, Ord label)
              => Lens' MachineP3 (Map EventId (Map label expr))
              -> ((Label,decl) -> label)
              -> [(Maybe EventId, [(Label, decl)])]
              -> RWS () [Error] MachineP3 ()
parseEvtExprDefault ln f xs = do
    let toEntry = f &&& (view evtExpr . snd)
        xs'  = MM.mapMaybe (runKleisli $ Kleisli id *** arr (map toEntry)) xs
        xs'' = M.map M.fromList $ M.fromListWith (++) xs'
    ln %= flip (M.unionWith M.union) xs''

parseInitExpr :: (HasEvtExpr decl expr, Ord label)
              => Lens' MachineP3 (Map label expr)
              -> ((Label,decl) -> label)
              -> [(Maybe EventId, [(Label, decl)])]
              -> RWS () [Error] MachineP3 ()
parseInitExpr ln f xs = do

    let toEntry = f &&& (view evtExpr . snd)
        ys' = concat $ MM.mapMaybe (\(x,y) -> guard (MM.isNothing x) >> return (map toEntry y)) xs
    ln %= M.union (M.fromList ys')

mapA :: Monad m => Kleisli m b c -> Kleisli m [b] [c]
mapA (Kleisli m) = Kleisli $ mapM m

instance IsEvtExpr Witness where
    parseEvtExpr xs = do
        let toExpr = (_witnessVar &&& view evtExpr) . snd
            -- isLocal x = x ^. declSource == Local
            getLocalExpr = mapA (second $ Kleisli $ is_local) >>> arr (map toExpr)
            withEvent    = Kleisli id
            withoutEvent = Kleisli $ guard . MM.isNothing
            xs' = MM.mapMaybe (runKleisli $ withEvent *** getLocalExpr) xs
            ys' = MM.mapMaybe (runKleisli $ withoutEvent *** getLocalExpr >>> arr snd) xs
        pWitness %= doubleUnion xs'
        pInitWitness %= M.union (M.fromList $ concat ys')

instance IsEvtExpr ActionDecl where
    parseEvtExpr xs = do
            parseEvtExprChoice' pOldActions pDelActions pNewActions fst xs
            vs <- gets $ view pDelVars
            let xs' = map (uncurry $ \k -> (k,) . concat . MM.mapMaybe (g k)) xs
                g (Just _) (lbl,Action (InhDelete (Just act)) Local _) = do
                        let f = frame' act `M.intersection` vs
                            ns = [ (lbl,Witness v (ba_pred act) Local undefined) | v <- M.elems f ]
                        return ns
                g _ _ = Nothing
            parseEvtExprDefault pWitness (_witnessVar . snd) xs'
            checkLocalExpr "action" 
                (uncurry M.union . (frame' &&& used_var' . ba_pred)) 
                xs

instance IsExprScope EventExpr where
    parseExpr xs = mapM_ (readEvtExprGroup parseEvtExpr) zs
        where
            ys = concatMap g xs
            zs = groupEvtExprGroup (++) ys
            g (lbl,EventExpr m) = M.elems $ M.mapWithKey (\eid -> readEvtExprScope $ \e -> EvtExprGroup [(eid,[(lbl,e)])]) m

init_witness_decl :: MPipeline MachineP2 [(Label,ExprScope)]
init_witness_decl = machineCmd "\\initwitness" $ \(String var, xp) _m p2 -> do
            -- ev <- get_event p2 evt
            li <- lift ask
            p  <- hoistEither $ parse_expr' (machine_parser p2) xp
            v  <- bind (format "'{0}' is not a disappearing variable" var)
                (var `M.lookup` (L.view pAbstractVars p2 `M.difference` L.view pStateVars p2))
            return [(label var, ExprScope $ EventExpr $ M.singleton Nothing (EvtExprScope $ Witness v p Local li))]

guard_decl :: MPipeline MachineP2
                    [(Label,ExprScope)]
guard_decl = machineCmd "\\evguard" $ \(evt, lbl, xs) _m p2 -> do
            ev <- get_event p2 evt
            li <- lift ask
            xp <- hoistEither $ parse_expr' (event_parser p2 ev) xs
            return [(lbl,ExprScope $ EventExpr $ M.singleton (Just ev) $ (EvtExprScope $ Guard (InhAdd xp) Local li))]

guard_removal :: MPipeline MachineP2 [(Label,ExprScope)]
guard_removal = machineCmd "\\removeguard" $ \(evt_lbl,lbls) _m p2 -> do
        ev  <- get_event p2 evt_lbl
        li <- lift ask
        return [(lbl,ExprScope $ EventExpr $ M.singleton (Just ev) $ (EvtExprScope $ Guard (InhDelete Nothing) Local li)) | lbl <- lbls ]

coarse_removal :: MPipeline MachineP2 [(Label,ExprScope)]
coarse_removal = machineCmd "\\removecoarse" $ \(evt_lbl,lbls) _m p2 -> do
        ev  <- get_event p2 evt_lbl
        li <- lift ask
        return [(lbl,ExprScope $ EventExpr $ M.singleton (Just ev) $ (EvtExprScope $ CoarseSchedule (InhDelete Nothing) Local li)) | lbl <- lbls ]

fine_removal :: MPipeline MachineP2 [(Label,ExprScope)]
fine_removal = machineCmd "\\removefine" $ \(evt_lbl,lbls) _m p2 -> do
        ev  <- get_event p2 evt_lbl
        li <- lift ask
        return [(lbl,ExprScope $ EventExpr $ M.singleton (Just ev) $ (EvtExprScope $ FineSchedule (InhDelete Nothing) Local li)) | lbl <- lbls ]

coarse_sch_decl :: MPipeline MachineP2
                    [(Label,ExprScope)]
coarse_sch_decl = machineCmd "\\cschedule" $ \(evt, lbl, xs) _m p2 -> do
            ev <- get_event p2 evt
            li <- lift ask
            xp <- hoistEither $ parse_expr' (schedule_parser p2 ev) xs
            return [(lbl,ExprScope $ EventExpr $ M.singleton (Just ev) $ (EvtExprScope $ CoarseSchedule (InhAdd xp) Local li))]

fine_sch_decl :: MPipeline MachineP2
                    [(Label,ExprScope)]
fine_sch_decl = machineCmd "\\fschedule" $ \(evt, lbl, xs) _m p2 -> do
            ev <- get_event p2 evt
            li <- lift ask
            xp <- hoistEither $ parse_expr' (schedule_parser p2 ev) xs
            return [(lbl,ExprScope $ EventExpr $ M.singleton (Just ev) $ (EvtExprScope $ FineSchedule (InhAdd xp) Local li))]

        -------------------------
        --  Theory Properties  --
        -------------------------

instance Scope Axiom where
    merge_scopes _ _ = error "Axiom Scope.merge_scopes: _, _"
    clashes _ _ = True
    keep_from s x = guard (s == f x) >> return x
        where
            f (Axiom _ s _) = s
    error_item (Axiom _ _ li) = ("assumtion", li)

parseExpr' :: (HasMchExpr b a, Ord label)
           => Lens' MachineP3 (Map label a) 
           -> [(label,b)] 
           -> RWS () [Error] MachineP3 ()
parseExpr' ln xs = modify $ ln %~ M.union (M.fromList $ map (second $ view mchExpr) xs)

instance IsExprScope Axiom where
    parseExpr = parseExpr' pAssumptions

assumption :: MPipeline MachineP2
                    [(Label,ExprScope)]
assumption = machineCmd "\\assumption" $ \(lbl,xs) _m p2 -> do
            li <- lift ask
            xp <- hoistEither $ parse_expr' (context_parser p2) xs
            return [(lbl,ExprScope $ Axiom xp Local li)]

        --------------------------
        --  Program properties  --
        --------------------------

initialization :: MPipeline MachineP2
                    [(Label,ExprScope)]
initialization = machineCmd "\\initialization" $ \(lbl,xs) _m p2 -> do
            li <- lift ask
            xp <- hoistEither $ parse_expr' (machine_parser p2) xs
            return [(lbl,ExprScope $ Initially xp Local li)]


modifyProps :: ( HasMchExpr b a, HasDeclSource b DeclSource
               , Scope b
               , Show a)
            => Lens' PropertySet (Map Label a)
            -> [(Label,b)]
            -> RWS () [Error] MachineP3 ()
modifyProps ln xs = do
    let 
        xs' = L.partition ((== Local) . view declSource . snd) xs
        (ys',zs') = (both `over` L.map (second $ view mchExpr)) xs'
    pNewPropSet.ln %= M.union (M.fromList ys')
    pOldPropSet.ln %= M.union (M.fromList zs')

instance Scope Invariant where
instance IsExprScope Invariant where
    parseExpr xs = do
        parseExpr' pInvariant xs
        modifyProps inv xs

invariant :: MPipeline MachineP2
                    [(Label,ExprScope)]
invariant = machineCmd "\\invariant" $ \(lbl,xs) _m p2 -> do
            li <- lift ask
            xp <- hoistEither $ parse_expr' (machine_parser p2) xs
            return [(lbl,ExprScope $ Invariant xp Local li)]

instance Scope InvTheorem where
instance IsExprScope InvTheorem where
    parseExpr xs = do
        parseExpr' pInvariant xs
        modifyProps inv_thm xs

mch_theorem :: MPipeline MachineP2
                    [(Label,ExprScope)]
mch_theorem = machineCmd "\\theorem" $ \(lbl,xs) _m p2 -> do
            li <- lift ask
            xp <- hoistEither $ parse_expr' (machine_parser p2) xs
            return [(lbl,ExprScope $ InvTheorem xp Local li)]

instance Scope TransientProp where
instance IsExprScope TransientProp where
    parseExpr xs = do
        parseExpr' pTransient xs
        modifyProps transient xs

transient_prop :: MPipeline MachineP2
                    [(Label,ExprScope)]
transient_prop = machineCmd "\\transient" $ \(evts, lbl, xs) _m p2 -> do
            _evs <- get_events p2 evts
            li   <- lift ask
            tr   <- hoistEither $ parse_expr' (machine_parser p2) 
                    { free_dummies = True } xs
            let withInd = L.filter (not . M.null . (^. eIndices) . ((p2 ^. pEvents) !)) _evs
            toEither $ error_list 
                [ ( not $ L.null withInd
                  , format "event(s) {0} have indices and require witnesses" 
                        $ intercalate "," $ map show withInd) ]
            let vs = symbol_table $ S.elems $ used_var tr
                fv = vs `M.intersection` dummy_vars p2
                prop = Transient fv tr evts empty_hint
            return [(lbl,ExprScope $ TransientProp prop Local li)]

transientB_prop :: MPipeline MachineP2
                    [(Label,ExprScope)]
transientB_prop = machineCmd "\\transientB" $ \(evts, lbl, hint, xs) m p2 -> do
            _evs <- get_events p2 evts
            li   <- lift ask
            tr   <- hoistEither $ parse_expr' (machine_parser p2) 
                    { free_dummies = True } xs
            let fv = free_vars' ds tr
                ds = dummy_vars p2
            evts' <- bind "Expecting non-empty list of events"
                    $ NE.nonEmpty evts
            hint  <- tr_hint p2 m fv evts' hint
            let prop = Transient fv tr evts hint
            return [(lbl,ExprScope $ TransientProp prop Local li)]

instance IsExprScope ConstraintProp where
    parseExpr xs = do
        modifyProps constraint xs

instance Scope ConstraintProp where
    merge_scopes _ _ = error "ConstraintProp Scope.merge_scopes: _, _"
    clashes _ _ = True
    keep_from s x = guard (s == s') >> return x
        where
            s' = case x of (ConstraintProp _ s _) -> s
    error_item (ConstraintProp _ _ li) = ("co property", li)

constraint_prop :: MPipeline MachineP2
                    [(Label,ExprScope)]
constraint_prop = machineCmd "\\constraint" $ \(lbl,xs) _m p2 -> do
            li  <- lift ask
            pre <- hoistEither $ parse_expr' (machine_parser p2)
                    { free_dummies = True
                    , is_step = True }
                    xs
            let vars = elems $ free_vars' ds pre
                ds = dummy_vars p2
                prop = Co vars pre
            return [(lbl,ExprScope $ ConstraintProp prop Local li)]

instance IsExprScope SafetyDecl where
    parseExpr xs = do
        parseExpr' pSafety xs
        modifyProps safety xs

instance Scope SafetyDecl where
    merge_scopes _ _ = error "SafetyDecl Scope.merge_scopes: _, _"
    clashes _ _ = True
    keep_from s x = guard (s == s') >> return x
        where
            s' = case x of (SafetyProp _ s _) -> s
    error_item (SafetyProp _ _ li) = ("safety property", li)

safety_prop :: Label -> Maybe Label
            -> LatexDoc'
            -> LatexDoc'
            -> MachineId
            -> MachineP2
            -> M [(Label,ExprScope)]
safety_prop lbl evt pCt qCt _m p2 = do
            li <- lift ask
            (p,q)  <- toEither (do
                _  <- case evt of
                        Just evt -> do
                            liftM Just $ fromEither (error "safetyB") 
                                $ get_event p2 evt
                        Nothing -> return Nothing
                -- _  <- bind
                --     (format "event '{0}' is undeclared" evt)
                --     $ evt `M.lookup` events m
                p <- fromEither ztrue $ hoistEither
                    $ parse_expr' (machine_parser p2) 
                        { free_dummies = True }
                        pCt
                q <- fromEither ztrue $ hoistEither
                    $ parse_expr' (machine_parser p2) 
                        { free_dummies = True } 
                        qCt
                return (p,q))
            let ds  = dummy_vars p2
                dum = free_vars' ds p `union` free_vars' ds q
                new_prop = Unless (M.elems dum) p q evt
            return [(lbl,ExprScope $ SafetyProp new_prop Local li)]

safetyA_prop :: MPipeline MachineP2
                    [(Label,ExprScope)]
safetyA_prop = machineCmd "\\safety" 
                $ \(lbl, pCt, qCt) -> safety_prop lbl Nothing pCt qCt

safetyB_prop :: MPipeline MachineP2
                    [(Label,ExprScope)]
safetyB_prop = machineCmd "\\safetyB" 
                $ \(lbl, evt, pCt, qCt) -> safety_prop lbl evt pCt qCt

instance IsExprScope ProgressDecl where
    parseExpr xs = do
        parseExpr' pProgress $ map (first PId) xs
        modifyProps progress xs

instance Scope ProgressDecl where
    merge_scopes _ _ = error "ProgressProp Scope.merge_scopes: _, _"
    clashes _ _ = True
    keep_from s x = guard (s == s') >> return x
        where
            s' = case x of (ProgressProp _ s _) -> s
    error_item (ProgressProp _ _ li) = ("progress property", li)

progress_prop :: MPipeline MachineP2
                    [(Label,ExprScope)]
progress_prop = machineCmd "\\progress" $ \(lbl, pCt, qCt) _m p2 -> do
            li <- lift ask
            (p,q)    <- toEither (do
                p    <- fromEither ztrue $ hoistEither
                    $ parse_expr' (machine_parser p2) 
                        { free_dummies = True }
                        pCt
                q    <- fromEither ztrue $ hoistEither
                    $ parse_expr' (machine_parser p2) 
                        { free_dummies = True } 
                        qCt
                return (p,q))
            let ds  = dummy_vars p2
                dum = free_vars' ds p `union` free_vars' ds q
                new_prop = LeadsTo (M.elems dum) p q
--             new_deriv <- bind (format "proof step '{0}' already exists" lbl)
--                 $ insert_new lbl (Rule Add) $ derivation $ props m
            return [(lbl,ExprScope $ ProgressProp new_prop Local li)]

refine_prog_prop :: MPipeline MachineP3
                [(ProgId,(Rule,[(ProgId,ProgId)]),LineInfo)]
refine_prog_prop = machineCmd "\\refine" $ \(goal, String rule, hyps, hint) m p3 -> do
        let p2   =  (pContext `over` view t2)
                    $ (pEvents `over` M.map (view e2)) 
                      (p3 ^. machineP2')
            prog = p3 ^. pProgress
            saf  = p3 ^. pSafety
            tr   = p3 ^. pTransient
            parser = p3 ^. pMchSynt
            rule' = map toLower rule
            goal' = PId goal
            dep = zip (repeat goal') (map PId hyps)
        r <- parse_rule' rule'
            (RuleParserDecl p2 m (M.mapKeys as_label prog) saf tr goal hyps hint parser)
        li <- ask
        return [(goal',(r,dep),li)]

data EventRef = EventRef 
        { coarseRef :: [(EventId,[((Label,ScheduleChange),LineInfo)])]
        , fineRef :: [(EventId,[((ProgId,ProgressProp),LineInfo)])] }

instance Monoid EventRef where
    mempty = EventRef [] []
    mappend (EventRef xs0 xs1) (EventRef ys0 ys1) = 
            EventRef (xs0 ++ ys0) (xs1 ++ ys1)


ref_replace_csched :: MPipeline MachineP3 EventRef
ref_replace_csched = machineCmd "\\replace" $ \(evt_lbl,del,add,keep,prog,saf) m p3 -> do
        -- let lbls  = (S.elems $ add `S.union` del `S.union` keep)
        (sprop,pprop,evt) <- toEither $ do
            sprop <- fromEither (error "replace_csched: saf") 
                        $ get_safety_prop p3 m saf
            pprop <- fromEither (error "replace_csched: prog") 
                        $ get_progress_prop p3 m prog
            evt   <- fromEither (error "replace_csched: evt")
                        $ get_event p3 evt_lbl
            return (sprop,pprop,evt)
        toEither $ do
            _ <- fromEither undefined $ bind_all del 
                    (format "'{1}' is not the label of a coarse schedule of '{0}' deleted during refinement" evt) 
                    (`M.lookup` (p3 ^. getEvent evt . eDelCoarseSched))
            _ <- fromEither undefined $ bind_all add 
                    (format "'{1}' is not the label of a coarse schedule of '{0}' added during refinement" evt) 
                    (`M.lookup` (p3 ^. getEvent evt . eAddedCoarseSched))
            _ <- fromEither undefined $ bind_all keep 
                    (format "'{1}' is not the label of a coarse schedule of '{0}' kept during refinement" evt) 
                    (`M.lookup` (p3 ^. getEvent evt . eKeptCoarseSched))
            return ()
        let rule = (replace (as_label prog,pprop) (saf,sprop)) 
                        { remove = fromList' del
                        , add  = fromList' add
                        , keep = fromList' keep }
            po_lbl = composite_label ["SCH",as_label m]            
        li <- lift ask
        return $ EventRef [(evt,[((po_lbl,rule),li)])] []

fromList' :: Ord a => [a] -> Map a ()
fromList' xs = M.fromList $ zip xs $ repeat ()


ref_replace_fsched :: MPipeline MachineP3 EventRef
ref_replace_fsched = machineCmd "\\replacefine" $ \(evt_lbl,prog) m p3 -> do
        evt <- get_event p3 evt_lbl
        pprop <- get_progress_prop p3 m prog
        let rule      = (prog,pprop)
        li <- lift ask
        return $ EventRef [] [(evt,[(rule,li)])]

all_comments :: MPipeline MachineP3 [(DocItem, String, LineInfo)]
all_comments = machineCmd "\\comment" $ \(item',cmt') _m p3 -> do
                li <- lift ask
                let cmt = concatMap flatten cmt'
                    item = L.filter (/= '$') $ remove_ref $ concatMap flatten item'
                    -- prop = props m
                    invs = get_invariants p3
                    is_inv = label item `member` invs
                    progs = progress_props p3
                    is_prog = PId (label item) `member` progs
                    evts = machine_events p3
                    is_event = label item `member` evts
                    vars = state_variables p3
                    is_var = item `member` vars
                    lbl = label item
                    conds = [is_inv,is_prog,is_event,is_var]
                unless (length (L.filter id conds) <= 1)
                    $ fail "all_comments: conditional not mutually exclusive"
                key <- if is_inv then do
                    return $ DocInv lbl
                else if is_prog then do
                    return $ DocProg lbl
                else if is_event then do
                    return $ DocEvent lbl
                else if is_var then do
                    return $ DocVar item
                else do
                    let msg = "`{0}` is not one of: a variable, an event, \
                              \ an invariant or a progress property "
                    unless (not $ or conds)
                        $ fail "all_comments: conditional not exhaustive"
                    left [Error (format msg item) li]
                return [(key,cmt,li)]

all_proofs :: MPipeline MachineP3 [(Label,Tactic Proof,LineInfo)]
all_proofs = machineEnv "proof" $ \(One po) xs m p3 -> do
        li <- lift ask
        let notation = get_notation p3
            po_lbl = label $ remove_ref $ concatMap flatten po
            lbl = composite_label [ as_label m, po_lbl ]
        proof <- mapEitherT 
            (\cmd -> runReaderT cmd notation) 
            $ run_visitor li xs collect_proof_step 
        return [(lbl,proof,li)]







