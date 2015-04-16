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
import Document.Expression hiding ( parse_expr' )
import Document.ExprScope
import Document.Pipeline
import Document.Phase as P
import Document.Proof
import Document.Refinement as Ref
import Document.Scope
import Document.Visitor

import Latex.Parser

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

import           Control.Monad 
import           Control.Monad.Reader.Class 
import           Control.Monad.State.Class 
import           Control.Monad.Writer.Class 
import qualified Control.Monad.Reader as R
import           Control.Monad.Trans
import           Control.Monad.Trans.Either
import           Control.Monad.Trans.Reader ( runReaderT )
import           Control.Monad.Trans.RWS as RWS ( execRWS, RWS, RWST, mapRWST )
import qualified Control.Monad.Writer as W

import Control.Lens as L hiding ((|>),(<.>),(<|),indices,Context)

import           Data.Char
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

import Utilities.Error
import Utilities.Format
import Utilities.Relation (type(<->),(|>),(<|))
import qualified Utilities.Relation as R
import Utilities.Syntactic
import Utilities.Trace ()
        
parse_rule' :: (Monad m)
            => String
            -> RuleParserParameter
            -> EitherT [Error] (RWST LineInfo [Error] System m) Rule
parse_rule' rule param = do
    li <- lift ask
    case M.lookup rule refinement_parser of
        Just f -> EitherT $ mapRWST (\x -> return (runIdentity x)) $
            runEitherT $ f rule param
        Nothing -> left [Error (format "invalid refinement rule: {0}" rule) li]

refinement_parser :: Map String (
                  String
               -> RuleParserParameter
               -> EitherT [Error] (RWS LineInfo [Error] System) Rule)
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
        HintBuilderDecl [LatexDoc] MachineId MachinePh2

ensure :: ProgressProp 
       -> HintBuilder
       -> [Label]
       -> ERWS Ensure
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
                     [(MachineId,MachineId)] 
                     (Hierarchy MachineId)
topological_order = Pipeline empty_spec empty_spec $ \es -> do
        let cs = cycles es
        vs <- lift $ toEither $ mapM cycl_err_msg cs
        return $ Hierarchy vs $ M.fromList es
    where
        struct = "refinement structure" :: String
        cycle_msg ys = format msg struct $ intercalate ", " (map show ys)
        cycl_err_msg (AcyclicSCC v) = return v
        cycl_err_msg (CyclicSCC vs) = do
            li <- ask
            tell [Error (cycle_msg vs) li] 
            return (error "topological_order")
        msg = "A cycle exists in the {0}: {1}"

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




get_components :: [LatexDoc] -> LineInfo 
               -> Either [Error] (M.Map String [LatexDoc],M.Map String [LatexDoc])
get_components xs li = 
        liftM g
            $ R.runReader (runEitherT $ W.execWriterT (mapM_ f xs)) li

    where
        with_li li cmd = R.local (const li) cmd
        get_name li xs = with_li li $ liftM fst $ lift $ get_1_lbl xs
        f x@(Env tag li0 xs _li1) 
            | tag == "machine" = do
                    n <- get_name li0 xs
                    W.tell ([(n,xs)],[])
            | tag == "context" = do
                    n <- get_name li0 xs
                    W.tell ([],[(n,xs)])
            | otherwise      = map_docM_ f x
        f x = map_docM_ f x
        g (x,y) = (M.fromListWith (++) x, M.fromListWith (++) y)


run_phase1_types :: Pipeline MM 
                        (MTable MachinePh0)
                        ( Hierarchy MachineId
                        , MTable MachinePh1)
run_phase1_types = proc p0 -> do
    ts <- set_decl      -< p0
    e  <- event_decl    -< p0
    r  <- refines_mch   -< p0
    it <- import_theory -< p0
    let refs  = r >>= make_all_tables (format "Multiple refinement clauses")
    One refs <- triggerP -< One refs
    r_ord <- topological_order -< toList $ mapMaybe (liftM fst . M.lookup ()) refs
    let t = M.map fst <$> ts
        s = M.map snd <$> ts
        evts'  = inherit3 r_ord `liftM` e >>= make_all_tables (format "Multiple events with the name {0}")
        types  = inherit r_ord `liftM` t  >>= make_all_tables (format "Multiple sets with the name {0}")
        imp_th = inherit r_ord `liftM` it >>= make_all_tables (format "Theory imported multiple times")
        -- remove the liftM in the next line
    (types,s,evts',imp_th') <- triggerP -< 
                ( types, s
                , M.map (M.map fst) `liftM` evts'
                , imp_th)
        -- BIG FLAG
        -- the creation of p1 won't detect clashes between type names, it will merely overshadow
        -- some types with (hopefully) the most local types
        -- BIG FLAG
    let f th = M.unions $ map AST.types $ M.elems th
        basic = fromList [("arithmetic",arithmetic),("basic",basic_theory)]
        imp_th = M.map (union basic . M.map fst) imp_th'
        all_types = M.intersectionWith (\ts th -> M.map fst ts `union` f th) types imp_th
        p1 = make_phase1 <$> p0 <.> imp_th 
                         <.> (M.map (M.map fst) types) 
                         <.> all_types 
                         <.> s <.> evts'
    returnA -< (r_ord,p1)

make_phase1 :: MachinePh0
            -> Map String Theory
            -> Map String Sort
            -> Map String Sort
            -> [(String, VarScope)]
            -> Map Label (EventId, DeclSource)
            -> MachinePh1
make_phase1 _p0 _pImports _pTypes _pAllTypes _pSetDecl evts = MachinePh1 { .. }
    where
        _pEvents    = M.map (uncurry EventPh1 . second (== Local)) evts ^. pFromEventId
        _pContext   = TheoryP1 { .. }
        _t0         = TheoryP0 ()
        -- _pImports
        -- _pNewEvents = M.map fst $ M.filter ((== Local) . snd) evts

run_phase :: [Pipeline MM a (Either [e] b)]
          -> Pipeline MM a (Either [e] [b])
run_phase xs = run_phase_aux xs >>> arr (all_errors')

run_phase_aux :: [Pipeline MM a b] -> Pipeline MM a [b]
run_phase_aux [] = arr $ const []
run_phase_aux (cmd:cs) = proc x -> do
        y  <- cmd -< x
        ys <- run_phase_aux cs -< x
        returnA -< y:ys

run_phase2_vars :: Pipeline MM 
                        (Hierarchy MachineId,MTable MachinePh1)
                        (MTable MachinePh2)
run_phase2_vars = proc (r_ord, p1) -> do
    vs <- run_phase
        [ variable_decl
        , constant_decl
        , dummy_decl
        , index_decl
        , arr $ Right . M.map (L.view pSetDecl)
        , param_decl
        , remove_var ] -< p1
    let vars    =      make_all_tables' err_msg
                   =<< inherit2 r_ord 
                   <$> unionsWith (++) <$> vs
        err_msg = (format "Multiple symbols with the name {0}") 
    One vars <- triggerP -< One vars
    let p2 = make_phase2 <$> p1 <.> vars
        _  = vars :: MTable (Map String VarScope)
    returnA -< p2

make_phase2 :: MachinePh1
            -> Map String VarScope
            -> MachinePh2 
make_phase2 p1 vars = MachinePh2 { .. }
    where
        -- _ = over :: Setting (->) s t a b -> (a -> b) -> s -> t
        -- over ln f = runIdentity . ln (Identity . f)
        _c1   = TheoryP2 (p1 ^. pContext)
        _e1   = EventPh2 <$> (p1 ^. pEvents) 
                         <.> _pIndices `M.union` evtEmpty
                         <.> _pParams  `M.union` evtEmpty
                         <.> _pSchSynt 
                         <.> _pEvtSynt 
        _p1   = p1 & (pEvents .~ _e1) & (pContext .~ _c1)
        types = p1 ^. pTypes 
        imps  = p1 ^. pImports
        _pDelVars = mapMaybe getDelVars vars
        evtEmpty = M.map (const M.empty) evts
        evts  = M.map (const ()) (p1 ^. pEvents)
        -- vars = M.map (M.map fst) vars'
        _pStateVars = fmap fst $ mapMaybe getStateVars vars
        _pDefinitions = mapMaybe getDefs vars
        _pIndices :: Map EventId (Map String Var)
        _pIndices   = flipMap $ mapMaybe (fmap (M.map fst) . getIndices) vars
        _pParams :: Map EventId (Map String Var)
        _pParams    = getEventParams evts vars
            -- flipMap $ mapMaybe (fmap (M.map fst) . getEventParams) vars
        ind_param :: Map EventId (Map String Var)
        ind_param   = flipMap $ mapMaybe (fmap (M.map fst) . getParamInd) vars
        _pAbstractVars = fmap fst $ mapMaybe getAbsVars vars
        _pNotation  = th_notation $ empty_theory { extends = imps }
        _pDummyVars = fmap fst $ mapMaybe getDummies vars
        _pConstants = fmap fst $ mapMaybe getConstants vars

        constants = (_pConstants `M.union` (M.mapMaybe defToVar _pDefinitions))

        _pCtxSynt   = mkSetting _pNotation types constants M.empty _pDummyVars
        _pMchSynt   = mkSetting _pNotation types constants refVars _pDummyVars
        
        refVars = _pAbstractVars `M.union` _pStateVars

        findE m e = findWithDefault M.empty e m :: Map String Var

        f :: Map EventId (Map String Var)
          -> EventId -> ParserSetting
        f table e    = mkSetting _pNotation types (constants `union` findE table e) refVars _pDummyVars
        
        event_namespace table = -- (fromList . map (f table) . M.elems) 
            M.mapWithKey (const . f table) evts 

        _pSchSynt :: Map EventId ParserSetting
        _pSchSynt = event_namespace _pIndices

        _pEvtSynt :: Map EventId ParserSetting
        _pEvtSynt = event_namespace ind_param

default_schedule_decl :: MPipeline MachinePh2 [(Label,ExprScope)]
default_schedule_decl = arr $ \p2 -> 
        Right $ M.map (map default_sch . elems . M.map Just . M.map (^. pEventId)) 
              $ M.map (M.filter (^. pIsNew) . (^. pEvents)) p2
    where
        li = LI "default" 1 1
        default_sch e = ( label "default",
                          ExprScope $ EventExpr 
                            $ singleton e (EvtExprScope $ CoarseSchedule zfalse Inherited li))

run_phase3_exprs :: Pipeline MM (Hierarchy MachineId,MTable MachinePh2) (MTable MachinePh3)
run_phase3_exprs = proc (r_ord,p2) -> do
        es <- run_phase 
            [ assignment
            , bcmeq_assgn
            , bcmsuch_assgn
            , bcmin_assgn
            , guard_decl
            , default_schedule_decl
            , fine_sch_decl
            , coarse_sch_decl
            , initialization
            , assumption
            , invariant
            , transient_prop
            , transientB_prop
            , constraint_prop
            , progress_prop
            , safetyA_prop
            , safetyB_prop
            , remove_assgn
            , remove_init
            , init_witness_decl
            , witness_decl ] -< p2
        let exprs =     make_all_tables' err_msg
                    =<< inherit2 r_ord 
                    <$> unionsWith (++) <$> es
            err_msg :: Label -> String
            err_msg = (format "Multiple expressions with the label {0}") 
                        
        One exprs <- triggerP -< One exprs
        let p3 = all_errors $ make_phase3 <$> p2 <.> exprs
        liftP -< hoistEither p3

old :: Scope s => Map a s -> Map a s
old = M.mapMaybe is_inherited

new :: Scope s => Map a s -> Map a s
new = M.mapMaybe is_local

make_phase3 :: MachinePh2 -> Map Label ExprScope -> Either [Error] MachinePh3
make_phase3 p2 exprs 
        | L.null errs = Right p3''
        | otherwise   = Left errs
    where
        p3 = over pEvents (M.map makeEventPh3) (makeMachinePh3' p2)
        (p3',errs) = execRWS (mapM_ (uncurry parseExpr) $ M.toList exprs) () p3
        skip = M.fromList [ (v,Word (prime v) `zeq` Word v) | v <- M.elems $ view newDelVars p3']
        p3'' = over pEvents (M.map $ over eWitness (`M.union` skip)) p3'

run_phase4_proofs :: Pipeline MM (Hierarchy MachineId,MTable MachinePh3) (MTable MachinePh4)
run_phase4_proofs = proc (r_ord,p3) -> do
        refs   <- run_phase 
            [ ref_replace_csched
            , ref_weaken_csched
            , ref_replace_fsched
            , ref_remove_guard ] -< p3
        ref_p  <- refine_prog_prop -< p3
        comm   <- all_comments -< p3
        prfs   <- all_proofs   -< p3
        let evt_refs :: Either [Error] (MTable (Map EventId [((Label,ScheduleChange),LineInfo)]))
            evt_refs = M.map (fromListWith (++)) <$> unionsWith (++) <$> refs
            prog_ref :: Either [Error] (MTable (Map ProgId ((Rule,[(ProgId,ProgId)]),LineInfo)))
            prog_ref = ref_p >>= make_all_tables (format "Multiple refinement of progress property {0}")
            proofs = prfs >>= make_all_tables (format "Multiple proofs labeled {0}")
            comments = do
                    c <- comm
                    make_all_tables (format "Multiple comments for {0}")
                        $ inherit r_ord c
        (evt_refs,prog_ref,comments,proofs) <- triggerP -< (evt_refs,prog_ref,comments,proofs)
        let _ = evt_refs :: MTable (Map EventId [((Label,ScheduleChange),LineInfo)])
            _ = prog_ref :: MTable (Map ProgId ((Rule,[(ProgId,ProgId)]),LineInfo))
            sch_chg :: MTable (Map EventId [(Label,Change)])
            sch_chg = M.map (M.map $ concatMap $ addRemove . snd . fst) evt_refs
            addRemove sc = M.toList (fromSet (const AddC) $ add sc) ++ M.toList (fromSet (const RemoveC) $ remove sc)
            old_sch = inheritWith 
                    (M.map $ L.map $ first (,Local)) 
                    -- _ _
                    (M.map $ L.map $ first $ second $ const Inherited) 
                    (M.unionWith (++)) 
                    r_ord sch_chg
            evt_live :: MTable (EventId <-> ProgId)
            evt_live  = M.map (R.fromListMap . M.map (concatMap $ hyps_labels . snd . fst)) evt_refs
            live_evt :: MTable (ProgId <-> EventId)
            live_evt  = M.map (R.fromListMap . M.map (supporting_evts . fst . fst)) prog_ref
                -- 
            evt_evt :: MTable (Map EventId EventId)
            evt_evt   = M.map (M.mapWithKey const) evt_refs 
            live_live :: MTable (LiveEvtId <-> LiveEvtId)
            live_live = M.map (R.bimap Right Right) $
                        M.map (R.fromListMap . M.map (L.map snd . snd . fst)) prog_ref
            distr :: ([a],b) -> [(a,b)]
            distr (xs,y) = map (\x -> (x,y)) xs 
            hyps_table :: ((a,ScheduleChange),c) -> [(ProgId,c)]
            hyps_table = distr . first (hyps_labels . snd)
            live_struct = LiveStruct <$> (M.map (view pMachineId) p3) 
                   <.> evt_live <.> live_live 
                   <.> live_evt <.> evt_evt 
                   <.> M.mapWithKey (\k -> M.map (k,)) (M.map (M.map snd) prog_ref) 
                   <.> M.mapWithKey (\k -> M.map (k,)) (M.map (uncurryMap . M.map (M.fromList . concatMap hyps_table)) evt_refs)
            struct = all_errors $ 
                     M.map raiseStructError $ inheritWith 
                        Conc (Abs . getConcrete)
                        mergeLiveness 
                        r_ord live_struct
                    -- >>= make_all_tables' _
        One struct <- triggerP -< One struct
        let p4 = make_phase4 <$> p3 <.> evt_refs 
                             <.> prog_ref <.> comments 
                             <.> proofs <.> struct
                             <.> old_sch
        returnA -< p4

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

instance Monoid LiveStruct where
    mempty = LiveStruct
        { machine_id = $myError
        , evt_live = R.empty
        , live_live = R.empty
        , live_evt = R.empty
        , evt_evt = M.empty
        , live_info = M.empty
        , evt_info = M.empty
        }
    mappend = $myError

make_phase4 :: MachinePh3 
            -> Map EventId [((Label, ScheduleChange), LineInfo)]
            -> Map ProgId ((Rule,[(ProgId,ProgId)]),LineInfo) 
            -> Map DocItem (String,LineInfo)
            -> Map Label (Tactic Proof, LineInfo) 
            -> LiveStruct
            -> Map EventId [((Label,DeclSource),Change)]
            -> MachinePh4
make_phase4 p3 evt_refs prog_ref comments proofs _ old_sch = MachinePh4 { .. }
    where
        _e3 = EventPh4 <$> (p3 ^. pEvents) 
                       <.> _pEventRefRule `M.union` evtEmpty
                       <.> old_sch' `M.union` evtEmpty
        old_sch' = M.map (  L.map (first fst) 
                                  . L.filter ((Inherited==) . snd . fst)) old_sch
        evtEmpty :: Map EventId [a]
        evtEmpty = M.map (const []) (p3 ^. pEvents)
        _p3 = p3 & pEvents .~ _e3
        _pProofs = proofs
        _pEventRefRule = M.map (L.map fst) evt_refs
        _pLiveRule = M.map (fst . fst) prog_ref
        _pComments = M.map fst comments

make_machine :: MachineId -> MachinePh4
             -> Either [Error] Machine
make_machine (MId m) p4 = mch'
    where
        types   = p4 ^. pTypes
        -- evtSet  = p4 ^. pEvents
        imp_th  = p4 ^. pImports
        evt_refs :: Map EventId [(Label,ScheduleChange)]
        evt_refs = p4 ^. pEventRefRule 
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
        evt_grd_po (evt,lbl) = composite_label 
                                        [ as_label evt
                                        , label "GRD"
                                        , label m, lbl]
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
                    `union` M.mapKeys evt_grd_po (uncurryMap $ M.mapWithKey (\k -> M.mapWithKey $ \l _ -> Rule (add_guard (as_label k) l)) (p4 ^. pNewGuards))
                    -- `union` M.fromList (L.map (rule_name &&& id) $ concat $ elems $ M.map (L.map Rule . sched_ref) evts)
                    `union` M.map (const $ Rule Add) (_progress props)) 
                    `union` fromList (concat $ elems $ M.mapWithKey evtr2der evt_refs)
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
            all_errors' $ flip map (toList po_err) $ \(lbl,(_,li)) -> 
                Left [Error (format "proof obligation does not exist: {0}" lbl) li]
            xs <- all_errors' $ flip map (toList proofs) $ \(k,(tac,li)) -> do
                p <- runTactic li (pos ! k) tac
                return (k,p)
            return mch 
                { AST.props = (AST.props mch) 
                    { _proofs = fromList xs } }
        evtr2der :: EventId -> [(Label,ScheduleChange)] -> [(Label,Rule)]
        evtr2der (EventId evt) xs = zipWith f xs [0..]
            where
                f (lbl,ref) n = (composite_label [evt,lbl,label $ show n], Rule ref)
        events = p4 ^. pEvents
        evts = M.mapWithKey g events 
                :: Map EventId Event
        g :: EventId -> EventPh4
          -> Event
        g (EventId name) evt
            = Event
                { indices = evt ^. eIndices
                , params  = evt ^. eParams
                , guards  = evt ^. eGuards
                , witness = evt ^. eWitness
                , old_guard = evt ^. eOldGuards
                , actions = evt ^. eNewActions
                , del_acts = evt ^. eDelActions
                , scheds  = c_sched `union` f_sched
                , eql_vars = keep' ab_var (evt ^. eOldActions)
                             `M.intersection` frame (evt ^. eNewActions)
                , old_sched = Schedule 
                                    { coarse = c_sched `M.intersection` old_sched
                                    , fine   = MM.listToMaybe $ M.toList $ f_sched `M.intersection` old_sched }
                , sched_ref =  map (add_guard name) (keys $ evt ^. eNewGuards) 
                            ++ map snd (evt ^. eRefRule)
                , old_acts = M.map (const ()) $ evt ^. eOldActions
                }
            where
                old_sched = M.filter (== AddC) $ M.fromList $ ("default",AddC) : reverse (evt ^. eOldSched)
                c_sched = (evt ^. eCoarseSched) 
                f_sched = (evt ^. eFineSched)

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

liftP :: Pipeline MM (M a) a
liftP = Pipeline empty_spec empty_spec lift


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



getEventParams :: Map EventId ()
               -> Map String VarScope 
               -> Map EventId (Map String Var)
getEventParams = getEventDecls Param

getEventDecl :: EvtScope -> VarScope -> Maybe (Map EventId (Var, LineInfo))
getEventDecl scope (Evt m) = Just $ fromList $ MM.mapMaybe f $ toList m
    where
        f (Just e,(v,s,_,li)) 
            | s == scope = Just (e,(v,li))
        f _ = Nothing
getEventDecl _ _ = Nothing

getEventDecls :: EvtScope
              -> Map EventId ()
              -> Map String VarScope
              -> Map EventId (Map String Var)
getEventDecls scope evts vars = M.map fromList $ M.unionsWith (++) $ empty : map moveName (M.toList decl)
    where
        empty :: Map EventId [(String,Var)]
        empty = M.map (const []) evts
        moveName :: (String,Map EventId (Var,LineInfo)) -> Map EventId [(String,Var)]
        moveName (vn,m) = M.map (\(x,_) -> [(vn,x)]) m
        decl = M.mapMaybe (getEventDecl scope) vars


getParamInd :: VarScope -> Maybe (Map EventId (Var,LineInfo))
getParamInd (Evt m) = Just $ fromList $ MM.mapMaybe f $ toList m
    where
        f (Just e,(v,_,_,li)) = Just (e,(v,li))
        f _ = Nothing
getParamInd _ = Nothing

getDefs :: VarScope -> Maybe Def
getDefs (TheoryDef d _ _) = Just d
getDefs _ = Nothing

getOrphanDelVars :: VarScope -> Maybe LineInfo
getOrphanDelVars (DelMch Nothing Local li) = Just li
getOrphanDelVars _ = Nothing


getStateVars :: VarScope -> Maybe (Var,LineInfo)
getStateVars (Machine v _ li) = Just (v,li)
getStateVars _ = Nothing

getDelVars :: VarScope -> Maybe (Var,LineInfo)
getDelVars (DelMch v _ li) = (,li) <$> v
getDelVars _ = Nothing

getAbsVars :: VarScope -> Maybe (Var,LineInfo)
getAbsVars (Machine v Inherited li) = Just (v,li)
getAbsVars (DelMch v Local li)      = (,li) <$> v
getAbsVars _ = Nothing


getDummies :: VarScope -> Maybe (Var,LineInfo)
getDummies (Evt m) = fmap (\(v,_,_,li) -> (v,li)) $ Nothing `M.lookup` m
getDummies _ = Nothing

defToVar :: Def -> Maybe Var
defToVar (Def _ n [] t _) = Just (Var n t)
defToVar (Def _ _ (_:_) _ _) = Nothing

getConstants :: VarScope -> Maybe (Var,LineInfo)
-- getConstants (TheoryDef (Def [] n [] t _) _ li) = Just (Var n t,li)
getConstants (TheoryConst v _ li) = Just (v,li)
getConstants _ = Nothing


getIndices :: VarScope -> Maybe (Map EventId (Var,LineInfo))
getIndices = getEventDecl Index

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

runPipeline' :: M.Map String [LatexDoc] 
             -> M.Map String [LatexDoc]
             -> Pipeline MM Input a 
             -> M a
runPipeline' ms cs p = runReaderT (f input) input
    where
        input = Input mch ctx
        mch   = M.mapKeys MId $ M.map (getLatexBlocks m_spec) ms
        ctx   = M.mapKeys CId $ M.map (getLatexBlocks c_spec) cs
        Pipeline m_spec c_spec f = p

type MPipeline ph a = Pipeline MM (MTable ph) (Either [Error] (MTable a))

set_decl :: MPipeline MachinePh0 
            ( [(String,Sort,LineInfo)]
            , [(String,VarScope)] )
set_decl = machineCmd "\\newset" $ \(One (String tag)) _m _ -> do
            let name     = tag 
                new_sort = Sort tag (z3_escape name) 0
                new_type = Gen $ USER_DEFINED new_sort []
                new_def = Def [] name [] (set_type new_type)
                                    $ zlift (set_type new_type) ztrue
            li <- lift ask
            return ([(tag,new_sort,li)],[(tag,TheoryDef new_def Local li)])

event_decl :: MPipeline MachinePh0 [(Label, EventId, LineInfo)]
event_decl = machineCmd "\\newevent" $ \(One evt) _m _ -> do 
            li <- lift ask 
            return [(evt,EventId evt,li)]

refines_mch :: MPipeline MachinePh0 [((), MachineId, LineInfo)]
refines_mch = machineCmd "\\refines" $ \(One amch) cmch (MachinePh0 ms _) -> do
            li <- lift ask
            unless (amch `M.member` ms) 
                $ left [Error (format "Machine {0} refines a non-existant machine: {1}" cmch amch) li]
                -- check that mch is a machine
            return [((),amch,li)]


import_theory :: MPipeline MachinePh0 [(String, Theory, LineInfo)]
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


variable_decl :: MPipeline MachinePh1
                    [(String,VarScope)]
variable_decl = machine_var_decl Machine "\\variable"

constant_decl :: MPipeline MachinePh1
                    [(String,VarScope)]
constant_decl = machine_var_decl TheoryConst "\\constant"

remove_var :: MPipeline MachinePh1 [(String,VarScope)]
remove_var = machineCmd "\\removevar" $ \(One xs) _m _p1 -> do
        li <- lift ask
        return $ map ((\x -> (x,DelMch Nothing Local li)) . toString) xs

dummy_decl :: MPipeline MachinePh1
                    [(String,VarScope)]
dummy_decl = machine_var_decl 
        (\v source li -> Evt $ singleton Nothing (v,Param,source,li)) 
        "\\dummy"

machine_var_decl :: (Var -> DeclSource -> LineInfo -> VarScope)
                 -> String
                 -> MPipeline MachinePh1
                        [(String,VarScope)]
machine_var_decl scope kw = machineCmd kw $ \(One xs) _m p1 -> do
            vs <- get_variables' (p1 ^. pAllTypes) xs
            li <- lift ask
            return $ map (\(x,y) -> (x,scope y Local li)) vs

index_decl :: MPipeline MachinePh1 [(String,VarScope)]
index_decl = event_var_decl Index "\\indices"

param_decl :: MPipeline MachinePh1 [(String,VarScope)]
param_decl = event_var_decl Param "\\param"

event_var_decl :: EvtScope
               -> String
               -> MPipeline MachinePh1
                    [(String,VarScope)]
event_var_decl escope kw = machineCmd kw $ \(lbl,xs) _m p1 -> do
            let ts   = L.view pTypes p1
                evts = L.view pEventIds p1 
            evt <- bind
                (format "event '{0}' is undeclared" lbl)
                $ lbl `M.lookup` evts
            li <- lift ask
            vs <- get_variables' ts xs
            return $ map (\(n,v) -> ((n,Evt $ M.singleton (Just evt) (v,escope,Local,li)))) vs

    -- Todo: detect when the same variable is declared twice
    -- in the same declaration block.
                        
tr_hint :: MachinePh2
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

tr_hint' :: MachinePh2
         -> MachineId
         -> Map String Var
         -> NonEmpty Label
         -> [LatexDoc]
         -> TrHint
         -> RWS LineInfo [Error] System TrHint
tr_hint' p2 _m fv lbls = visit_doc []
        [ ( "\\index"
          , CmdBlock $ \(String x, texExpr) (TrHint ys z) -> do
                evs <- get_events p2 $ NE.toList lbls
                -- evts <- bind_all lbls
                --     (format "'{1}' is not an event of '{0}'" $ _name m)
                --     (`M.lookup` events m)
                let inds = event_indices p2
                vs <- bind_all evs 
                    (format "'{0}' is not an index of '{1}'" x) 
                    (\e -> x `M.lookup` (inds ! e))
                let Var _ t = head vs
                    ind = prime $ Var x t
                expr <- parse_expr' 
                    (machine_parser p2 `with_vars` fv) 
                        { expected_type = Just t }
                    texExpr
                return $ TrHint (insert x (t, Word ind `zeq` expr) ys) z)
        , ( "\\witness"
          , CmdBlock $ \(String x, texExpr) (TrHint ys z) -> do
                evs <- get_events p2 $ NE.toList lbls
                -- evts <- bind_all lbls
                --     (format "'{1}' is not an event of '{0}'" $ _name m)
                --     (`M.lookup` events m)
                let inds = event_indices p2
                vs <- bind_all evs 
                    (format "'{0}' is not an index of '{1}'" x) 
                    (\e -> x `M.lookup` (inds ! e))
                let Var _ t = head vs
                    ind = prime $ Var x t
                    x'  = x ++ "'"
                expr <- parse_expr' 
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


check_types :: Either [String] a -> EitherT [Error] (RWS LineInfo [Error] System) a    
check_types c = EitherT $ do
    li <- ask
    return $ either (\xs -> Left $ map (`Error` li) xs) Right c

get_progress_prop :: MachinePh3 -> MachineId -> ProgId -> M ProgressProp
get_progress_prop p3 _m lbl =  
            bind
                (format "progress property '{0}' is undeclared" lbl)
                $ lbl `M.lookup` (L.view pProgress p3)

get_safety_prop :: MachinePh3 -> MachineId -> Label -> M SafetyProp
get_safety_prop p3 _m lbl =  
            bind
                (format "safety property '{0}' is undeclared" lbl)
                $ lbl `M.lookup` (L.view pSafety p3)

get_notation :: HasMachinePh2' phase => phase events thy -> Notation
get_notation p2 = L.view pNotation p2
    -- where MachinePh2 _ _ _ _ _ notation _ _ _ _ = ancestor p2

machine_events :: HasMachinePh1 phase events => phase events thy -> Map Label EventId
machine_events p2 = L.view pEventIds p2

get_event :: HasMachinePh1 phase events => phase events thy -> Label -> M EventId
get_event p2 ev_lbl = do
        let evts = machine_events p2
        bind
            (format "event '{0}' is undeclared" ev_lbl)
            $ ev_lbl `M.lookup` evts

get_events :: MachinePh2 -> [Label] -> M [EventId]
get_events p2 ev_lbl = do
            let evts = machine_events p2
            bind_all ev_lbl
                (format "event '{0}' is undeclared")
                $ (`M.lookup` evts)

get_schedules :: MachinePh3 -> EventId -> M (Map Label Expr)
get_schedules p3 evt = 
        return $ L.view pSchedules p3 ! evt

get_guards :: MachinePh3 -> EventId -> M (Map Label Expr)
get_guards p3 evt = 
        return $ (p3 ^. pGuards) ! evt

get_invariants :: MachinePh3 -> Map Label Expr
get_invariants p3 = (p3 ^. pInvariant)

progress_props :: MachinePh3 -> Map ProgId ProgressProp
progress_props p3 = p3 ^. pProgress

event_parser :: HasMachinePh2 phase events => phase events thy -> EventId -> ParserSetting
event_parser p2 ev = (p2 ^. pEvtSynt) ! ev

schedule_parser :: HasMachinePh2 phase events => phase events thy -> EventId -> ParserSetting
schedule_parser p2 ev = (p2 ^. pSchSynt) ! ev

machine_parser :: HasMachinePh2 phase events => phase events thy -> ParserSetting
machine_parser p2 = L.view pMchSynt p2

context_parser :: HasMachinePh2' phase => phase events thy -> ParserSetting
context_parser p2 = p2 ^. pCtxSynt

state_variables :: HasMachinePh2' phase => phase events thy -> Map String Var
state_variables p2 = p2 ^. pStateVars

abstract_variables :: HasMachinePh2' phase => phase events thy -> Map String Var
abstract_variables p2 = p2 ^. pAbstractVars

dummy_vars :: HasMachinePh2' phase => phase events thy -> Map String Var
dummy_vars p2 = p2 ^. pDummyVars

event_indices :: HasMachinePh2 phase events => phase events thy -> Map EventId (Map String Var)
event_indices p2 = p2 ^. pIndices

free_vars' :: Map String Var -> Expr -> Map String Var
free_vars' ds e = vs `M.intersection` ds
    where
        vs = symbol_table $ S.elems $ used_var e

assignment :: MPipeline MachinePh2
                    [(Label,ExprScope)]
assignment = machineCmd "\\evassignment" $ \(ev_lbl, lbl, xs) _m p2 -> do
            ev <- get_event p2 ev_lbl
            pred <- parse_expr' 
                (event_parser p2 ev) 
                { is_step = True } xs
            let frame = M.elems $ (state_variables p2) `M.difference` (abstract_variables p2) :: [Var] 
                act = BcmSuchThat frame pred
            li <- lift ask
            return [(lbl,ExprScope $ EventExpr $ M.singleton (Just ev) $ (EvtExprScope $ Action act Local li))]

bcmeq_assgn :: MPipeline MachinePh2
                    [(Label,ExprScope)]
bcmeq_assgn = machineCmd "\\evbcmeq" $ \(ev_lbl, lbl, String v, xs) _m p2 -> do
            let _ = lbl :: Label
            ev <- get_event p2 ev_lbl
            var@(Var _ t) <- bind
                (format "variable '{0}' undeclared" v)
                $ v `M.lookup` (state_variables p2)
            xp <- parse_expr' 
                (event_parser p2 ev) 
                { expected_type = Just t } xs
            check_types
                $ Right (Word var :: Expr) `mzeq` Right xp
            let act = Assign var xp
            li <- lift ask
            return [(lbl,ExprScope $ EventExpr $ M.singleton (Just ev) $ (EvtExprScope $ Action act Local li))]

bcmsuch_assgn :: MPipeline MachinePh2
                    [(Label,ExprScope)]
bcmsuch_assgn = machineCmd "\\evbcmsuch" $ \(evt, lbl, vs, xs) _m p2 -> do
            ev <- get_event p2 evt
            xp  <- parse_expr' (event_parser p2 ev)
                    { is_step = True } xs
            vars <- bind_all (map toString vs)
                (format "variable '{0}' undeclared")
                $ (`M.lookup` state_variables p2)
            let act = BcmSuchThat vars xp
            li <- lift ask
            return [(lbl,ExprScope $ EventExpr $ M.singleton (Just ev) $ (EvtExprScope $ Action act Local li))]

bcmin_assgn :: MPipeline MachinePh2
                    [(Label,ExprScope)]
bcmin_assgn = machineCmd "\\evbcmin" $ \(evt, lbl, String v, xs) _m p2 -> do
            ev <- get_event p2 evt
            var@(Var _ t) <- bind
                (format "variable '{0}' undeclared" v)
                $ v `M.lookup` (state_variables p2)
            xp  <- parse_expr' (event_parser p2 ev)
                    { expected_type = Just (set_type t) } xs
            let act = BcmIn var xp
            check_types $ Right (Word var) `zelem` Right xp
            li <- lift ask
            return [(lbl,ExprScope $ EventExpr $ M.singleton (Just ev) $ (EvtExprScope $ Action act Local li))]

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
    make_inherited (Initially x _ y) = Just $ Initially x Inherited y
    make_inherited (DelInit x _ y) = Just $ DelInit x Inherited y
    merge_scopes (DelInit _ s li) (Initially e _ _) = DelInit (Just e) s li
    merge_scopes (Initially e _ _) (DelInit _ s li) = DelInit (Just e) s li
    merge_scopes _ _ = error "Initially Scope.merge_scopes: _, _"

used_var' :: Expr -> Map String Var
used_var' = symbol_table . S.toList . used_var

instance IsExprScope Initially where
    parseExpr lbl (Initially x _ li) = do
        modify $ over pInit $ M.insert lbl x
        vs <- gets $ view pDelVars
        let msg = format "initialization predicate '{0}' refers to deleted variables" lbl
            lis = L.map (first name) $ M.elems $ vs `M.intersection` used_var' x
            lis' = L.map (first (format "deleted variable {0}")) lis
        unless (L.null lis')
            $ tell [MLError msg $ (format "predicate {0}" lbl,li):lis']
    parseExpr lbl (DelInit (Just x) Local _) = modify $ over pDelInits $ M.insert lbl x
    parseExpr _ (DelInit (Just _) Inherited _) = return ()
    parseExpr lbl (DelInit Nothing _ li) = tell [Error msg li]
        where
            msg = format "initialization predicate '{0}' was deleted but does not exist" lbl

remove_init :: MPipeline MachinePh2 [(Label,ExprScope)]
remove_init = machineCmd "\\removeinit" $ \(One lbls) _m _p2 -> do
            li <- lift ask
            return [(lbl,ExprScope $ DelInit Nothing Local li) | lbl <- lbls ]

remove_assgn :: MPipeline MachinePh2 [(Label,ExprScope)]
remove_assgn = machineCmd "\\removeact" $ \(evt, lbls) _m p2 -> do
            ev <- get_event p2 evt
            li <- lift ask
            return [(lbl,ExprScope $ EventExpr $ M.singleton (Just ev) $ (EvtExprScope $ DelAction Nothing Local li)) | lbl <- lbls ]

witness_decl :: MPipeline MachinePh2 [(Label,ExprScope)]
witness_decl = machineCmd "\\witness" $ \(evt, String var, xp) _m p2 -> do
            ev <- get_event p2 evt
            p  <- parse_expr' (event_parser p2 ev) { is_step = True } xp
            v  <- bind (format "'{0}' is not a disappearing variable" var)
                (var `M.lookup` (L.view pAbstractVars p2 `M.difference` L.view pStateVars p2))
            li <- lift ask
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

instance IsEvtExpr CoarseSchedule where
    type ExprT CoarseSchedule = Expr
    exprLens _ = [LensT eCoarseSched]

instance IsEvtExpr FineSchedule where
    type ExprT FineSchedule = Expr
    exprLens _ = [LensT eFineSched]

instance IsEvtExpr Guard where
    type ExprT Guard = Expr
    exprLens x = case x ^. declSource of 
                    Inherited -> [LensT eOldGuards]
                    Local -> [LensT eNewGuards]

instance IsEvtExpr Witness where
    type ExprT Witness = Expr
    parseEvtExpr _ eid (Witness v e s _) = do
        case s of
            Inherited -> return ()
            Local -> 
                case eid of
                    Just eid ->
                        addToEventTable eWitness v eid e
                    Nothing ->
                        modify $ over pInitWitness $ M.insert v e
    exprLens _ = []

instance IsEvtExpr ActionDecl where
    type ExprT ActionDecl = Action
    parseEvtExpr lbl (Just eid) (DelAction Nothing _ li) = 
        tell [Error (format "action '{0}' of event '{1}' was deleted but does not exist" lbl eid) li]
    parseEvtExpr lbl (Just eid) x = do
        forM_ (exprLens x) $ \ln ->
            addToEventTable (getLens ln) lbl eid (x ^. evtExpr)
        case x of
            Action act _ li -> do
                vs <- gets $ view pDelVars
                let msgR = format "event '{1}', action '{0}' refers to deleted variables" lbl eid
                    msgW = format "event '{1}', action '{0}' assigns to deleted variables" lbl eid
                    liAct = (format "action {0}" lbl,li)
                    refs = L.map (first name) . M.elems 
                    lisRead = refs $ vs `M.intersection` used_var' (ba_pred act)
                    lisWrite = refs $ vs `M.intersection` frame (M.singleton "" act)
                    lisRead' = L.map (first $ format "deleted variable {0}") lisRead
                    lisWrite' = L.map (first $ format "deleted variable {0}") lisWrite
                unless (L.null lisRead')
                    $ tell [MLError msgR $ liAct:lisRead']
                unless (L.null lisWrite')
                    $ tell [MLError msgW $ liAct:lisWrite']
            DelAction (Just act) Local _ -> do
                vs <- gets $ view pDelVars
                ws <- gets $ view $ getEvent eid . eWitness
                let f = frame' act `M.intersection` vs
                    ns = M.fromList [ (v,ba_pred act) | v <- M.elems f ] `M.difference` ws
                modify $ over (getEvent eid . eWitness) $ M.union ns
            _ -> return ()
    parseEvtExpr _ Nothing _ = error "IsEvtExpr: Nothing"
    exprLens (Action _ Local _) = [LensT eNewActions]
    exprLens (Action _ Inherited _) = [LensT eOldActions,LensT eNewActions]
    exprLens (DelAction (Just _) Local _)  = [LensT eDelActions,LensT eOldActions]
    exprLens _ = []

instance IsExprScope EventExpr where
    parseExpr lbl (EventExpr m) = mapM_ f (toList m)
        where
            -- f :: (forall a. IsEvtExpr a => a -> b) -> EvtExprScope -> b
            f (eid,EvtExprScope x) = parseEvtExpr lbl eid x

init_witness_decl :: MPipeline MachinePh2 [(Label,ExprScope)]
init_witness_decl = machineCmd "\\initwitness" $ \(String var, xp) _m p2 -> do
            -- ev <- get_event p2 evt
            p  <- parse_expr' (machine_parser p2) xp
            v  <- bind (format "'{0}' is not a disappearing variable" var)
                (var `M.lookup` (L.view pAbstractVars p2 `M.difference` L.view pStateVars p2))
            li <- lift ask
            return [(label var, ExprScope $ EventExpr $ M.singleton Nothing (EvtExprScope $ Witness v p Local li))]

guard_decl :: MPipeline MachinePh2
                    [(Label,ExprScope)]
guard_decl = machineCmd "\\evguard" $ \(evt, lbl, xs) _m p2 -> do
            ev <- get_event p2 evt
            xp <- parse_expr' (event_parser p2 ev) xs
            li <- lift ask
            return [(lbl,ExprScope $ EventExpr $ M.singleton (Just ev) $ (EvtExprScope $ Guard xp Local li))]
 
coarse_sch_decl :: MPipeline MachinePh2
                    [(Label,ExprScope)]
coarse_sch_decl = machineCmd "\\cschedule" $ \(evt, lbl, xs) _m p2 -> do
            ev <- get_event p2 evt
            xp <- parse_expr' (schedule_parser p2 ev) xs
            li <- lift ask
            return [(lbl,ExprScope $ EventExpr $ M.singleton (Just ev) $ (EvtExprScope $ CoarseSchedule xp Local li))]

fine_sch_decl :: MPipeline MachinePh2
                    [(Label,ExprScope)]
fine_sch_decl = machineCmd "\\fschedule" $ \(evt, lbl, xs) _m p2 -> do
            ev <- get_event p2 evt
            xp <- parse_expr' (schedule_parser p2 ev) xs
            li <- lift ask
            return [(lbl,ExprScope $ EventExpr $ M.singleton (Just ev) $ (EvtExprScope $ FineSchedule xp Local li))]

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
    make_inherited (Axiom x _ y) = Just $ Axiom x Inherited y

instance IsExprScope Axiom where
    parseExpr lbl (Axiom x _ _) = modify $ over pAssumptions $ M.insert lbl x

assumption :: MPipeline MachinePh2
                    [(Label,ExprScope)]
assumption = machineCmd "\\assumption" $ \(lbl,xs) _m p2 -> do
            xp <- parse_expr' (context_parser p2) xs
            li <- lift ask
            return [(lbl,ExprScope $ Axiom xp Local li)]

        --------------------------
        --  Program properties  --
        --------------------------

initialization :: MPipeline MachinePh2
                    [(Label,ExprScope)]
initialization = machineCmd "\\initialization" $ \(lbl,xs) _m p2 -> do
            xp <- parse_expr' (machine_parser p2) xs
            li <- lift ask
            return [(lbl,ExprScope $ Initially xp Local li)]

instance Scope Invariant where
    merge_scopes _ _ = error "Invariant Scope.merge_scopes: _, _"
    clashes _ _ = True
    keep_from s x = guard (s == s') >> return x
        where
            s' = case x of (Invariant _ s _) -> s
    make_inherited (Invariant x _ y) = Just $ Invariant x Inherited y
    error_item (Invariant _ _ li)   = ("invariant", li)

modifyProps :: DeclSource -> Lens' MachinePh3 PropertySet
modifyProps Inherited = pOldPropSet
modifyProps Local = pNewPropSet

instance IsExprScope Invariant where
    parseExpr lbl (Invariant x s _) = 
        do 
            modify $ over pInvariant $ M.insert lbl x
            modify $ over (modifyProps s . inv) $ M.insert lbl x

invariant :: MPipeline MachinePh2
                    [(Label,ExprScope)]
invariant = machineCmd "\\invariant" $ \(lbl,xs) _m p2 -> do
            xp <- parse_expr' (machine_parser p2) xs
            li <- lift ask
            return [(lbl,ExprScope $ Invariant xp Local li)]

instance Scope TransientProp where
    merge_scopes _ _ = error "TransientProp Scope.merge_scopes: _, _"
    clashes _ _ = True
    keep_from s x = guard (s == s') >> return x
        where
            s' = case x of (TransientProp _ s _) -> s
    make_inherited (TransientProp x _ y) = Just $ TransientProp x Inherited y
    error_item (TransientProp _ _ li) = ("transient predicate", li)

instance IsExprScope TransientProp where
    parseExpr lbl (TransientProp x s _) = do
        modify $ over pTransient $ M.insert lbl x
        modify $ over (modifyProps s . transient) $ M.insert lbl x

transient_prop :: MPipeline MachinePh2
                    [(Label,ExprScope)]
transient_prop = machineCmd "\\transient" $ \(evts, lbl, xs) _m p2 -> do
            _evs <- get_events p2 evts
            tr   <- parse_expr' (machine_parser p2) 
                    { free_dummies = True } xs
            let withInd = L.filter (not . M.null . (^. eIndices) . ((p2 ^. pEvents) !)) _evs
            toEither $ error_list 
                [ ( not $ L.null withInd
                  , format "event(s) {0} have indices and require witnesses" 
                        $ intercalate "," $ map show withInd) ]
            let vs = symbol_table $ S.elems $ used_var tr
                fv = vs `M.intersection` dummy_vars p2
                prop = Transient fv tr evts empty_hint
            li <- lift ask
            return [(lbl,ExprScope $ TransientProp prop Local li)]

transientB_prop :: MPipeline MachinePh2
                    [(Label,ExprScope)]
transientB_prop = machineCmd "\\transientB" $ \(evts, lbl, hint, xs) m p2 -> do
            _evs <- get_events p2 evts
            tr   <- parse_expr' (machine_parser p2) 
                    { free_dummies = True } xs
            let fv = free_vars' ds tr
                ds = dummy_vars p2
            evts' <- bind "Expecting non-empty list of events"
                    $ NE.nonEmpty evts
            hint  <- tr_hint p2 m fv evts' hint
            let prop = Transient fv tr evts hint
            li <- lift ask
            return [(lbl,ExprScope $ TransientProp prop Local li)]

instance IsExprScope ConstraintProp where
    parseExpr lbl (ConstraintProp x s _) = do
        modify $ over (modifyProps s . constraint) $ M.insert lbl x

instance Scope ConstraintProp where
    merge_scopes _ _ = error "ConstraintProp Scope.merge_scopes: _, _"
    clashes _ _ = True
    keep_from s x = guard (s == s') >> return x
        where
            s' = case x of (ConstraintProp _ s _) -> s
    make_inherited (ConstraintProp x _ y) = Just $ ConstraintProp x Inherited y
    error_item (ConstraintProp _ _ li) = ("co property", li)

constraint_prop :: MPipeline MachinePh2
                    [(Label,ExprScope)]
constraint_prop = machineCmd "\\constraint" $ \(lbl,xs) _m p2 -> do
            pre <- parse_expr' (machine_parser p2)
                    { free_dummies = True
                    , is_step = True }
                    xs
            let vars = elems $ free_vars' ds pre
                ds = dummy_vars p2
                prop = Co vars pre
            li <- lift ask
            return [(lbl,ExprScope $ ConstraintProp prop Local li)]

instance IsExprScope SafetyDecl where
    parseExpr lbl (SafetyProp x s _) = 
        do 
            modify $ over pSafety $ M.insert lbl x
            modify $ over (modifyProps s . safety) $ M.insert lbl x

instance Scope SafetyDecl where
    merge_scopes _ _ = error "SafetyDecl Scope.merge_scopes: _, _"
    clashes _ _ = True
    keep_from s x = guard (s == s') >> return x
        where
            s' = case x of (SafetyProp _ s _) -> s
    make_inherited (SafetyProp x _ y) = Just $ SafetyProp x Inherited y
    error_item (SafetyProp _ _ li) = ("safety property", li)

safety_prop :: Label -> Maybe Label
            -> [LatexDoc]
            -> [LatexDoc]
            -> MachineId
            -> MachinePh2
            -> M [(Label,ExprScope)]
safety_prop lbl evt pCt qCt _m p2 = do
            (p,q)  <- toEither (do
                _  <- case evt of
                        Just evt -> do
                            liftM Just $ fromEither (error "safetyB") 
                                $ get_event p2 evt
                        Nothing -> return Nothing
                -- _  <- bind
                --     (format "event '{0}' is undeclared" evt)
                --     $ evt `M.lookup` events m
                p <- fromEither ztrue 
                    $ parse_expr' (machine_parser p2) 
                        { free_dummies = True }
                        pCt
                q <- fromEither ztrue 
                    $ parse_expr' (machine_parser p2) 
                        { free_dummies = True } 
                        qCt
                return (p,q))
            let ds  = dummy_vars p2
                dum = free_vars' ds p `union` free_vars' ds q
                new_prop = Unless (M.elems dum) p q evt
            li <- lift ask
            return [(lbl,ExprScope $ SafetyProp new_prop Local li)]

safetyA_prop :: MPipeline MachinePh2
                    [(Label,ExprScope)]
safetyA_prop = machineCmd "\\safety" 
                $ \(lbl, pCt, qCt) -> safety_prop lbl Nothing pCt qCt

safetyB_prop :: MPipeline MachinePh2
                    [(Label,ExprScope)]
safetyB_prop = machineCmd "\\safetyB" 
                $ \(lbl, evt, pCt, qCt) -> safety_prop lbl evt pCt qCt

instance IsExprScope ProgressDecl where
    parseExpr lbl (ProgressProp x s _) = 
        do 
            modify $ over pProgress $ M.insert (PId lbl) x
            modify $ over (modifyProps s . progress) $ M.insert lbl x

instance Scope ProgressDecl where
    merge_scopes _ _ = error "ProgressProp Scope.merge_scopes: _, _"
    clashes _ _ = True
    keep_from s x = guard (s == s') >> return x
        where
            s' = case x of (ProgressProp _ s _) -> s
    make_inherited (ProgressProp x _ y) = Just $ ProgressProp x Inherited y
    error_item (ProgressProp _ _ li) = ("progress property", li)

progress_prop :: MPipeline MachinePh2
                    [(Label,ExprScope)]
progress_prop = machineCmd "\\progress" $ \(lbl, pCt, qCt) _m p2 -> do
            (p,q)    <- toEither (do
                p    <- fromEither ztrue 
                    $ parse_expr' (machine_parser p2) 
                        { free_dummies = True }
                        pCt
                q    <- fromEither ztrue 
                    $ parse_expr' (machine_parser p2) 
                        { free_dummies = True } 
                        qCt
                return (p,q))
            let ds  = dummy_vars p2
                dum = free_vars' ds p `union` free_vars' ds q
                new_prop = LeadsTo (M.elems dum) p q
--             new_deriv <- bind (format "proof step '{0}' already exists" lbl)
--                 $ insert_new lbl (Rule Add) $ derivation $ props m
            li <- lift ask
            return [(lbl,ExprScope $ ProgressProp new_prop Local li)]

refine_prog_prop :: MPipeline MachinePh3
                [(ProgId,(Rule,[(ProgId,ProgId)]),LineInfo)]
refine_prog_prop = machineCmd "\\refine" $ \(goal, String rule, hyps, hint) m p3 -> do
        let p2   = (pEvents `over` M.map (view e2)) (p3 ^. machinePh2')
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

type EventRef = [(EventId,[((Label,ScheduleChange),LineInfo)])]

emit_event_ref :: EventId -> MachineId -> ScheduleChange -> M EventRef
emit_event_ref = emit_event_ref' "SCH"

emit_event_ref' :: Label -> EventId -> MachineId -> ScheduleChange -> M EventRef
emit_event_ref' lbl ev (MId m) sch = do
    let po_lbl = composite_label [lbl,label m]            
    li <- lift ask
    return [(ev,[((po_lbl,sch),li)])]

ref_replace_csched :: MPipeline MachinePh3 EventRef
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
        let rule = (replace evt_lbl (as_label prog,pprop) (saf,sprop)) 
                        { remove = del
                        , add = add
                        , keep = keep }
        emit_event_ref evt m rule

ref_weaken_csched :: MPipeline MachinePh3 EventRef
ref_weaken_csched = machineCmd "\\weakento" $ \(evt_lbl,del,add) m p3 -> do
        let _ = evt_lbl :: Label
            _ = del :: S.Set Label
            _ = add :: S.Set Label
            rule   = (weaken evt_lbl)
                        { remove = del
                        , add = add }
        evt <- get_event p3 evt_lbl
        emit_event_ref evt m rule


ref_replace_fsched :: MPipeline MachinePh3 EventRef
ref_replace_fsched = machineCmd "\\replacefine" $ \(evt_lbl,old,new,prog) m p3 -> do
        evt <- get_event p3 evt_lbl
        sc  <- get_schedules p3 evt
        old_exp <- bind
            (format "'{0}' is not a valid schedule" $ MM.fromJust old)
            $ maybe (Just ztrue) (`M.lookup` sc) old
        new_exp <- bind 
            (format "'{0}' is not a valid schedule" $ MM.fromJust new)
            $ maybe (Just ztrue) (`M.lookup` sc) new
        pprop <- case prog of
            Just prog -> do
                pprop <- get_progress_prop p3 m prog
                return $ Just (prog,pprop)
            Nothing -> return Nothing
        let rule      = (replace_fine evt_lbl old_exp new new_exp $ fmap (first as_label) pprop)
        emit_event_ref evt m rule

ref_remove_guard :: MPipeline MachinePh3 EventRef
ref_remove_guard = machineCmd "\\removeguard" $ \(evt_lbl,lbls) m p3 -> do
        evt  <- get_event p3 evt_lbl
        grds <- get_guards p3 evt
        _ <- bind_all lbls (format "'{0}' is not a valid guard") 
            (`M.lookup` grds)
        let rules     = map (AST.remove_guard evt_lbl) lbls
        liftM concat 
            $ forM rules 
            $ emit_event_ref' "GRD" evt m

all_comments :: MPipeline MachinePh3 [(DocItem, String, LineInfo)]
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

all_proofs :: MPipeline MachinePh3 [(Label,Tactic Proof,LineInfo)]
all_proofs = machineEnv "proof" $ \(One po) xs m p3 -> do
        li <- lift ask
        let notation = get_notation p3
            po_lbl = label $ remove_ref $ concatMap flatten po
            lbl = composite_label [ as_label m, po_lbl ]
        proof <- mapEitherT 
            (\cmd -> runReaderT cmd notation) 
            $ run_visitor li xs collect_proof_step 
        return [(lbl,proof,li)]







