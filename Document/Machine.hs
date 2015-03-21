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
import           Control.Monad.Writer.Class 
import qualified Control.Monad.Reader as R
import           Control.Monad.Trans
import           Control.Monad.Trans.Either
import           Control.Monad.Trans.Reader ( runReaderT )
import           Control.Monad.Trans.RWS as RWS ( RWS, RWST, mapRWST )
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
            (L.map $ second make_inherited)
            (++)

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
        -- _pNewEvents = M.map fst $ M.filter ((== Local) . snd) evts

run_phase2_vars :: Pipeline MM 
                        (Hierarchy MachineId,MTable MachinePh1)
                        (MTable MachinePh2)
run_phase2_vars = proc (r_ord, p1) -> do
    v <- variable_decl -< p1
    c <- constant_decl -< p1
    d <- dummy_decl -< p1
    ind <- index_decl -< p1
    par <- param_decl -< p1
    let s = Right $ M.map (L.view pSetDecl) p1
        vars    = do
            vs <- all_errors' [v,c,d,ind,par,s]
            make_all_tables' (format "Multiple symbols with the name {0}") 
                    $ inherit2 r_ord $ unionsWith (++) vs
                        
    One vars <- triggerP -< One vars
    let p2 = make_phase2 <$> p1 <.> vars
        _  = vars :: MTable (Map String VarScope)
    returnA -< p2

make_phase2 :: MachinePh1
            -- -> Map String Sort
            -- -> Map String (Theory,LineInfo)
            -- -> Map Label EventId
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
        _pMchSynt   = mkSetting _pNotation types constants _pStateVars _pDummyVars
        
        findE m e = findWithDefault M.empty e m :: Map String Var

        f :: Map EventId (Map String Var)
          -> EventId -> ParserSetting
        f table e    = mkSetting _pNotation types (constants `union` findE table e) _pStateVars _pDummyVars
        
        event_namespace table = -- (fromList . map (f table) . M.elems) 
            M.mapWithKey (const . f table) evts 

        _pSchSynt :: Map EventId ParserSetting
        _pSchSynt = event_namespace _pIndices

        _pEvtSynt :: Map EventId ParserSetting
        _pEvtSynt = event_namespace ind_param

run_phase3_exprs :: Pipeline MM (Hierarchy MachineId,MTable MachinePh2) (MTable MachinePh3)
run_phase3_exprs = proc (r_ord,p2) -> do
        ba    <- assignment -< p2
        beq   <- bcmeq_assgn -< p2
        bsuch <- bcmsuch_assgn -< p2
        bin   <- bcmin_assgn -< p2
        grd   <- guard_decl -< p2
        fs    <- fine_sch_decl -< p2
        cs    <- coarse_sch_decl -< p2
        init  <- initialization -< p2
        asm   <- assumption -< p2
        inv   <- invariant  -< p2
        tr    <- transient_prop -< p2
        tr'   <- transientB_prop -< p2
        co    <- constraint_prop -< p2
        prog  <- progress_prop   -< p2
        saf   <- safetyA_prop  -< p2
        saf'  <- safetyB_prop  -< p2
        let li = LI "default" 1 1
            default_sch e = ( label "default",
                              EventExpr 
                                $ singleton e (CoarseSchedule zfalse,Inherited,li))
            exprs = do
                es <- all_errors' 
                    [ ba,beq,bsuch,bin
                    , grd,fs,cs,init
                    , asm,tr,inv,tr'
                    , co,prog,saf,saf'
                    , Right $ M.map (map default_sch . elems . M.map (^. pEventId)) 
                            $ M.map (M.filter (^. pIsNew) . (^. pEvents)) p2 ]
                make_all_tables' (format "Multiple expressions with the label {0}") 
                    $ inherit2 r_ord $ unionsWith (++) es
                        
        One exprs <- triggerP -< One exprs
        let p3 = make_phase3 <$> p2 <.> exprs
        returnA -< p3

old :: Scope s => Map a s -> Map a s
old = M.mapMaybe is_inherited

new :: Scope s => Map a s -> Map a s
new = M.mapMaybe is_local

make_phase3 :: MachinePh2 -> Map Label ExprScope -> MachinePh3
make_phase3 p2 exprs = MachinePh3 { .. }
    where
        _e2 = EventPh3 <$> (p2 ^. pEvents) 
                       <.> _pCoarseSched  `M.union` evtEmpty
                       <.> _pFineSched    `M.union` evtEmpty
                       <.> _pOldGuards    `M.union` evtEmpty
                       <.> _pNewGuards    `M.union` evtEmpty
                       <.> _pOldActions   `M.union` evtEmpty
                       <.> _pAllActions   `M.union` evtEmpty
        evtEmpty :: Map EventId (Map k a)
        evtEmpty = M.map (const M.empty) (p2 ^. pEvents)
        _p2 = p2 & pEvents .~ _e2 -- (pEvents `over` M.map EventPh3) p2 
        _pProgress = M.mapKeys PId $ M.mapMaybe getProgressProp exprs
        _pSafety   = M.mapMaybe getSafetyProp exprs
        _pTransient   = M.mapMaybe get_transient exprs
        _pAssumptions = M.mapMaybe getAssump exprs
        _pInvariant   = M.mapMaybe getInvariant exprs
        _pInit        = M.mapMaybe getInits exprs
        _pCoarseSched = getEventCoarseSch evts exprs 
        _pFineSched   = getEventFineSch evts exprs
        _pOldGuards   = getEventGuards evts $ old exprs
        _pNewGuards   = getEventGuards evts $ new exprs
        _pAllActions  = getEventActions evts exprs
        _pOldActions  = getEventActions evts $ old exprs
        _pOldPropSet  = get_prop_set $ old exprs
        _pNewPropSet  = get_prop_set $ new exprs
        evts   = machine_events p2

run_phase4_proofs :: Pipeline MM (Hierarchy MachineId,MTable MachinePh3) (MTable MachinePh4)
run_phase4_proofs = proc (r_ord,p3) -> do
        ref_p  <- refine_prog_prop -< p3
        rep_c  <- ref_replace_csched -< p3
        wk_c   <- ref_weaken_csched  -< p3
        rep_f  <- ref_replace_fsched -< p3
        rem_g  <- ref_remove_guard   -< p3
        comm   <- all_comments -< p3
        prfs   <- all_proofs   -< p3
        let evt_refs :: Either [Error] (MTable (Map EventId [((Label,ScheduleChange),LineInfo)]))
            evt_refs = do
                    refs <- all_errors' [rep_c,wk_c,rep_f,rem_g] 
                    return $ M.map (fromListWith (++)) $ unionsWith (++) refs
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
        -- _pEvtRef :: Abs EventId <-> Conc EventId
        -- _pEvtRef      = _
        -- _pEvtRefProgA :: Abs EventId <-> Abs Label
        -- _pEvtRefProgA = _
        -- _pEvtRefProgC :: Abs EventId <-> Conc Label
        -- _pEvtRefProgC = _
        -- _pLiveProof   :: ProgId  <-> ProgId
        -- _pLiveProof   = _ -- R.fromList prog_dep
        -- _pLiveImplA   :: Abs Label  <-> Abs EventId
        -- _pLiveImplA   = _
        -- _pLiveImplC   :: Conc Label <-> Conc EventId
        -- _pLiveImplC   = _

        -- prog_ref' :: Map ProgId (Rule,LineInfo)
        -- prog_ref' = M.map (first fst) prog_ref
        -- prog_dep :: [(Label,Label)]
        -- prog_dep = -- unionWith (++) 
        --         concatMap (snd . fst) (elems prog_ref)
        --         ++
        --         ( do
        --             (evt,ps) <- toList evt_refs
        --             (_,refs) <- liftM fst ps
        --             prog     <- hyps_labels refs
        --             return (as_label evt,prog))

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
            , inits = p4 ^. pInit
            , props = props 
            , derivation = (ref_prog 
                    `union` M.mapKeys evt_grd_po (uncurryMap $ M.mapWithKey (\k -> M.mapWithKey $ \l _ -> Rule (add_guard (as_label k) l)) (p4 ^. pNewGuards))
                    -- `union` M.fromList (L.map (rule_name &&& id) $ concat $ elems $ M.map (L.map Rule . sched_ref) evts)
                    `union` M.map (const $ Rule Add) (progress props)) 
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
        -- adep :: Abs EventId <-> Abs Label
        -- adep = p4 ^. pEvtRefProgA
        -- cdep :: Conc EventId <-> Conc Label
        -- cdep = p4 ^. pEvt
        -- live :: Conc Label <-> Conc Label
        -- live = R.closure $ R.bimap Conc Conc _
        -- eref :: Conc EventId <-> Abs EventId
        -- eref = R.bimap Conc Abs $ R.identity _
        -- pref_a :: Abs Label <-> Abs EventId
        -- pref_a = R.bimap Abs Abs _
        -- pref_c :: Conc Label <-> Abs EventId
        -- pref_c = R.bimap Conc Abs _
        -- cdep' :: Conc EventId <-> Label
        -- cdep' =           R.mapRange getAbstract (R.compose eref adep)
        --         `R.union` R.mapRange getConcrete (R.compose cdep live)
        --         `R.union` R.mapRange getConcrete cdep

        -- problems = R.cycles $ (adep `R.compose` pref_a :: Abs EventId <-> Abs EventId)

        pos = raw_machine_pos mch
        po_err = proofs `difference` pos
        mch' = do
            -- po_err here
            all_errors' $ flip map (toList po_err) $ \(lbl,(_,li)) -> 
                Left [Error (format "proof obligation does not exist: {0}" lbl) li]
            xs <- all_errors' $ flip map (toList proofs) $ \(k,(tac,li)) -> do
                p <- runTactic li (pos ! k) tac
                return (k,p)
            return mch 
                { AST.props = (AST.props mch) 
                    { proofs = fromList xs } }
        evtr2der :: EventId -> [(Label,ScheduleChange)] -> [(Label,Rule)]
        evtr2der (EventId evt) xs = zipWith f xs [0..]
            where
                f (lbl,ref) n = (composite_label [evt,lbl,label $ show n], Rule ref)
        -- old_guards = getEventGuards evtSet $ old exprs
        -- new_guards = getEventGuards evtSet $ new exprs
        -- old_actions = getEventActions evtSet $ old exprs
        -- actions = getEventActions evtSet exprs

        -- c_sched = getEventCoarseSch evtSet exprs
        -- f_sched = getEventFineSch evtSet exprs
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
                , old_guard = evt ^. eOldGuards
                , actions = evt ^. eAllActions
                , scheds  = c_sched `union` f_sched
                , eql_vars = keep' ab_var (evt ^. eOldActions)
                             `S.intersection` frame (evt ^. eAllActions)
                , old_sched = Schedule 
                                    { coarse = c_sched `M.intersection` old_sched
                                    , fine   = MM.listToMaybe $ M.toList $ f_sched `M.intersection` old_sched }
                -- , old_guard = _
                , sched_ref =  map (add_guard name) (keys $ evt ^. eNewGuards) 
                            ++ map snd (evt ^. eRefRule)
                , old_acts = M.keysSet $ evt ^. eOldActions
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


-- traceP :: Show a => String -> Pipeline MM a ()
-- traceP m = Pipeline empty_spec empty_spec $ traceM . format "{0}: {1}" m


get_prop_set :: Map Label ExprScope -> PropertySet
get_prop_set m = PS
    { transient = M.mapMaybe get_transient m
    , inv = M.mapMaybe getInvariant m
    , constraint = M.mapMaybe getConstraint m
    , inv_thm = M.empty
    , progress = M.mapMaybe getProgressProp m
    , safety = M.mapMaybe getSafetyProp m
    , proofs = M.empty
    }

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


getAssump :: ExprScope -> Maybe Expr
getAssump (Axiom e _ _) = Just e
getAssump _ = Nothing

getInits :: ExprScope -> Maybe Expr
getInits (Initially e _ _) = Just e
getInits _ = Nothing

getEventExprs :: ((EvtExprScope, DeclSource, LineInfo) -> Maybe a) 
              -> Map Label EventId
              -> Map Label ExprScope
              -> Map EventId (Map Label a)
getEventExprs f evts exprs = M.map M.fromList $ M.unionsWith (++) $ empty : map swapName guards
    where
        empty  = M.fromList $ zip (elems evts) (repeat [])
        guards = M.toList (M.mapMaybe getExprs exprs)
        swapName (lbl,m) = M.map (\e -> [(lbl,e)]) m
        -- getExprs :: ExprScope -> Maybe (Map EventId Expr)
        getExprs (EventExpr m) = Just $ M.mapMaybe f m
        getExprs _ = Nothing

getGuard :: (EvtExprScope,DeclSource,LineInfo) -> Maybe Expr
getGuard (Guard g,_,_) = Just g
getGuard (_,_,_) = Nothing

getEventGuards :: Map Label EventId
               -> Map Label ExprScope
               -> Map EventId (Map Label Expr)
getEventGuards = getEventExprs getGuard

getAction :: (EvtExprScope,DeclSource,LineInfo) -> Maybe Action
getAction (Action act,_,_) = Just act
getAction _ = Nothing

getEventActions :: Map Label EventId
                -> Map Label ExprScope
                -> Map EventId (Map Label Action)
getEventActions = getEventExprs getAction

getCoarseSch :: (EvtExprScope,DeclSource,LineInfo) -> Maybe Expr
getCoarseSch (CoarseSchedule sch,_,_) = Just sch
getCoarseSch _ = Nothing

getEventCoarseSch :: Map Label EventId
                  -> Map Label ExprScope 
                  -> Map EventId (Map Label Expr)
getEventCoarseSch = getEventExprs getCoarseSch

getFineSch :: (EvtExprScope,DeclSource,LineInfo) -> Maybe Expr
getFineSch (FineSchedule sch,_,_) = Just sch
getFineSch _ = Nothing

getEventFineSch :: Map Label EventId
                -> Map Label ExprScope 
                -> Map EventId (Map Label Expr)
getEventFineSch = getEventExprs getFineSch

get_transient :: ExprScope -> Maybe Transient
get_transient (TransientProp tr _ _) = Just tr
get_transient _ = Nothing

getInvariant :: ExprScope -> Maybe Expr
getInvariant (Invariant inv _ _) = Just inv
getInvariant _ = Nothing

getConstraint :: ExprScope -> Maybe Constraint
getConstraint (ConstraintProp co _ _) = Just co
getConstraint _ = Nothing

getSafetyProp :: ExprScope -> Maybe SafetyProp
getSafetyProp (SafetyProp prop _ _) = Just prop
getSafetyProp _ = Nothing

getProgressProp :: ExprScope -> Maybe ProgressProp
getProgressProp (ProgressProp prop _ _) = Just prop
getProgressProp _ = Nothing

getStateVars :: VarScope -> Maybe (Var,LineInfo)
getStateVars (Machine v _ li) = Just (v,li)
getStateVars _ = Nothing

getAbsVars :: VarScope -> Maybe (Var,LineInfo)
getAbsVars (Machine v Inherited li) = Just (v,li)
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
            return [(lbl,EventExpr $ M.singleton ev $ (Action act,Local,li))]

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
            return [(lbl,EventExpr $ M.singleton ev $ (Action act,Local,li))]

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
            return [(lbl,EventExpr $ M.singleton ev $ (Action act,Local,li))]

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
            return [(lbl,EventExpr $ M.singleton ev $ (Action act,Local,li))]

guard_decl :: MPipeline MachinePh2
                    [(Label,ExprScope)]
guard_decl = machineCmd "\\evguard" $ \(evt, lbl, xs) _m p2 -> do
            ev <- get_event p2 evt
            xp <- parse_expr' (event_parser p2 ev) xs
            li <- lift ask
            return [(lbl,EventExpr $ M.singleton ev $ (Guard xp,Local,li))]
 
coarse_sch_decl :: MPipeline MachinePh2
                    [(Label,ExprScope)]
coarse_sch_decl = machineCmd "\\cschedule" $ \(evt, lbl, xs) _m p2 -> do
            ev <- get_event p2 evt
            xp <- parse_expr' (schedule_parser p2 ev) xs
            li <- lift ask
            return [(lbl,EventExpr $ M.singleton ev $ (CoarseSchedule xp,Local,li))]

fine_sch_decl :: MPipeline MachinePh2
                    [(Label,ExprScope)]
fine_sch_decl = machineCmd "\\fschedule" $ \(evt, lbl, xs) _m p2 -> do
            ev <- get_event p2 evt
            xp <- parse_expr' (schedule_parser p2 ev) xs
            li <- lift ask
            return [(lbl,EventExpr $ M.singleton ev $ (FineSchedule xp,Local,li))]

        -------------------------
        --  Theory Properties  --
        -------------------------

assumption :: MPipeline MachinePh2
                    [(Label,ExprScope)]
assumption = machineCmd "\\assumption" $ \(lbl,xs) _m p2 -> do
            xp <- parse_expr' (context_parser p2) xs
            li <- lift ask
            return [(lbl,Axiom xp Local li)]

        --------------------------
        --  Program properties  --
        --------------------------

initialization :: MPipeline MachinePh2
                    [(Label,ExprScope)]
initialization = machineCmd "\\initialization" $ \(lbl,xs) _m p2 -> do
            xp <- parse_expr' (machine_parser p2) xs
            li <- lift ask
            return [(lbl,Initially xp Local li)]

invariant :: MPipeline MachinePh2
                    [(Label,ExprScope)]
invariant = machineCmd "\\invariant" $ \(lbl,xs) _m p2 -> do
            xp <- parse_expr' (machine_parser p2) xs
            li <- lift ask
            return [(lbl,Invariant xp Local li)]

transient_prop :: MPipeline MachinePh2
                    [(Label,ExprScope)]
transient_prop = machineCmd "\\transient" $ \(evts, lbl, xs) _m p2 -> do
            _evs <- get_events p2 evts
            tr   <- parse_expr' (machine_parser p2) 
                    { free_dummies = True } xs
            let vs = symbol_table $ S.elems $ used_var tr
                fv = vs `M.intersection` dummy_vars p2
                prop = Transient fv tr evts empty_hint
            li <- lift ask
            return [(lbl,TransientProp prop Local li)]

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
            return [(lbl,TransientProp prop Local li)]

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
            return [(lbl,ConstraintProp prop Local li)]


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
            return [(lbl,SafetyProp new_prop Local li)]

safetyA_prop :: MPipeline MachinePh2
                    [(Label,ExprScope)]
safetyA_prop = machineCmd "\\safety" 
                $ \(lbl, pCt, qCt) -> safety_prop lbl Nothing pCt qCt

safetyB_prop :: MPipeline MachinePh2
                    [(Label,ExprScope)]
safetyB_prop = machineCmd "\\safetyB" 
                $ \(lbl, evt, pCt, qCt) -> safety_prop lbl evt pCt qCt

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
            return [(lbl,ProgressProp new_prop Local li)]

    -- Todo: report an error if we create two assignments (or other events 
    -- elements)
    -- with the same name
    -- Todo: guard the `insert` statements with checks for name clashes
    -- Todo: check scopes

-- data ProgRefScope = ProgPropRef Rule [(Label,Label)]

-- data EventRefScope = EventRefScope ScheduleChange

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

--                     toEither $ error_list
--                         [   ( not (goal `member` (progress (props m) `union` progress (inh_props m)))
--                             , format "the goal is an undefined progress property {0}" goal )
--                         ]
--                     let prog = progress (props m) `union` progress (inh_props m)
--                         saf  = safety (props m) `union` safety (inh_props m)
--                         rem_add ref
--                             | ref == Rule Add = Nothing
--                             | otherwise       = Just ref
--                     r <- parse_rule' (map toLower rule) 
--                         (RuleParserParameter m prog saf goal hyps hint)
--                     new_der <- bind 
--                         (format "progress property {0} already has a refinement" goal)
--                         (insert_new goal r $ update rem_add goal $ derivation $ props m)
--                     return m { props = (props m) { derivation = new_der } } 
--             )

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

--                     old_event <- bind
--                         (format "event '{0}' is undeclared" evt)
--                         $ evt `M.lookup` events m
--                     let grd       = guards old_event
--                     toEither $ do
--                         error_list $ flip map lbls $ \lbl ->
--                             ( not $ lbl `member` grd
--                                 , format "'{0}' is not a valid schedule" lbl )
--                     let n         = length $ sched_ref old_event
--                         rules     = map (remove_guard evt) lbls
--                         new_event = old_event 
--                                     { sched_ref = rules ++ sched_ref old_event }
--                         po_lbl    = flip map [n .. ] $ \n -> 
--                                     composite_label [evt,label "GRD",_name m,label $ show n]
--                     return m 
--                       { events = insert evt new_event $ events m
--                       , props = (props m) { 
--                             derivation = 
--                                      M.fromList (zip po_lbl $ map Rule rules)
--                             `union`  derivation (props m) } 
--                       }
--             )


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







