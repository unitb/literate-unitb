{-# LANGUAGE BangPatterns, FlexibleContexts     #-}
{-# LANGUAGE TupleSections, ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances, Arrows          #-}
{-# LANGUAGE TypeOperators, TypeFamilies        #-}
{-# LANGUAGE MultiParamTypeClasses              #-}
{-# LANGUAGE TemplateHaskell                    #-}
{-# LANGUAGE RecordWildCards                    #-}
module Document.Machine where

    --
    -- Modules
    --
import Document.Context
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
import Control.Parallel.Strategies

import Control.Arrow hiding (left,app) -- (Arrow,arr,(>>>))

import           Control.Monad 
import           Control.Monad.State.Class 
import           Control.Monad.Reader.Class 
import           Control.Monad.Writer.Class 
import qualified Control.Monad.Reader as R
import           Control.Monad.Trans
import           Control.Monad.Trans.Either
import qualified Control.Monad.Trans.State as ST
import           Control.Monad.Trans.Reader ( runReaderT )
import           Control.Monad.Trans.RWS as RWS ( RWS, RWST, mapRWST, runRWS )
import qualified Control.Monad.Writer as W

import Control.Lens as L (view,(^.))
-- import Control.Lens.TH

import           Data.Char
import           Data.Either
import           Data.Either.Combinators
import           Data.Functor
import           Data.Functor.Identity
import           Data.Graph
import           Data.Map   as M hiding ( map, foldl, (\\) )
import qualified Data.Map   as M
import           Data.Maybe as M ( maybeToList, isJust, isNothing ) 
import qualified Data.Maybe as MM
import           Data.Monoid
import           Data.List as L hiding ( union, insert, inits )
import           Data.List.NonEmpty ( NonEmpty(..) )
import qualified Data.List.NonEmpty as NE
import           Data.List.Ordered (sortOn)
import qualified Data.Set as S

import Utilities.Error
import Utilities.Format
import Utilities.Permutation hiding (cycles)
import Utilities.Relation (type(<->),(|>),(<|))
import qualified Utilities.Relation as R
import Utilities.Syntactic
import Utilities.Trace

default (Int)

list_file_obligations :: FilePath
                       -> IO (Either [Error] [(Machine, Map Label Sequent)])
list_file_obligations fn = do
        runEitherT $ list_proof_obligations fn

list_proof_obligations :: FilePath
                       -> EitherT [Error] IO [(Machine, Map Label Sequent)]
list_proof_obligations fn = do
        xs <- list_machines fn
        hoistEither $ forM xs $ \x -> do
            y <- proof_obligation x
            return (x,y)

list_machines :: FilePath
              -> EitherT [Error] IO [Machine]
list_machines fn = do
        xs <- EitherT $ parse_latex_document fn
        ms <- hoistEither $ all_machines xs
        return $ map snd $ toList $ machines ms
        
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
        HintBuilder [LatexDoc] Machine
        | HintBuilderDecl [LatexDoc] MachineId Phase2

ensure :: ProgressProp 
       -> HintBuilder
       -> [Label]
       -> ERWS Ensure
ensure prog@(LeadsTo fv _ _) hint lbls = do
        let vs = symbol_table fv
        lbls' <- bind  "Expected non empty list of events"
                    $ NE.nonEmpty lbls
        hint <- case hint of
            HintBuilder thint m -> do
                hint <- toEither $ tr_hint m vs lbls thint empty_hint
                _    <- bind_all lbls
                    (format "event {0} is undeclared") 
                    (`M.lookup` events m)
                return hint
            HintBuilderDecl thint m p2 -> do
                hint <- toEither $ tr_hint' p2 m vs lbls' thint empty_hint
                _    <- get_events p2 lbls
                return hint
        return $ Ensure prog lbls hint

instance RuleParser (a,()) => RuleParser (HintBuilder -> a,()) where
    parse_rule (f,_) xs rule param@(RuleParserParameter m _ _ _ _ hint) = do
        parse_rule (f (HintBuilder hint m),()) xs rule param
    parse_rule (f,_) xs rule param@(RuleParserDecl p2 m _ _ _ _ _ hint _) = do
        parse_rule (f (HintBuilderDecl hint m p2),()) xs rule param

check_acyclic :: (Monad m) => String 
              -> [(Label,Label)] 
              -> LineInfo
              -> EitherT [Error] (RWST b [Error] d m) ()
check_acyclic x es li = do
        let cs = cycles es
        toEither $ mapM_ (cycl_err_msg x) cs
    where
        cycle_msg x ys = format msg (x :: String) $ intercalate ", " (map show ys)
        cycl_err_msg _ (AcyclicSCC _) = return ()
        cycl_err_msg x (CyclicSCC vs) = tell [Error (cycle_msg x vs) li]
        msg = "A cycle exists in the {0}: {1}"

trickle_down
        :: (Machine -> Machine -> Either [String] Machine) 
        -> LineInfo
        -> M ()
trickle_down f li = do
            ms   <- lift $ gets machines
            refs <- lift $ gets ref_struct
            let g (AcyclicSCC v) = v
                g (CyclicSCC _)  = error "trickle_down: the input graph should be acyclic"
                rs = map g $ cycles $ toList refs
            ms <- foldM (\ms n -> 
                    case M.lookup n refs of
                        Just anc  -> do
                            m <- hoistEither $ either 
                                (Left . map (\x -> Error x li)) Right 
                                $ f (ms ! show n) (ms ! show anc)
                            return $ insert (show n) m ms
                        Nothing -> return ms
                    ) ms rs
            lift $ modify $ \s -> s
                { machines = ms }

topological_order :: Pipeline MM
                     [(MachineId,MachineId)] 
                     (Hierarchy MachineId)
topological_order = Pipeline empty_spec empty_spec $ \es -> do
        let cs = cycles es
        vs <- lift $ toEither $ mapM cycl_err_msg cs
        return $ Hierarchy vs $ M.fromList es
    where
        struct = "refinement structure"
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

abstract :: Ord k => Hierarchy k -> a -> Map k a -> Map k a
abstract (Hierarchy _ m') def m = M.mapWithKey f m
    where
        f k _ = M.findWithDefault def (M.findWithDefault k k m') m

all_machines :: [LatexDoc] -> Either [Error] System
all_machines xs = do
        cmd
        return s
    where
        (cmd,s,_) = runRWS (runEitherT $ read_document xs) li empty_system
        li = LI "" 1 1 

data MachineTag = MTag String LineInfo [LatexDoc] LineInfo

data ContextTag = CTag String LineInfo [LatexDoc] LineInfo

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

all_contents :: [MachineTag] -> [LatexDoc]
all_contents xs = concatMap f xs
    where
        f (MTag _ _ xs _) = xs

data Input = Input 
    { getMachineInput :: M.Map MachineId DocBlocks
    , getContextInput :: M.Map ContextId DocBlocks
    }

run_phase1_types :: Pipeline MM 
                        (MTable Phase0)
                        ( Hierarchy MachineId
                        -- , Either [Error] (MTable (Map String Def))
                        , MTable Phase1)
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
        p1 = make_phase1 <$> p0 .> imp_th 
                          .> (M.map (M.map fst) types) .> all_types 
                          .> s .> evts'
    -- traceP -< imp_th
    -- traceP -< all_types
    -- traceP -< s
    -- traceP -< evts'
    -- traceP -< p0
    -- traceP -< it
    returnA -< (r_ord,p1)

make_phase1 :: Phase0
            -> Map String Theory
            -> Map String Sort
            -> Map String Sort
            -> [(String, VarScope)]
            -> Map Label (EventId, DeclSource)
            -> Phase1
make_phase1 _p0 _pImports _pTypes _pAllTypes _pSetDecl evts = Phase1 { .. }
    where
        _pEvents    = M.map fst evts
        _pNewEvents = M.map fst $ M.filter ((== Local) . snd) evts

run_phase2_vars :: Pipeline MM 
                        (Hierarchy MachineId,MTable Phase1)
                        (MTable Phase2)
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
    let p2 = make_phase2 <$> p1 .> vars
        _  = vars :: MTable (Map String VarScope)
    returnA -< p2

make_phase2 :: Phase1
            -- -> Map String Sort
            -- -> Map String (Theory,LineInfo)
            -- -> Map Label EventId
            -> Map String VarScope
            -> Phase2 
make_phase2 _p1 vars = Phase2 { .. }
    where
        types = _p1 ^. pTypes 
        imps  = _p1 ^. pImports
        evts  = _p1 ^. pEvents
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
          -> EventId -> (EventId, ParserSetting)
        f table e    = (e, mkSetting _pNotation types (_pConstants `union` findE table e) _pStateVars _pDummyVars)
        
        event_namespace table = (fromList . map (f table) . M.elems) evts 

        _pSchSynt :: Map EventId ParserSetting
        _pSchSynt = event_namespace _pIndices

        _pEvtSynt :: Map EventId ParserSetting
        _pEvtSynt = event_namespace ind_param

run_phase3_exprs :: Pipeline MM (Hierarchy MachineId,MTable Phase2) (MTable Phase3)
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
                    , Right $ M.map (map default_sch . elems) 
                            $ M.map (^. pNewEvents) p2 ]
                make_all_tables' (format "Multiple expressions with the label {0}") 
                    $ inherit2 r_ord $ unionsWith (++) es
                        
        One exprs <- triggerP -< One exprs
        let p3 = make_phase3 <$> p2 .> exprs
        returnA -< p3

old :: Scope s => Map a s -> Map a s
old = M.mapMaybe is_inherited

new :: Scope s => Map a s -> Map a s
new = M.mapMaybe is_local

make_phase3 :: Phase2 -> Map Label ExprScope -> Phase3
make_phase3 p2 exprs = Phase3 { .. }
    where
        _p2 = p2 
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

run_phase4_proofs :: Pipeline MM (Hierarchy MachineId,MTable Phase3) (MTable Phase4)
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
            live_struct = LiveStruct <$> (M.map (view pMachineId) p3) .> evt_live .> live_live 
                    .> live_evt .> evt_evt 
                    .> M.mapWithKey (\k -> M.map (k,)) (M.map (M.map snd) prog_ref) 
                    .> M.mapWithKey (\k -> M.map (k,)) (M.map (uncurryMap . M.map (M.fromList . concatMap hyps_table)) evt_refs)
            struct = all_errors $ 
                     M.map raiseStructError $ inheritWith 
                        Conc (Abs . getConcrete)
                        mergeLiveness 
                        r_ord live_struct
                    -- >>= make_all_tables' _
        One struct <- triggerP -< One struct
        let p4 = make_phase4 <$> p3 .> evt_refs .> prog_ref .> comments .> proofs .> struct
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
        -- f x = trace (format "liveness structure {0}\n{1}" (live_live x) (live_evt x)) x
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

make_phase4 :: Phase3 
            -> Map EventId [((Label, ScheduleChange), LineInfo)]
            -> Map ProgId ((Rule,[(ProgId,ProgId)]),LineInfo) 
            -> Map DocItem (String,LineInfo)
            -> Map Label (Tactic Proof, LineInfo) 
            -> LiveStruct
            -> Phase4
make_phase4 p3 evt_refs prog_ref comments proofs _ = Phase4 { .. }
    where
        _p3 = p3
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

make_machine :: MachineId -> Phase4
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
                    { derivation = (ref_prog 
                            `union` M.mapKeys evt_grd_po (uncurryMap $ M.mapWithKey (\k -> M.mapWithKey $ \l _ -> Rule (add_guard (as_label k) l)) (p4 ^. pNewGuards))
                            -- `union` M.fromList (L.map (rule_name &&& id) $ concat $ elems $ M.map (L.map Rule . sched_ref) evts)
                            `union` M.map (const $ Rule Add) (progress props)) 
                            `union` fromList (concat $ elems $ M.mapWithKey evtr2der evt_refs)
                    }
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
        ind :: Map EventId (Map String Var)
        ind  = p4 ^. pIndices
        param :: Map EventId (Map String Var)
        param   = p4 ^. pParams
        guard   = p4 ^. pGuards
        old_guards :: Map EventId (Map Label Expr)
        -- old_guards = getEventGuards evtSet $ old exprs
        old_guards = p4 ^. pOldGuards
        new_guards :: Map EventId (Map Label Expr)
        -- new_guards = getEventGuards evtSet $ new exprs
        new_guards = p4 ^. pNewGuards 
        old_actions = p4 ^. pOldActions
        -- old_actions = getEventActions evtSet $ old exprs
        -- actions = getEventActions evtSet exprs
        actions = p4 ^. pAllActions

        c_sched = p4 ^. pCoarseSched
        -- c_sched = getEventCoarseSch evtSet exprs
        f_sched = p4 ^. pFineSched
        -- f_sched = getEventFineSch evtSet exprs
        events = M.fromList $ L.map ((id &&& const ()) . snd) $ M.toList (p4 ^. pEvents) 
        evts = M.mapWithKey g events 
                .> ind .> param 
                .> new_guards .> old_guards .> guard
                .> c_sched .> f_sched 
                .> old_actions .> actions 
                .> evt_refs
                :: Map EventId Event
        g :: EventId -> ()
          -> Map String Var 
          -> Map String Var
          -> Map Label Expr
          -> Map Label Expr
          -> Map Label Expr
          -> Map Label Expr
          -> Map Label Expr
          -> Map Label Action
          -> Map Label Action
          -> [(Label,ScheduleChange)]
          -> Event
        g (EventId name) () ind param 
                    new_guards old_guards guards 
                    c_sched f_sched 
                    old_actions actions evt_refs 
            = empty_event
                { indices = ind
                , params  = param
                , guards  = guards
                , actions = actions
                , scheds  = c_sched `union` f_sched
                , sched_ref =  map (add_guard name) (keys new_guards) 
                            ++ map snd evt_refs
                , old_acts = M.keysSet old_actions
                , old_guard = old_guards
                -- , old_guard = _
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

type MM = R.ReaderT Input M

traceP :: Show a => Pipeline MM a ()
traceP = Pipeline empty_spec empty_spec $ traceM . show

read_document :: [LatexDoc] -> M ()
read_document xs = bimapEitherT (sortOn line_info . shrink_error_list) id $ do
            let li = line_info xs
            (ms,cs) <- hoistEither $ get_components xs li
            ms <- runPipeline' ms cs $ proc doc -> do
                let mch = M.map (const ()) $ getMachineInput doc
                    p0 = M.mapWithKey (const . Phase0 mch) mch
                (r_ord,p1) <- run_phase1_types -<  p0
                -- traceP -< r_ord
                -- traceP -< p1
                p2 <- run_phase2_vars   -< (r_ord, p1)
                p3 <- run_phase3_exprs  -< (r_ord, p2)
                p4 <- run_phase4_proofs -< (r_ord, p3)
                let ms = M.mapWithKey make_machine p4 :: MTable (Either [Error] Machine)
                One machines <- triggerP -< One (all_errors ms)
                -- let refs' = M.mapKeys as_label $ M.map as_label $ P.edges $ r_ord
                    -- map2maybe = fmap (as_label . fst) . (() `M.lookup`)
                --     check0 = forM_ (keys mch) $ \m -> check_schedule_ref_struct
                --                 refs' (as_label m)
                --                 _ -- (prog_dep ! m)
                --                 (events $ machines ! m)
                --                 (transient $ props $ machines ! m)
                --                 ((p4 ! m) ^. pProgress) -- exprs ! m)
                -- liftP -< toEither check0
                returnA -< machines
            lift $ modify $ \s -> s { machines = M.mapKeys (\(MId s) -> s) ms }

liftP :: Pipeline MM (M a) a
liftP = Pipeline empty_spec empty_spec lift

get_prop_set :: Map Label ExprScope -> PropertySet
get_prop_set m = PS
    { transient = M.mapMaybe get_transient m
    , inv = M.mapMaybe getInvariant m
    , constraint = M.mapMaybe getConstraint m
    , inv_thm = M.empty
    , progress = M.mapMaybe getProgressProp m
    , safety = M.mapMaybe getSafetyProp m
    , proofs = M.empty
    , derivation = M.empty
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

forEach :: WithMap k a m => ElementOf k a m -> Map k a -> m
forEach f m = M.map (const f) m `for_each` m

forEachWithKey :: WithMap k a m => (k -> ElementOf k a m) -> Map k a -> m
forEachWithKey f m = M.mapWithKey (\ k _ -> f k) m `for_each` m

getEventParams :: Map Label EventId 
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
              -> Map Label EventId
              -> Map String VarScope
              -> Map EventId (Map String Var)
getEventDecls scope evts vars = M.map fromList $ M.unionsWith (++) $ empty : map moveName (M.toList decl)
    where
        empty :: Map EventId [(String,Var)]
        empty = M.map (const []) $ mapKeys (evts !) evts
        moveName :: (String,Map EventId (Var,LineInfo)) -> Map EventId [(String,Var)]
        moveName (vn,m) = M.map (\(x,_) -> [(vn,x)]) m
        decl = M.mapMaybe (getEventDecl scope) vars

getEventIndices :: Map Label EventId 
                -> Map String VarScope 
                -> Map EventId (Map String Var)
getEventIndices = getEventDecls Index

getParamInd :: VarScope -> Maybe (Map EventId (Var,LineInfo))
getParamInd (Evt m) = Just $ fromList $ MM.mapMaybe f $ toList m
    where
        f (Just e,(v,_,_,li)) = Just (e,(v,li))
        f _ = Nothing
getParamInd _ = Nothing

getDefs :: VarScope -> Maybe Def
getDefs (TheoryDef d _ _) = Just d
getDefs _ = Nothing

getConsts :: VarScope -> Maybe Var
getConsts (TheoryConst c _ _) = Just c
getConsts _ = Nothing

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

class Trigger a where
    type RetType a :: *
    trigger' :: a -> Either [Error] (RetType a)

instance Trigger () where
    type RetType () = ()
    trigger' () = return ()

instance Trigger as => Trigger (Either [Error] a :+: as) where
    type RetType (Either [Error] a :+: as) = a :+: RetType as
    trigger' (x :+: xs) = 
            case (x, trigger' xs) of
                (Right x, Right xs) -> Right (x:+:xs)
                (x,xs) -> Left $ f x ++ f xs
        where
            f (Left xs) = xs
            f (Right _) = []

trigger :: ( IsTuple a, Trigger (TypeList a)
           , TypeList (Tuple (RetType (TypeList a)))
                      ~ RetType (TypeList a)
           , IsTuple (Tuple (RetType (TypeList a))))
        => a -> Either [Error] (Tuple (RetType (TypeList a)))
trigger x = fromTuple `liftM` trigger' (toTuple x)

triggerM :: ( IsTuple a, Trigger (TypeList a)
            ,   TypeList (Tuple (RetType (TypeList a)))
              ~ RetType (TypeList a)
            , IsTuple (Tuple (RetType (TypeList a))))
         => a -> MM (Tuple (RetType (TypeList a)))
triggerM x = lift $ hoistEither $ trigger x

triggerP :: ( IsTuple a, Trigger (TypeList a)
            ,   TypeList (Tuple (RetType (TypeList a)))
              ~ RetType (TypeList a)
            , IsTuple (Tuple (RetType (TypeList a))))
         => Pipeline MM a (Tuple (RetType (TypeList a)))
triggerP = Pipeline empty_spec empty_spec triggerM

-- trigger_errors 

type family ElementMap a :: *
type instance ElementMap (Map k ()) = ()
type instance ElementMap (Map k (x :+: xs) ) = Map k x :+: ElementMap (Map k xs)

-- type family MapOf a :: *
-- type instance MapOf [(a,b,LineInfo)] = Either [Error] (Map a b)

split_tables :: ( Arrow arr, IsTuple a
                , ElementLists (TypeList a)
                , IsTuple (Tuple (ElementMap (Map k (TypeList a))))
                ,   TypeList (Tuple (ElementMap (Map k (TypeList a))))
                  ~ ElementMap (Map k (TypeList a))) 
             => arr (Map k a) (Tuple (ElementMap (Map k (TypeList a))))
split_tables = arr $ fromTuple . split_tables' . M.map toTuple

class ElementLists a where
    split_tables' :: Map k a -> ElementMap (Map k a)

instance ElementLists () where
    split_tables' _ = ()

instance ElementLists as => ElementLists (a:+:as) where
    split_tables' m = M.map f m :+: split_tables' (M.map g m)
        where
            f (x :+: _) = x
            g (_ :+: xs) = xs

make_table' :: forall a b.
               (Ord a, Show a, Scope b) 
            => (a -> String) 
            -> [(a,b)] 
            -> Either [Error] (Map a b)
make_table' f xs = all_errors $ M.mapWithKey g ws
    where
        g k ws
                | all (\xs -> length xs <= 1) ws 
                            = Right $ foldl merge_scopes (head xs) (tail xs)
                | otherwise = Left $ map (\xs -> MLError (f k) $ map error_item xs) 
                                    $ L.filter (\xs -> length xs > 1) ws
            where
                xs = concat ws             
        zs = fromListWith (++) $ map (\(x,y) -> (x,[y])) xs
        ws :: Map a [[b]]
        ws = M.map (flip u_scc clashes) zs 

make_table :: (Ord a, Show a) 
           => (a -> String) 
           -> [(a,b,LineInfo)] 
           -> Either [Error] (Map a (b,LineInfo))
make_table f xs = returnOrFail $ fromListWith add $ map mkCell xs
    where
        mkCell (x,y,z) = (x,Right (y,z))
        sepError (x,y) = case y of
                 Left z -> Left (x,z)
                 Right (z,li) -> Right (x,(z,li))
        returnOrFail m = failIf $ map sepError $ M.toList m
        failIf xs 
            | L.null ys = return $ fromList $ rights xs
            | otherwise = Left $ map (uncurry err) ys
            where
                ys = lefts xs
        err x li = MLError (f x) (map (show x,) li)
        lis (Left xs)     = xs
        lis (Right (_,z)) = [z]
        add x y = Left $ lis x ++ lis y



make_all_tables' :: (Scope b, Show a, Ord a, Ord k) 
                 => (a -> String) 
                 -> Map k [(a,b)] 
                 -> Either [Error] (Map k (Map a b))
make_all_tables' f xs = all_errors (M.map (make_table' f) xs) `using` parTraversable rseq

make_all_tables :: (Show a, Ord a, Ord k) 
                => (a -> String)
                -> Map k [(a, b, LineInfo)] 
                -> Either [Error] (Map k (Map a (b,LineInfo)))
make_all_tables f xs = all_errors (M.map (make_table f) xs) `using` parTraversable rseq

all_errors' :: [Either [e] a] -> Either [e] [a]
all_errors' xs = do
    let es = lefts xs
    unless (L.null es)
        $ Left $ concat es
    return $ map fromRight' xs

all_errors :: Ord k => Map k (Either [e] a) -> Either [e] (Map k a)
all_errors m = do
        let es = lefts $ M.elems m
        unless (L.null es)
            $ Left $ concat es
        return $ M.map fromRight' m

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

instance Readable MachineId where
    read_one = do
        xs <- read_one
        return $ MId $ show (xs :: Label)
    read_args = do
        xs <- read_args
        return $ MId $ show (xs :: Label)

instance Readable ProgId where
    read_one  = liftM PId read_one
    read_args = liftM PId read_args
        
instance Readable (Maybe ProgId) where
    read_one  = liftM (fmap PId) read_one
    read_args = liftM (fmap PId) read_args

cmdSpec :: String -> Int -> DocSpec
cmdSpec cmd nargs = DocSpec M.empty (M.singleton cmd nargs)

envSpec :: String -> Int -> DocSpec
envSpec env nargs = DocSpec (M.singleton env nargs) M.empty

parseArgs :: (IsTuple a, AllReadable (TypeList a))
          => [[LatexDoc]]
          -> M a
parseArgs xs = do
    (x,[]) <- ST.runStateT read_all xs
    return $ fromTuple x

machineCmd :: forall result args ctx. 
              ( Monoid result, IsTuple args
              , IsTypeList  (TypeList args)
              , AllReadable (TypeList args))
           => String
           -> (args -> MachineId -> ctx -> M result) 
           -> Pipeline MM (MTable ctx) (Either [Error] (MTable result))
machineCmd cmd f = Pipeline m_spec empty_spec g
    where
        nargs = len ($myError :: TypeList args)
        m_spec = cmdSpec cmd nargs
        param = Collect 
            { getList = getCmd
            , tag = cmd
            , getInput = getMachineInput
            }
        g = collect param (cmdFun f)

type M' = RWS LineInfo [Error] System

cmdFun :: forall a b c d. 
              ( IsTuple b, Ord c
              , IsTypeList  (TypeList b)
              , AllReadable (TypeList b))
           => (b -> c -> d -> M a) 
           -> Cmd
           -> c -> (Map c d) -> M a
cmdFun f xs m ctx = local (const $ cmdLI xs) $ do
        x <- parseArgs (getCmdArgs xs)
        f x m (ctx ! m)

machineEnv :: forall result args ctx.
              ( Monoid result, IsTuple args
              , IsTypeList  (TypeList args)
              , AllReadable (TypeList args))
           => String
           -> (args -> [LatexDoc] -> MachineId -> ctx -> M result)
           -> Pipeline MM (MTable ctx) (Either [Error] (MTable result))
machineEnv env f = Pipeline m_spec empty_spec g
    where
        nargs = len ($myError :: TypeList args)
        m_spec = envSpec env nargs
        param = Collect 
            { getList = getEnv
            , tag = env
            , getInput = getMachineInput
            }
        g = collect param (envFun f)

envFun :: forall a b c d. 
              ( IsTuple b, Ord c
              , IsTypeList  (TypeList b)
              , AllReadable (TypeList b))
           => (b -> [LatexDoc] -> c -> d -> M a) 
           -> Env
           -> c -> (Map c d) -> M a
envFun f xs m ctx = local (const $ envLI xs) $ do
        x <- parseArgs (getEnvArgs xs)
        f x (getEnvContent xs) m (ctx ! m)

contextCmd :: forall a b c. 
              ( Monoid a, IsTuple b
              , IsTypeList  (TypeList b)
              , AllReadable (TypeList b))
           => String
           -> (b -> ContextId -> c -> M a) 
           -> Pipeline MM (CTable c) (Either [Error] (CTable a))
contextCmd cmd f = Pipeline empty_spec c_spec g
    where
        nargs = len ($myError :: TypeList b)
        c_spec = cmdSpec cmd nargs
        param = Collect 
            { getList = getCmd
            , tag = cmd
            , getInput = getContextInput
            }
        g = collect param (cmdFun f)

contextEnv :: forall result args ctx.
              ( Monoid result, IsTuple args
              , IsTypeList  (TypeList args)
              , AllReadable (TypeList args))
           => String
           -> (args -> [LatexDoc] -> ContextId -> ctx -> M result)
           -> Pipeline MM (CTable ctx) (Either [Error] (CTable result))
contextEnv env f = Pipeline empty_spec c_spec g
    where
        nargs = len ($myError :: TypeList args)
        c_spec = envSpec env nargs
        param = Collect 
            { getList = getEnv
            , tag = env
            , getInput = getContextInput
             }
        g = collect param (envFun f)

data Collect a b k t = Collect 
    { getList :: a -> Map k [b] 
    , getInput :: Input -> Map t a 
    -- , getContent :: b -> a
    , tag :: k }

collect :: (Ord k, Monoid z, Ord c)
        => Collect a b k c
        -> (b -> c -> d -> M z) 
        -> d
        -> MM (Either [Error] (Map c z))
collect p f arg = do
            cmp <- ask
            xs <- lift $ lift $ runEitherT $ toEither 
                $ forM (M.toList $ getInput p cmp) $ \(mname, x) -> do
                    xs <- forM (M.findWithDefault [] (tag p) $ getList p x) $ \e -> do
                        fromEither mempty $ f e mname arg 
                    return (mname, mconcat xs)
            return $ fmap (fromListWith mappend) xs

read_document' :: [LatexDoc] -> M ()
read_document' xs = do
            -- traceM "step A"
            let li = line_info xs
            (ms,cs) <- hoistEither $ get_components xs li
            -- ms <- foldM gather empty xs
            let default_thy = empty_theory 
                                { extends = fromList [("basic",basic_theory)] }
                procM pass = do
                    ms' <- lift $ gets machines 
                    ms' <- toEither $ mapM (uncurry pass) 
                        $ M.elems 
                        $ M.intersectionWith (,) ms ms'
                    lift $ modify $ \s -> s{ 
                        machines = M.fromList $ zip (M.keys ms) ms' }
                procC pass = do
                    cs' <- lift $ gets theories
                    cs' <- toEither $ zipWithM 
                            (uncurry . pass) 
                            (M.keys cs)
                        $ M.elems 
                        $ M.intersectionWith (,) cs cs'
                    lift $ modify $ \s -> s 
                        { theories = M.fromList (zip (M.keys cs) cs') 
                                `M.union` theories s }
            lift $ modify (\s -> s 
                { machines = M.mapWithKey (\k _ -> empty_machine k) ms 
                , theories = M.map (const default_thy) cs `M.union` theories s })
            procM type_decl
            procC ctx_type_decl
            refs  <- lift $ gets ref_struct
            check_acyclic "refinement structure" (toList refs) li
            trickle_down merge_struct li

                -- take actual generic parameter from `type_decl'
            procM imports
            procC ctx_imports
            trickle_down merge_import li
    
                -- take the types from `imports' and `type_decl`
            procM declarations
            procC ctx_declarations
            trickle_down merge_decl li
                
                -- use the `declarations' of variables to check the
                -- type of expressions
            procM collect_expr
            procC ctx_collect_expr
            trickle_down merge_exprs li
            
                -- use the label of expressions from `collect_expr' 
                -- and properties
            procM collect_refinement
            trickle_down merge_refinements li
            
                -- use the label of expressions from `collect_expr' 
                -- and the refinement rules
                -- in hints.
            procM collect_proofs
            procC ctx_collect_proofs
            cs <- lift $ gets theories
            toEither $ forM_ (toList cs) $ \(name,ctx) -> do
                let li = line_info xs
                fromEither () $ check_acyclic 
                    ("proofs of " ++ name)
                    (thm_depend ctx) li
            trickle_down merge_proofs li
            ms <- lift $ gets machines
            toEither $ forM_ (M.elems ms) 
                $ deduce_schedule_ref_struct li
            s  <- lift $ gets proof_struct
            check_acyclic "proof of liveness" s li

type MPipeline ph a = Pipeline MM (MTable ph) (Either [Error] (MTable a))

set_decl :: MPipeline Phase0 
            ( [(String,Sort,LineInfo)]
            , [(String,VarScope)] )
set_decl = machineCmd "\\newset" $ \(String name, String tag) _m _ -> do
            let new_sort = Sort tag name 0
                new_type = Gen $ USER_DEFINED new_sort []
                new_def = Def [] name [] (set_type new_type)
                                    $ ztypecast "const" (set_type new_type) ztrue
            li <- lift ask
            return ([(tag,new_sort,li)],[(tag,TheoryDef new_def Local li)])

event_decl :: MPipeline Phase0 [(Label, EventId, LineInfo)]
event_decl = machineCmd "\\newevent" $ \(One evt) _m _ -> do 
            li <- lift ask 
            return [(evt,EventId evt,li)]

refines_mch :: MPipeline Phase0 [((), MachineId, LineInfo)]
refines_mch = machineCmd "\\refines" $ \(One amch) cmch (Phase0 ms _) -> do
            li <- lift ask
            unless (amch `M.member` ms) 
                $ left [Error (format "Machine {0} refines a non-existant machine: {1}" cmch amch) li]
                -- check that mch is a machine
            return [((),amch,li)]

type_decl :: [LatexDoc] -> Machine -> MSEither Machine
type_decl = visit_doc []
            [  (  "\\newset"
               ,  CmdBlock $ \(String name, String tag) m -> do
                    let th = theory m
                        new_sort = Sort tag name 0
                        new_type = Gen $ USER_DEFINED new_sort []
                        new_def = Def [] name [] (set_type new_type)
                                    $ ztypecast "const" (set_type new_type) ztrue
                    new_types  <- bind
                        (format "a sort with name '{0}' is already declared" tag)
                        $ insert_new tag new_sort (types th)
                        -- this is not a user error
                    new_defs <- bind
                            (format "a constant with name '{0}' is already declared" tag)
                            $ insert_new tag new_def (defs th)
                    let hd = th 
                            {  types = new_types
                            , defs = new_defs
                            }
                    return m { theory = hd } 
               )
            ,  (  "\\newevent"
               ,  CmdBlock $ \(One evt) m -> do 
                        toEither $ error_list
                            [ ( evt `member` events m
                              , format "event '{0}' is already defined" evt )
                            ]
                        return m { events = insert evt (empty_event) $ events m } 
               )
            ,  (  "\\refines"
               ,  CmdBlock $ \(One mch) m -> do
                        anc   <- lift $ gets ref_struct
                        sys   <- lift $ gets machines
                        li    <- lift ask
                        unless (show mch `member` sys) 
                            $ left [Error (format "Machine {0} refines a non-existant machine: {1}" (_name m) mch) li]
                        when (_name m `member` anc) 
                            $ left [Error (format "Machines can only refine one other machine") li]
                        lift $ modify $ \x -> x { ref_struct = insert (_name m) mch $ ref_struct x }
                        return m
               )
            ]

import_theory :: MPipeline Phase0 [(String, Theory, LineInfo)]
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

imports :: [LatexDoc] -> Machine 
        -> MSEither Machine 
imports = visit_doc []
            [   ( "\\with"
                , CmdBlock $ \(One (String th_name)) m -> do
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
                        Just th -> 
                            return m { theory = (theory m) {
                                extends = insert th_name th 
                                    $ extends (theory m) } }
                )
            ]

variable_decl :: MPipeline Phase1
                    [(String,VarScope)]
variable_decl = machine_var_decl Machine "\\variable"

constant_decl :: MPipeline Phase1
                    [(String,VarScope)]
constant_decl = machine_var_decl TheoryConst "\\constant"

dummy_decl :: MPipeline Phase1
                    [(String,VarScope)]
dummy_decl = machine_var_decl (\v source li -> Evt $ singleton Nothing (v,Param,source,li)) "\\dummy"

machine_var_decl :: (Var -> DeclSource -> LineInfo -> VarScope)
                 -> String
                 -> MPipeline Phase1
                        [(String,VarScope)]
machine_var_decl scope kw = machineCmd kw $ \(One xs) _m p1 -> do
            vs <- get_variables' (p1 ^. pAllTypes) xs
            li <- lift ask
            return $ map (\(x,y) -> (x,scope y Local li)) vs

index_decl :: MPipeline Phase1 [(String,VarScope)]
index_decl = event_var_decl Index "\\indices"

param_decl :: MPipeline Phase1 [(String,VarScope)]
param_decl = event_var_decl Param "\\param"

event_var_decl :: EvtScope
               -> String
               -> MPipeline Phase1
                    [(String,VarScope)]
event_var_decl escope kw = machineCmd kw $ \(lbl,xs) _m p1 -> do
            let ts   = L.view pTypes p1
                evts = L.view pEvents p1 
            evt <- bind
                (format "event '{0}' is undeclared" lbl)
                $ lbl `M.lookup` evts
            li <- lift ask
            vs <- get_variables' ts xs
            return $ map (\(n,v) -> ((n,Evt $ M.singleton (Just evt) (v,escope,Local,li)))) vs

    -- Todo: detect when the same variable is declared twice
    -- in the same declaration block.
declarations :: [LatexDoc] -> Machine 
             -> MSEither Machine
declarations = visit_doc []
        [   (   "\\variable"
            ,   CmdBlock $ \(One xs) m -> do
                        let msg = "repeated declaration: {0}"
                        vs <- get_variables 
                            (context m) 
                            xs
                        let inter =                  S.fromList (map fst vs) 
                                    `S.intersection` keysSet (variables m)
                        toEither $ error_list 
                            [ ( not $ S.null inter
                              , format msg (intercalate ", " $ S.toList inter ))
                            ]
                        return m { variables = fromList vs `union` variables m} 
            )
        ,   (   "\\indices"
            ,   CmdBlock $ \(evt,xs) m -> do
                        let msg = "repeated declaration: {0}"
                        vs <- get_variables 
                            (context m) 
                            xs
                        old_event <- bind 
                            (format "event '{0}' is undeclared" evt)
                            $ evt `M.lookup` events m
                        let var_names = map fst vs
                            inter = S.fromList var_names `S.intersection` 
                                    (           keysSet (params old_event) 
                                      `S.union` keysSet (indices old_event) )
                        toEither $ error_list
                            [ ( not $ S.null inter
                              , format msg $ intercalate ", " $ S.toList inter )
                            ]
                        let new_event = old_event { 
                            indices = fromList vs `union` indices old_event }
                        return m { events = insert evt new_event $ events m } 
            )
        ,   (   "\\param"
            ,   CmdBlock $ \(evt,xs) m -> do
                        
                        vs <- get_variables 
                            (context m) 
                            xs
                        old_event <- bind
                            (format "event '{0}' is undeclared" evt)
                            $ evt `M.lookup` events m
                        let var_names = map fst vs
                            inter = S.fromList var_names `S.intersection` 
                                    (           keysSet (params old_event) 
                                      `S.union` keysSet (indices old_event) )
                            msg = "repeated declaration: {0}"
                        toEither $ error_list
                            [ ( not $ S.null inter
                              , format msg (intercalate ", " $ S.toList inter) )
                            ]
                        let new_event = old_event { 
                            params = fromList vs `union` params old_event }
                        return m { events = insert evt new_event $ events m } 
            )
        ,   (   "\\constant"
            ,   CmdBlock $ \(One xs) m -> do
                        let err = "repeated definition"
                        vs <- get_variables 
                            (context m) 
                            xs
                        return m { theory = (theory m) { 
                                consts = merge 
                                    (fromListWith (error err) vs) 
                                    (consts $ theory m) } } 
            )
        ,   (   "\\dummy"
            ,   CmdBlock $ \(One xs) m -> do
                        let err = "repeated definition"
                        vs <- get_variables 
                            (context m) 
                            xs
                        return m { theory = (theory m) { 
                                dummies = merge 
                                    (fromListWith (error err) vs) 
                                    (dummies $ theory m) } } 
            )
        ]

tr_hint' :: Phase2
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
                expr <- parse_expr' 
                    (machine_parser p2 `with_vars` fv) 
                        { expected_type = Just t }
                    texExpr
                -- expr <- get_expr_with_ctx m 
                --     (Context M.empty vs M.empty M.empty M.empty) xs
                -- toEither $ error_list $ map (\evt ->
                --     ( not $ x `member` indices evt 
                --     , format "'{0}' is not an index of '{1}'" x lbls )
                --     ) evts
                return $ TrHint (insert x expr ys) z)
        , ( "\\lt"
          , CmdBlock $ \(One prog) (TrHint ys z) -> do
                let msg = "Only one progress property needed for '{0}'"
                toEither $ error_list 
                    [ ( not $ isNothing z
                      , format msg lbls )
                    ]
                return $ TrHint ys (Just prog))
        ]

tr_hint :: Machine
        -> Map String Var
        -> [Label]
        -> [LatexDoc]
        -> TrHint
        -> RWS LineInfo [Error] System TrHint
tr_hint m vs lbls = visit_doc []
        [ ( "\\index"
          , CmdBlock $ \(String x, xs) (TrHint ys z) -> do
                evts <- bind_all lbls
                    (format "'{1}' is not an event of '{0}'" $ _name m)
                    (`M.lookup` events m)
                expr <- get_expr_with_ctx m 
                    (Context M.empty vs M.empty M.empty M.empty) xs
                toEither $ error_list $ map (\evt ->
                    ( not $ x `member` indices evt 
                    , format "'{0}' is not an index of '{1}'" x lbls )
                    ) evts
                return $ TrHint (insert x expr ys) z)
        , ( "\\lt"
          , CmdBlock $ \(One prog) (TrHint ys z) -> do
                let msg = "Only one progress property needed for '{0}'"
                toEither $ error_list 
                    [ ( not $ isNothing z
                      , format msg lbls )
                    ]
                return $ TrHint ys (Just prog))
        ]

check_types :: Either String a -> EitherT [Error] (RWS LineInfo [Error] System) a    
check_types c = EitherT $ do
    li <- ask
    return $ either (\x -> Left [Error x li]) Right c

get_progress_prop :: Phase3 -> MachineId -> ProgId -> M ProgressProp
get_progress_prop p3 _m lbl =  
            bind
                (format "progress property '{0}' is undeclared" lbl)
                $ lbl `M.lookup` (L.view pProgress p3)

get_safety_prop :: Phase3 -> MachineId -> Label -> M SafetyProp
get_safety_prop p3 _m lbl =  
            bind
                (format "safety property '{0}' is undeclared" lbl)
                $ lbl `M.lookup` (L.view pSafety p3)

get_notation :: HasPhase2 phase => phase -> Notation
get_notation p2 = L.view pNotation p2
    -- where Phase2 _ _ _ _ _ notation _ _ _ _ = ancestor p2

machine_events :: HasPhase1 phase => phase -> Map Label EventId
machine_events p2 = L.view pEvents p2

get_event :: HasPhase1 phase => phase -> Label -> M EventId
get_event p2 ev_lbl = do
        let evts = machine_events p2
        bind
            (format "event '{0}' is undeclared" ev_lbl)
            $ ev_lbl `M.lookup` evts

get_events :: Phase2 -> [Label] -> M [EventId]
get_events p2 ev_lbl = do
            let evts = machine_events p2
            bind_all ev_lbl
                (format "event '{0}' is undeclared")
                $ (`M.lookup` evts)

get_schedules :: Phase3 -> EventId -> M (Map Label Expr)
get_schedules p3 evt = 
        return $ L.view pSchedules p3 ! evt

get_guards :: Phase3 -> EventId -> M (Map Label Expr)
get_guards p3 evt = 
        return $ (p3 ^. pGuards) ! evt

get_invariants :: Phase3 -> Map Label Expr
get_invariants p3 = (p3 ^. pInvariant)

progress_props :: Phase3 -> Map ProgId ProgressProp
progress_props p3 = p3 ^. pProgress

event_parser :: HasPhase2 phase => phase -> EventId -> ParserSetting
event_parser p2 ev = (p2 ^. pEvtSynt) ! ev

schedule_parser :: HasPhase2 phase => phase -> EventId -> ParserSetting
schedule_parser p2 ev = (p2 ^. pSchSynt) ! ev

machine_parser :: HasPhase2 phase => phase -> ParserSetting
machine_parser p2 = L.view pMchSynt p2

context_parser :: HasPhase2 phase => phase -> ParserSetting
context_parser p2 = p2 ^. pCtxSynt

state_variables :: HasPhase2 phase => phase -> Map String Var
state_variables p2 = p2 ^. pStateVars

abstract_variables :: HasPhase2 phase => phase -> Map String Var
abstract_variables p2 = p2 ^. pAbstractVars

dummy_vars :: HasPhase2 phase => phase -> Map String Var
dummy_vars p2 = p2 ^. pDummyVars

event_indices :: HasPhase2 phase => phase -> Map EventId (Map String Var)
event_indices p2 = p2 ^. pIndices

free_vars' :: Map String Var -> Expr -> Map String Var
free_vars' ds e = vs `M.intersection` ds
    where
        vs = symbol_table $ S.elems $ used_var e

assignment :: MPipeline Phase2
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

bcmeq_assgn :: MPipeline Phase2
                    [(Label,ExprScope)]
bcmeq_assgn = machineCmd "\\evbcmeq" $ \(ev_lbl, lbl, String v, xs) _m p2 -> do
            ev <- get_event p2 ev_lbl
            var <- bind
                (format "variable '{0}' undeclared" v)
                $ v `M.lookup` (state_variables p2)
            xp <- parse_expr' 
                (event_parser p2 ev) 
                { expected_type = Nothing } xs
            check_types
                $ Right (Word var) `mzeq` Right xp
            let act = Assign var xp
            li <- lift ask
            return [(lbl,EventExpr $ M.singleton ev $ (Action act,Local,li))]

bcmsuch_assgn :: MPipeline Phase2
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

bcmin_assgn :: MPipeline Phase2
                    [(Label,ExprScope)]
bcmin_assgn = machineCmd "\\evbcmin" $ \(evt, lbl, String v, xs) _m p2 -> do
            ev <- get_event p2 evt
            xp  <- parse_expr' (event_parser p2 ev)
                    { expected_type = Nothing } xs
            var <- bind
                (format "variable '{0}' undeclared" v)
                $ v `M.lookup` (state_variables p2)
            let act = BcmIn var xp
            check_types $ Right (Word var) `zelem` Right xp
            li <- lift ask
            return [(lbl,EventExpr $ M.singleton ev $ (Action act,Local,li))]

guard_decl :: MPipeline Phase2
                    [(Label,ExprScope)]
guard_decl = machineCmd "\\evguard" $ \(evt, lbl, xs) _m p2 -> do
            ev <- get_event p2 evt
            xp <- parse_expr' (event_parser p2 ev) xs
            li <- lift ask
            return [(lbl,EventExpr $ M.singleton ev $ (Guard xp,Local,li))]
 
coarse_sch_decl :: MPipeline Phase2
                    [(Label,ExprScope)]
coarse_sch_decl = machineCmd "\\cschedule" $ \(evt, lbl, xs) _m p2 -> do
            ev <- get_event p2 evt
            xp <- parse_expr' (schedule_parser p2 ev) xs
            li <- lift ask
            return [(lbl,EventExpr $ M.singleton ev $ (CoarseSchedule xp,Local,li))]

fine_sch_decl :: MPipeline Phase2
                    [(Label,ExprScope)]
fine_sch_decl = machineCmd "\\fschedule" $ \(evt, lbl, xs) _m p2 -> do
            ev <- get_event p2 evt
            xp <- parse_expr' (schedule_parser p2 ev) xs
            li <- lift ask
            return [(lbl,EventExpr $ M.singleton ev $ (FineSchedule xp,Local,li))]

        -------------------------
        --  Theory Properties  --
        -------------------------

assumption :: MPipeline Phase2
                    [(Label,ExprScope)]
assumption = machineCmd "\\assumption" $ \(lbl,xs) _m p2 -> do
            xp <- parse_expr' (context_parser p2) xs
            li <- lift ask
            return [(lbl,Axiom xp Local li)]

        --------------------------
        --  Program properties  --
        --------------------------

initialization :: MPipeline Phase2
                    [(Label,ExprScope)]
initialization = machineCmd "\\initialization" $ \(lbl,xs) _m p2 -> do
            xp <- parse_expr' (machine_parser p2) xs
            li <- lift ask
            return [(lbl,Initially xp Local li)]

invariant :: MPipeline Phase2
                    [(Label,ExprScope)]
invariant = machineCmd "\\invariant" $ \(lbl,xs) _m p2 -> do
            xp <- parse_expr' (machine_parser p2) xs
            li <- lift ask
            return [(lbl,Invariant xp Local li)]

transient_prop :: MPipeline Phase2
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

transientB_prop :: MPipeline Phase2
                    [(Label,ExprScope)]
transientB_prop = machineCmd "\\transientB" $ \(evts, lbl, hint, xs) m p2 -> do
            _evs <- get_events p2 evts
            tr   <- parse_expr' (machine_parser p2) 
                    { free_dummies = True } xs
            let fv = free_vars' ds tr
                ds = dummy_vars p2
            evts' <- bind "Expecting non-empty list of events"
                    $ NE.nonEmpty evts
            hint  <- toEither $ tr_hint'
                            p2 m fv evts' hint empty_hint
            let prop = Transient fv tr evts hint
            li <- lift ask
            return [(lbl,TransientProp prop Local li)]

constraint_prop :: MPipeline Phase2
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
            -> Phase2
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

safetyA_prop :: MPipeline Phase2
                    [(Label,ExprScope)]
safetyA_prop = machineCmd "\\safety" 
                $ \(lbl, pCt, qCt) -> safety_prop lbl Nothing pCt qCt

safetyB_prop :: MPipeline Phase2
                    [(Label,ExprScope)]
safetyB_prop = machineCmd "\\safetyB" 
                $ \(lbl, evt, pCt, qCt) -> safety_prop lbl evt pCt qCt

progress_prop :: MPipeline Phase2
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
collect_expr :: [LatexDoc] -> Machine 
             -> MSEither Machine
collect_expr = visit_doc 
                --------------
                --  Events  --
                --------------
        [] [(   "\\evassignment"
            ,   CmdBlock $ \(evs, lbl, xs) m -> do
                        let msg = "{0} is already used for another assignment"
                        evs <- forM evs $ \ev -> do
                                -- should revert back to only one event
                            old_event <- bind
                                (format "event '{0}' is undeclared" ev)
                                $ ev `M.lookup` events m
                            pred    <- get_evt_part m old_event xs
                            let frame = M.elems $ variables m `M.difference` abs_vars m
                                act = BcmSuchThat frame pred
                            new_act <- bind 
                                (format msg lbl)
                                $ insert_new lbl act (actions old_event)
                            let new_event = old_event 
                                        { actions = new_act }
                            scope (context m) pred (        params old_event 
                                                   `merge` indices old_event)
                            return (ev,new_event)
                        return m {          
                                events  = union (fromList evs) $ events m } 
            )
        ,   (   "\\evbcmeq"
            ,   CmdBlock $ \(evt, lbl, String v, xs) m -> do
                    let msg = "{0} is already used for another assignment"
                    old_event <- bind
                                (format "event '{0}' is undeclared" evt)
                                $ evt `M.lookup` events m
                    xp  <- parse_expr' (event_setting m old_event) 
                            { expected_type = Nothing } xs
                    var <- bind
                        (format "variable '{0}' undeclared" v)
                        $ v `M.lookup` variables m
                    let act = Assign var xp
                    check_types
                        $ Right (Word var) `mzeq` Right xp
                    new_act <- bind
                        (format msg lbl)
                        $ insert_new lbl act (actions old_event)
                    let new_event = old_event { actions = new_act }
                    return m { events = M.insert evt new_event $ events m }
            )
        ,   (   "\\evbcmsuch"
            ,   CmdBlock $ \(evt, lbl, vs, xs) m -> do
                    let msg = "{0} is already used for another assignment"
                    old_event <- bind
                                (format "event '{0}' is undeclared" evt)
                                $ evt `M.lookup` events m
                    xp  <- parse_expr' (event_setting m old_event) 
                            { is_step = True } xs
                    vars <- bind_all (map toString vs)
                        (format "variable '{0}' undeclared")
                        $ (`M.lookup` variables m)
                    let act = BcmSuchThat vars xp
                    new_act <- bind
                        (format msg lbl)
                        $ insert_new lbl act (actions old_event)
                    let new_event = old_event { actions = new_act }
                    return m { events = M.insert evt new_event $ events m }
            )
        ,   (   "\\evbcmin"
            ,   CmdBlock $ \(evt, lbl, String v, xs) m -> do
                    let msg = "{0} is already used for another assignment"
                    old_event <- bind
                                (format "event '{0}' is undeclared" evt)
                                $ evt `M.lookup` events m
                    xp  <- get_evt_part m old_event xs
                    var <- bind
                        (format "variable '{0}' undeclared" v)
                        $ v `M.lookup` variables m
                    let act = BcmIn var xp
                    check_types $ Right (Word var) `zelem` Right xp
                    new_act <- bind
                        (format msg lbl)
                        $ insert_new lbl act (actions old_event)
                    let new_event = old_event { actions = new_act }
                    return m { events = M.insert evt new_event $ events m }
            )
        ,   (   "\\evguard"
            ,   CmdBlock $ \(evt, lbl, xs) m -> do
                        old_event <- bind
                            ( format "event '{0}' is undeclared" evt )
                            $ evt `M.lookup` events m
                        let grds = guards old_event
                            msg = "'{0}' is already used for another guard"
                        grd       <- get_evt_part m old_event xs
                        new_guard <- bind (format msg lbl)
                            $ insert_new lbl grd grds 
                        let n         = length $ sched_ref old_event
                            rule      = add_guard evt lbl
                            new_event = old_event
                                        { sched_ref = rule : sched_ref old_event
                                        , guards    = new_guard  }
                            po_lbl    = composite_label 
                                        [ evt, label "GRD"
                                        , _name m, label $ show n]
                        scope (context m) grd (        indices old_event 
                                               `merge` params old_event)
                        return m  
                              { props = (props m) { 
                                    derivation = 
                                        insert po_lbl (Rule rule)
                                    $ derivation (props m) } 
                              , events  = insert evt new_event $ events m } 
            )
        ,   (   "\\cschedule"
            ,   CmdBlock $ \(evt, lbl, xs) m -> do
                        old_event <- bind 
                            ( format "event '{0}' is undeclared" evt )
                            $ evt `M.lookup` events m
                        let msg = "'{0}'' is already used for another schedule"
                        sch <- get_evt_part m old_event xs
                        new_sched <- bind
                            (format msg lbl)
                            $ insert_new lbl sch $ scheds old_event
                        let new_event = old_event { 
                                    scheds = new_sched }
                        scope (context m) sch (indices old_event) 
                        return m {          
                                events  = insert evt new_event $ events m } 
            )
        ,   (   "\\fschedule"
            ,   CmdBlock $ \(evt, lbl :: Label, xs) m -> do
                        old_event <- bind
                            (format "event '{0}' is undeclared" evt)
                            $ evt `M.lookup` events m
                        let msg = "{0} is already used for another schedule"
                        sch       <- get_evt_part m old_event xs
                        new_sched <- bind 
                            (format msg lbl)
                            $ insert_new lbl sch $ scheds old_event
                        let new_event = old_event { 
                                    scheds = new_sched }
                        scope (context m) sch (indices old_event) 
                        return m {          
                                events  = insert evt new_event $ events m } 
            )
                -------------------------
                --  Theory Properties  --
                -------------------------
        ,   (   "\\assumption"
            ,   CmdBlock $ \(lbl,xs) m -> do
                        let th = theory m
                            msg = "'{0}' is already used for another assertion"
                        axm      <- get_assert m xs
                        new_fact <- bind (format msg lbl)
                            $ insert_new lbl axm $ fact th
                        return m { 
                            theory = th { fact = new_fact } } 
            )
                --------------------------
                --  Program properties  --
                --------------------------
        ,   (   "\\initialization"
            ,   CmdBlock $ \(lbl,xs) m -> do
                        let msg = "'{0}' is already used for another invariant"
                        initp     <- get_assert m xs
                        new_inits <- bind (format msg lbl)
                            $ insert_new lbl initp $ inits m
                        return m {
                                inits = new_inits } 
            )
        ,   (   "\\invariant"
            ,   CmdBlock $ \(lbl,xs) m -> do
                        let msg = "'{0}' is already used for another invariant"
                        invar   <- get_assert m xs
                        new_inv <- bind (format msg lbl)
                            $ insert_new lbl invar $ inv $ props m
                        return m { 
                            props = (props m) { 
                                inv = new_inv } } 
            )
        ,   (   "\\transient"      
            ,   CmdBlock $ \(evts, lbl, xs) m -> do
                        let msg = "'{0}' is already used for another\
                                  \ program property"
                        toEither $ error_list $ map (\ev ->
                            ( not (ev `member` events m)
                            , format "event '{0}' is undeclared" ev )
                            ) evts
                        tr            <- get_assert_with_free m xs
                        let prop = Transient 
                                    (free_vars (context m) tr) 
                                    tr evts empty_hint
                            old_prog_prop = transient $ props m
                        new_props     <- bind (format msg lbl)
                            $ insert_new lbl prop $ old_prog_prop
                        return m {
                            props = (props m) {
                                transient = new_props } } 
            )
        ,   (   "\\transientB"      
            ,   CmdBlock $ \(evts, lbl, hint, xs) m -> do
                        let msg = "'{0}' is already used for\
                                  \ another program property"
                        toEither $ error_list $ map (\ev ->
                            ( not (ev `member` events m)
                            , format "event '{0}' is undeclared" ev )
                            ) evts
                        tr            <- get_assert_with_free m xs
                        let fv = (free_vars (context m) tr)
                        hint <- toEither $ tr_hint 
                                            m fv evts hint empty_hint
                        let prop = Transient fv tr evts hint
                            old_prog_prop = transient $ props m
                        new_props  <- bind (format msg lbl)
                                $ insert_new lbl prop $ old_prog_prop
                        return m {
                            props = (props m) {
                                transient = new_props } } 
            )
        ,   (   "\\constraint"
            ,   CmdBlock $ \(lbl,xs) m -> do
                        let msg = "'{0}' is already used for another safety property"
                        pre <- get_predicate m empty_ctx WithFreeDummies xs
                        let vars = elems $ free_vars (context m) pre
                        new_cons <- bind (format msg lbl)
                                $ insert_new lbl (Co vars pre) 
                                    $ constraint $ props m
                        return m { 
                            props = (props m) { 
                                constraint = new_cons } } 
            )
        ,   (   "\\safety"
            ,   CmdBlock $ \(lbl, pCt, qCt) m -> do
                    (p,q)    <- toEither (do
                        p    <- fromEither ztrue $ get_assert_with_free m pCt
                        q    <- fromEither ztrue $ get_assert_with_free m qCt
                        return (p,q))
                    let ctx = context m
                        dum = free_vars ctx p `union` free_vars ctx q
                        new_prop = Unless (M.elems dum) p q Nothing
                    new_saf_props <- bind (format "safety property '{0}' already exists" lbl)
                        $ insert_new lbl 
                                new_prop
                                (safety $ props m)
                    return m { props = (props m) 
                        { safety = new_saf_props } } 
            )
        ,   (   "\\progress"
            ,   CmdBlock $ \(lbl, pCt, qCt) m -> do
                    let prop = progress $ props m
                    (p,q)    <- toEither (do
                        p    <- fromEither ztrue $ get_assert_with_free m pCt
                        q    <- fromEither ztrue $ get_assert_with_free m qCt
                        return (p,q))
                    let ctx = context m
                        dum = S.fromList (elems $ free_vars ctx p) 
                                `S.union` S.fromList (elems $ free_vars ctx q)
                        new_prop = LeadsTo (S.elems dum) p q
                    new_prog <- bind (format "progress property '{0}' already exists" lbl)
                        $ insert_new lbl new_prop $ prop 
                    new_deriv <- bind (format "proof step '{0}' already exists" lbl)
                        $ insert_new lbl (Rule Add) $ derivation $ props m
                    return m { props = (props m) 
                        { progress   = new_prog
                        , derivation = new_deriv
                        } } 
            )
        ]

scope :: (Monad m, R.MonadReader LineInfo m)
      => Context -> Expr -> Map String Var 
      -> EitherT [Error] m ()
scope ctx xp vs = do
    let fv          = keysSet $ free_vars ctx xp
    let decl_v      = keysSet vs
    let undecl_v    = S.toList (fv `S.difference` decl_v)
    li             <- R.ask
    if fv `S.isSubsetOf` decl_v
    then return ()
    else left [Error (format "Undeclared variables: {0}" 
                      (intercalate ", " undecl_v)) li]

-- data ProgRefScope = ProgPropRef Rule [(Label,Label)]

-- data EventRefScope = EventRefScope ScheduleChange

refine_prog_prop :: MPipeline Phase3
                [(ProgId,(Rule,[(ProgId,ProgId)]),LineInfo)]
refine_prog_prop = machineCmd "\\refine" $ \(goal, String rule, hyps, hint) m p3 -> do
        let p2   = p3 ^. phase2
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
emit_event_ref ev (MId m) sch = do
    let po_lbl = composite_label [label "SCH",label m]            
    li <- lift ask
    return [(ev,[((po_lbl,sch),li)])]

ref_replace_csched :: MPipeline Phase3 EventRef
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

ref_weaken_csched :: MPipeline Phase3 EventRef
ref_weaken_csched = machineCmd "\\weakento" $ \(evt_lbl,del,add) m p3 -> do
        let _ = evt_lbl :: Label
            _ = del :: S.Set Label
            _ = add :: S.Set Label
            rule   = (weaken evt_lbl)
                        { remove = del
                        , add = add }
        evt <- get_event p3 evt_lbl
        emit_event_ref evt m rule


ref_replace_fsched :: MPipeline Phase3 EventRef
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

ref_remove_guard :: MPipeline Phase3 EventRef
ref_remove_guard = machineCmd "\\removeguard" $ \(evt_lbl,lbls) m p3 -> do
        evt  <- get_event p3 evt_lbl
        grds <- get_guards p3 evt
        _ <- bind_all lbls (format "'{0}' is not a valid guard") 
            (`M.lookup` grds)
        let rules     = map (AST.remove_guard evt_lbl) lbls
        liftM concat 
            $ forM rules 
            $ emit_event_ref evt m

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

collect_refinement :: [LatexDoc] -> Machine
                   -> MSEither Machine 
collect_refinement = visit_doc []
        [   (   "\\refine"
            ,   CmdBlock $ \(goal, String rule, hyps, hint) m -> do
                    toEither $ error_list
                        [   ( not (goal `member` (progress (props m) `union` progress (inh_props m)))
                            , format "the goal is an undefined progress property {0}" goal )
                        ]
                    let prog = progress (props m) `union` progress (inh_props m)
                        saf  = safety (props m) `union` safety (inh_props m)
                        rem_add ref
                            | ref == Rule Add = Nothing
                            | otherwise       = Just ref
                    r <- parse_rule' (map toLower rule) 
                        (RuleParserParameter m prog saf goal hyps hint)
                    new_der <- bind 
                        (format "progress property {0} already has a refinement" goal)
                        (insert_new goal r $ update rem_add goal $ derivation $ props m)
                    return m { props = (props m) { derivation = new_der } } 
            )
        ,   (   "\\safetyB"
            ,   CmdBlock $ \(lbl, evt, pCt, qCt) m -> do
                        -- Why is this here instead of the expression collector?
                    _  <- bind
                        (format "event '{0}' is undeclared" evt)
                        $ evt `M.lookup` events m
                    let prop = safety $ props m
                    (p,q) <- toEither (do
                        p <- fromEither ztrue $ get_assert_with_free m pCt
                        q <- fromEither ztrue $ get_assert_with_free m qCt
                        return (p,q))
                    let ctx = context m
                        dum =       free_vars ctx p 
                            `union` free_vars ctx q
                    let new_prop = Unless (M.elems dum) p q (Just evt)
                    new_saf <- bind 
                        (format "safety property '{0}' already exists" lbl)
                        $ insert_new lbl new_prop prop 
                    return m { props = (props m) 
                        { safety = new_saf
                        } } 
            )
        ,   (   "\\replace"
            ,   CmdBlock $ \(evt,del,add,keep,prog,saf) m -> do
                    old_event <- bind
                        (format "event '{0}' is undeclared" evt)
                        $ evt `M.lookup` events m
                    let sc    = scheds old_event
                        lbls  = (S.elems $ add `S.union` del `S.union` keep)
                        progs = progress (props m) `union` progress (inh_props m)
                        safs  = safety (props m) `union` safety (inh_props m)
                    _     <- bind_all lbls
                        (format "'{0}' is not a valid schedule")
                        $ (`M.lookup` sc)
                    pprop <- bind 
                        (format "'{0}' is not a valid progress property" prog)
                        $ prog `M.lookup` progs
                    sprop <- bind
                        (format "'{0}' is not a valid safety property" saf)
                        $ saf `M.lookup` safs
                    let n         = length $ sched_ref old_event
                        rule      = (replace evt (prog,pprop) (saf,sprop)) 
                                    { remove = del
                                    , add = add
                                    , keep = keep }
                        new_event = old_event { sched_ref = rule : sched_ref old_event }
                        po_lbl    = composite_label [evt,label "SCH",_name m,label $ show n]
                    return m 
                      { events = insert evt new_event $ events m
                      , props = (props m) { 
                            derivation = 
                                insert po_lbl (Rule rule)
                            $ derivation (props m) } 
                      }
            )
        ,   (   "\\weakento"
            ,   CmdBlock $ \(evt :: Label,del :: S.Set Label,add :: S.Set Label) m -> do
                    old_event <- bind
                        (format "event '{0}' is undeclared" evt)
                        $ evt `M.lookup` events m
                    let sc        = scheds old_event
                        lbls      = (S.elems $ add `S.union` del)
                    _     <- bind_all lbls
                        (format "'{0}' is not a valid schedule")
                        $ (`M.lookup` sc)
                    let n         = length $ sched_ref old_event
                        rule      = (weaken evt)
                                    { remove = del
                                    , add = add }
                        new_event = old_event 
                                    { sched_ref = rule : sched_ref old_event }
                        po_lbl    = composite_label [evt,label "SCH",_name m,label $ show n]
                    return m 
                      { events = insert evt new_event $ events m
                      , props = (props m) { 
                            derivation = 
                                insert po_lbl (Rule rule)
                            $ derivation (props m) } 
                      }
            )
        ,   (   "\\replacefine"
            ,   CmdBlock $ \(evt, old, new, prog) m -> do
                    old_event <- bind
                        (format "event '{0}' is undeclared" evt)
                        $ evt `M.lookup` events m
                    let sc        = scheds old_event
                        progs     = progress (props m) `union` progress (inh_props m)
                    -- _     <- bind_all (S.elems keep)
                    --     (format "'{0}' is not a valid schedule")
                    --     $ (`M.lookup` sc)
                    pprop <- case prog of
                        Just prog -> do
                            pprop <- bind 
                                (format "'{0}' is not a valid progress property" prog)
                                $ prog `M.lookup` progs
                            return $ Just (prog,pprop)
                        Nothing -> return Nothing
                    old_exp <- bind
                        (format "'{0}' is not a valid schedule" $ MM.fromJust old)
                        $ maybe (Just ztrue) (`M.lookup` sc) old
                    new_exp <- bind 
                        (format "'{0}' is not a valid schedule" $ MM.fromJust new)
                        $ maybe (Just ztrue) (`M.lookup` sc) new
                    let n         = length $ sched_ref old_event
                        rule      = (replace_fine evt old_exp new new_exp pprop)
--                                    { add = S.fromList $ maybeToList new
--                                    , remove = S.fromList $ maybeToList old 
--                                    , keep = keep }
                        new_event = old_event 
                                    { sched_ref = rule : sched_ref old_event }
                        po_lbl    = composite_label [evt,label "SCH",_name m,label $ show n]
                    return m 
                      { events = insert evt new_event $ events m
                      , props = (props m) { 
                            derivation = 
                                insert po_lbl (Rule rule)
                            $ derivation (props m) } 
                      }
            )
        ,   (   "\\removeguard"
            ,   CmdBlock $ \(evt, lbls) m -> do
                    old_event <- bind
                        (format "event '{0}' is undeclared" evt)
                        $ evt `M.lookup` events m
                    let grd       = guards old_event
                    toEither $ do
                        error_list $ flip map lbls $ \lbl ->
                            ( not $ lbl `member` grd
                                , format "'{0}' is not a valid schedule" lbl )
                    let n         = length $ sched_ref old_event
                        rules     = map (AST.remove_guard evt) lbls
                        new_event = old_event 
                                    { sched_ref = rules ++ sched_ref old_event }
                        po_lbl    = flip map [n .. ] $ \n -> 
                                    composite_label [evt,label "GRD",_name m,label $ show n]
                    return m 
                      { events = insert evt new_event $ events m
                      , props = (props m) { 
                            derivation = 
                                     M.fromList (zip po_lbl $ map Rule rules)
                            `union`  derivation (props m) } 
                      }
            )
        ]

all_comments :: MPipeline Phase3 [(DocItem, String, LineInfo)]
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

all_proofs :: MPipeline Phase3 [(Label,Tactic Proof,LineInfo)]
all_proofs = machineEnv "proof" $ \(One po) xs m p3 -> do
        li <- lift ask
        let notation = get_notation p3
            po_lbl = label $ remove_ref $ concatMap flatten po
            lbl = composite_label [ as_label m, po_lbl ]
        proof <- mapEitherT 
            (\cmd -> runReaderT cmd notation) 
            $ run_visitor li xs collect_proof_step 
        return [(lbl,proof,li)]

collect_proofs :: [LatexDoc] -> Machine
               -> MSEither Machine
collect_proofs = visit_doc
        [   (   "proof"
            ,   EnvBlock $ \(One po) xs m -> do -- with_tracingM $ do
                        -- This should be moved to its own phase
                    let po_lbl = label $ remove_ref $ concatMap flatten po
                        lbl = composite_label [ _name m, po_lbl ]
                        th  = theory m
                    toEither $ error_list 
                        [   ( lbl `member` proofs (props m)
                            , format "a proof for {0} already exists" lbl )
                        ] 
                    li <- lift ask
                    s  <- bind 
                        (format "proof obligation does not exist: {0} {1}" 
                                lbl 
                                (M.keys $ raw_machine_pos m))
                        $ lbl `M.lookup` raw_machine_pos m
                    let notation = th_notation th
                    p <- mapEitherT 
                        (\cmd -> runReaderT cmd notation) 
                        $ run_visitor li xs collect_proof_step 
                    let _ = p :: Tactic Proof
                    p <- hoistEither $ runTactic li s p
                    return m { 
                        props = (props m) { 
                            proofs = insert lbl p $ 
                                    proofs $ props m } } 
            )
        ] [
            ( "\\comment"
            , CmdBlock $ \(item',cmt') m -> do
                li <- lift ask
                let cmt = concatMap flatten cmt'
                    item = L.filter (/= '$') $ remove_ref $ concatMap flatten item'
                    prop = props m
                    is_inv = label item `member` inv prop
                    is_prog = label item `member` progress prop
                    is_event = label item `member` events m
                    is_var = item `member` variables m
                    lbl = label item
                    conds = [is_inv,is_prog,is_event,is_var]
                unless (length (L.filter id conds) <= 1)
                    $ fail "collect_proofs: conditional not mutually exclusive"
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
                        $ fail "collect_proofs: conditional not exhaustive"
                    left [Error (format msg item) li]
                return $ m { comments = M.insert key cmt 
                            $ comments m }
            )
        ]

check_schedule_ref_struct :: Map Label Label
                            -> Label
                            -> [(Label,Label)]
                            -> Map Label Event
                            -> Map Label Transient
                            -> Map Label ProgressProp
                            -> RWS LineInfo [Error] System ()
check_schedule_ref_struct refs m prog_dep es trs progs = fromEither () $ do
        let _ = m :: Label
        li <- ask
        struct <- toEither $ W.execWriterT $ do
            forM_ (toList es) $ check_sched
            forM_ (toList trs) $ check_trans li
        check_acyclic "proof of liveness" (struct ++ prog_dep) li
    where
        check_trans li (lbl,Transient _ _ evts (TrHint _ lt))  = do
                add_proof_edge' lbl $ map (\evt -> g evt m) evts
                forM_ evts $ \evt -> do
                    lift $ do
                        let f_sch = fine $ new_sched (es ! evt)
                        unless (maybe True (`member` progs) lt)
                            $ tell [Error (format "'{0}' is not a progress property" $ MM.fromJust lt) li]
                        unless (isJust f_sch == isJust lt)
                            $ if isJust f_sch
                            then tell [Error (format fmt0 lbl evt) li]
                            else tell [Error (format fmt1 lbl evts) li]
                    add_proof_edge' lbl $ maybeToList lt
            where
                fmt0 =    "transient predicate {0}: a leads-to property is required for "
                       ++ "transient predicates relying on events "
                       ++ "({1}) with a fine schedule"
                fmt1 =    "transient predicate {0}: a leads-to property is only required "
                       ++ "for events ({1}) with a fine schedule"
        check_sched (lbl,evt) = do
                case M.lookup m refs of
                    Just m' -> do
                        add_proof_edge' (g lbl m') [g lbl m]
                        mapM_ (f (g lbl m')) $ sched_ref evt
                    Nothing ->
                        return ()
        f lbl cs = 
            case rule cs of
                Weaken -> return ()
                Replace (prog,_) (saf,_) -> 
                    add_proof_edge' lbl [prog,saf]
                ReplaceFineSch _ _ _ (Just (prog,_)) ->
                    add_proof_edge' lbl [prog]
                ReplaceFineSch _ _ _ Nothing ->
                    return ()
                RemoveGuard _ -> return ()
                AddGuard _ -> return ()
        g lbl m = composite_label [m, lbl, label "SCH"]

add_proof_edge' :: Monad m 
                => Label -> [Label] 
                -> W.WriterT [(Label,Label)] m ()
add_proof_edge' x xs = tell $ zip (repeat x) xs

deduce_schedule_ref_struct :: Monad m
                           => LineInfo -> Machine
                           -> RWST r [Error] System m ()
deduce_schedule_ref_struct li m = do
        forM_ (toList $ events m) check_sched
        forM_ (toList $ transient $ props m) check_trans
    where
        check_trans (lbl,Transient _ _ evts (TrHint _ lt))  = do
                add_proof_edge lbl $ map (\evt -> g evt $ _name m) evts
                forM_ evts $ \evt -> do
                    let f_sch = fine $ new_sched (events m ! evt)
                        progs = progress (props m) `union` progress (inh_props m) 
                    unless (maybe True (`member` progs) lt)
                        $ tell [Error (format "'{0}' is not a progress property" $ MM.fromJust lt) li]
                    unless (isJust f_sch == isJust lt)
                        $ if isJust f_sch
                        then tell [Error (format fmt0 lbl evt) li]
                        else tell [Error (format fmt1 lbl evts) li]
                    add_proof_edge lbl $ maybeToList lt
            where
                fmt0 =    "transient predicate {0}: a leads-to property is required for "
                       ++ "transient predicates relying on events "
                       ++ "({1}) with a fine schedule"
                fmt1 =    "transient predicate {0}: a leads-to property is only required "
                       ++ "for events ({1}) with a fine schedule"
        check_sched (lbl,evt) = do
                ref <- gets ref_struct
                case M.lookup (_name m) ref of
                    Just m' -> do
                        add_proof_edge (g lbl m') [g lbl $ _name m]
                        mapM_ (f (g lbl m')) $ sched_ref evt
                    Nothing ->
                        return ()
        f lbl cs = 
            case rule cs of
                Weaken -> return ()
                Replace (prog,_) (saf,_) -> 
                    add_proof_edge lbl [prog,saf]
                ReplaceFineSch _ _ _ (Just (prog,_)) ->
                    add_proof_edge lbl [prog]
                ReplaceFineSch _ _ _ Nothing ->
                    return ()
                RemoveGuard _ -> return ()
                AddGuard _ -> return ()
        g lbl m = composite_label [m, lbl, label "SCH"]

parse_system :: FilePath -> IO (Either [Error] System)
parse_system fn = runEitherT $ do
        xs <- EitherT $ parse_latex_document fn
        hoistEither $ all_machines xs
        
parse_machine :: FilePath -> IO (Either [Error] [Machine])
parse_machine fn = runEitherT $ do
        xs <- EitherT $ parse_latex_document fn
        ms <- hoistEither $ all_machines xs
        return $ map snd $ toList $ machines ms





