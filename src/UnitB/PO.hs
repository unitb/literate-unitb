{-# LANGUAGE BangPatterns
    ,OverloadedStrings
    ,ScopedTypeVariables
    ,ViewPatterns
    ,GADTs,TypeFamilies #-}
    -- Behavior hiding
module UnitB.PO 
    ( theory_po
    , step_ctx, evt_live_ctx
    , theory_ctx, theory_facts
    , evt_saf_ctx, invariants, assert_ctx
    , verify_all, prop_saf, prop_tr
    , tr_wd_po, saf_wd_po
    , prop_saf'
    , proof_obligation'
    , raw_machine_pos'
    , dump, used_types )
where

    -- Modules
import Logic.Expr.Prism
import Logic.Expr.Scope
import Logic.Proof
import           Logic.Proof.POGenerator hiding ( variables, definitions )
import qualified Logic.Proof.POGenerator as POG
import Logic.Theory
import Logic.WellDefinedness

import UnitB.Expr
import UnitB.Proof
import UnitB.Syntax as AST 

import Z3.Z3

    -- Libraries
import Control.Arrow
import Control.CoApplicative
import Control.Lens  hiding (indices,Context,Context',(.=))
import Control.Monad hiding (guard)
import Control.Precondition

import           Data.Either
import           Data.Existential
import           Data.Foldable as F
import           Data.List as L hiding (inits, union,insert)
import           Data.List.NonEmpty as NE hiding (inits,(!!))
import           Data.List.Utils as LU (replace)
import           Data.Map as M hiding 
                    ( map, (!)
                    , delete, filter, null
                    , (\\), mapMaybe )
import qualified Data.Map as M
import           Data.Monoid.Monad
import qualified Data.Traversable as T

import System.IO

import Text.Printf.TH

import Utilities.Functor
import Utilities.Syntactic

    -- 
    --
    -- Proof Obligation Labelling Convention
    --
    -- Transient
    --      Mch/Evt/TR/EN/lbl
    --      Mch/Evt/TR/NEG/lbl
    -- Co
    --      Mch/Evt/CO/lbl
    -- Inv
    --      Mch/Evt/INV/lbl
    --      Mch/INIT/INV/lbl
    -- Thm 
    --      Mch/THM/lbl
    -- Feasibility
    --      Mch/Evt/FIS
    --      Mch/Evt/SCH
    --
    --

    -- TODO: 
    -- add theorem POs
    --      problem: In what order do we prove the theorems?

tr_lbl            :: Label
co_lbl            :: Label
inv_lbl           :: Label
inv_init_lbl      :: Label
init_fis_lbl      :: Label
fis_lbl           :: Label
sch_lbl           :: Label
thm_lbl           :: Label

tr_lbl            = label "TR"
co_lbl            = label "CO"
inv_lbl           = label "INV"
inv_init_lbl      = label "INIT/INV"
init_fis_lbl      = label "INIT/FIS"
fis_lbl           = label "FIS"
sch_lbl           = label "SCH"
thm_lbl           = label "THM"

assert_ctx :: RawMachineAST -> Context
assert_ctx m = empty_ctx
        & constants .~ (vars `M.union` del)
        & definitions .~ ds
    where
        del  = m!.del_vars
        vars = m!.variables
        mkDef n e = makeDef [] n [] (type_of e) e
        ds   = M.mapWithKey mkDef $ m!.defs

step_ctx :: RawMachineAST -> Context
step_ctx m = merge_all_ctx 
        [  empty_ctx 
                & constants .~ primeAll (vars `M.union` abs)
                & definitions .~ ds
        ,  assert_ctx m ]
    where
        abs  = m!.abs_vars
        vars = m!.variables
        mkDef n e = makeDef [] n [] (type_of e) e
        ds   = M.mapWithKey mkDef 
                $ M.mapKeys addPrime 
                $ primed (vars `M.union` abs) <$> m!.defs

abstract_step_ctx :: RawMachineAST -> Context
abstract_step_ctx m = merge_all_ctx 
        [  empty_ctx 
                & constants .~ primeAll vars
                & definitions .~ ds
        ,  assert_ctx m ]
    where
        mkDef n e = makeDef [] n [] (type_of e) e
        ds   = M.mapWithKey mkDef 
                $ M.mapKeys addPrime 
                $ primed vars <$> m!.defs
        vars = m!.variables


evt_saf_ctx :: HasConcrEvent' event RawExpr => event -> Context
evt_saf_ctx evt  = Context M.empty (evt^.new.params) M.empty M.empty M.empty

evt_live_ctx :: HasConcrEvent' event RawExpr => event -> Context
evt_live_ctx evt = Context M.empty (evt^.new.indices) M.empty M.empty M.empty

primed_vars :: Map Name Var -> POCtx ()
primed_vars = POG.variables . primeAll

skipOrLabel :: SkipOrEvent -> Label
skipOrLabel lbl = fromRight "SKIP" $ as_label <$> lbl

invariants :: RawMachineAST -> Map Label RawExpr
invariants m = 
                  (_inv p0) 
        `M.union` (_inv_thm p0) 
        `M.union` (_inv p1)
        `M.union` (_inv_thm p1)
    where
        p0 = m!.props
        p1 = m!.inh_props

invariants_only :: RawMachineAST -> Map Label RawExpr
invariants_only m = 
                  (_inv p0) 
        `M.union` (_inv p1)
    where
        p0 = m!.props
        p1 = m!.inh_props

raw_machine_pos' :: HasExpr expr => MachineAST' expr -> (Map Label Sequent)
raw_machine_pos' m' = eval_generator $ 
                with (do
                        prefix_label $ as_label $ _name m
                        _context $ theory_ctx (m!.theory)
                        set_syntactic_props syn
                        nameless_hyps $ M.elems unnamed 
                        named_hyps $ named_f
                        setTimeout $ m!.timeout
                        ) $ do
                    let moreTr = additional_transient m
                    forM_ (M.toList (p^.transient) ++ moreTr) $ \tr -> do
                        prop_tr m tr
                        tr_wd_po m tr
                    let moreSaf = additional_safety m
                    forM_ (M.toList (p^.safety) ++ moreSaf) $ \saf -> do
                        prop_saf m saf
                        saf_wd_po m saf
                    forM_ (M.toList $ _constraint p) $ \co -> do
                        prop_co m co 
                        co_wd_po m co
                    init_fis_po m
                    init_wd_po m
                    init_sim_po m
                    init_wit_wd_po m
                    init_witness_fis_po m
                    inv_wd_po m
                    thm_wd_po m
                    mapM_ (inv_po m) $ M.toList $ _inv p
                    mapM_ (thm_po m) $ M.toList $ _inv_thm p
                    forM_  (M.toList $ nonSkipUpwards m) $ \ev -> do
                        strengthen_guard_po m ev
                        evt_eql_po m ev
                    --forM_ (all_refs m) $ 
                        sim_po m ev
                        sch_po m ev
                    -- forM_ (all_refs m) $ \ev -> do
                    forM_  (M.toList $ nonSkipDownwards m) $ \ev -> do
                        ind_wit_wd_po m ev
                        ind_wit_fis_po m ev
                        replace_csched_po m ev
                        weaken_csched_po  m ev
                        replace_fsched_po m ev
                    forM_  (M.toList $ nonSkipUpwards m) $ \ev -> do
                        evt_wd_po m ev
                        wit_wd_po m ev
                        wit_fis_po m ev
                        fis_po m ev
                    mapM_ (prog_wd_po m) $ M.toList $ _progress p
                    run $ foldMapWithKey (fmap Cons . ref_po m) (m!.derivation)
    where 
        m   = raw m'
        syn = allSyntacticThms (m!.theory)
        p   = m!.props
        unnamed = theory_facts (m!.theory) `M.difference` named_f
        named_f = theory_facts (m!.theory) { _extends = M.empty }

proof_obligation' :: IsExpr expr 
                  => Map Label Sequent
                  -> Map Label (ProofBase expr)
                  -> MachineAST' expr 
                  -> Either [Error] (Map Label Sequent)
proof_obligation' pos proofs m = do
        forM_ (M.toList proofs) (\(lbl,p) -> do
            let li = line_info p
            if lbl `M.member` pos
                then return ()
                else Left [Error 
                    ([s|a proof is provided for non-existant proof obligation %s|] $ pretty lbl)
                        li])
        xs <- forM (M.toList pos) (\(lbl,po) -> do
            case M.lookup lbl proofs of
                Just c ->
                    proof_po c lbl po
                Nothing -> 
                    return [(lbl,po)])
        ys <- theory_po (m!.theory)
        return $ M.fromList (concat xs) `M.union` ys

additional_transient :: RawMachineAST -> [(Label, RawTransient)]
additional_transient m = do
    M.foldMapWithKey 
        (allAutomaticTransients . ("LIVE" </>) . as_label) 
        --(m!.props.progress) 
        (m!.derivation)

additional_safety :: RawMachineAST -> [(Label, RawSafetyProp)]
additional_safety m = do
    F.fold $ M.intersectionWithKey 
        (const . allAutomaticSafety . ("LIVE" </>) . as_label) 
        (m!.props.progress) 
        (m!.derivation)

ref_po :: RawMachineAST -> ProgId -> ProofTree -> M ()
ref_po m lbl r = 
        with (do
                prefix_label $ as_label lbl
                prefix_label "LIVE" 
                _context $ assert_ctx m
                _context $ step_ctx m
                named_hyps $ invariants m) 
            $ refinement_po m r

theory_po :: Theory -> Either [Error] (Map Label Sequent)
theory_po th = do
        xs <- mapM (uncurry f) $ M.toList $ M.mapWithKey g thm
        return $ M.fromList $ concat xs
    where
--        axm = M.filterKeys (not . (`S.member` theorems th)) $ fact th
        dep :: Map Label (Map Label ())
        dep       = M.map M.fromList $ M.fromListWith (++) 
                        [ (x,[(y,())]) | (x,y) <- th^.thm_depend ]
        depend x  = thm `M.intersection` findWithDefault M.empty x dep
        (thm,axm) = M.partitionWithKey p $ th ^. fact
        p k _     = k `M.member` view theorems th

        g lbl x   = empty_sequent & named .~ (depend lbl `M.union` axm) 
                                  & goal .~ x
        keys k    = composite_label ["THM",k]
        f lbl po = result
          where
            result = case keys lbl `M.lookup` view theorems th of
                        Just (Just proof) -> do
                            xs <- proof_po proof (keys lbl) po'
                            return xs
                        _ -> return [(keys lbl, po')]
            po' = po & context  %~ (`merge_ctx` theory_ctx th)
                     & nameless %~ (concatMap 
                            (M.elems . theory_facts) 
                            (elems $ _extends th) ++) 

init_sim_po :: RawMachineAST -> M ()
init_sim_po m = 
    with 
        (do prefix_label "INIT"
            prefix_label "SIM"
            _context (assert_ctx m)
            named_hyps $ m!.inits
            named_hyps $ M.mapKeys as_label $ witnessDef <$> m!.init_witness)
        (forM_ (M.toList $ m!.del_inits) $ \(lbl,p) -> do
            emit_goal [lbl] p)

init_wit_wd_po :: RawMachineAST -> M ()
init_wit_wd_po m =
    with 
        (do _context (assert_ctx m)
            named_hyps $ m!.inits)
        (emit_goal ["INIT/WWD"] 
            (well_definedness $ zall $ witnessDef <$> m!.init_witness))

init_witness_fis_po :: RawMachineAST -> M ()
init_witness_fis_po m =
    with 
        (do _context (assert_ctx m)
            named_hyps $ m!.inits)
        (emit_exist_goal ["INIT/WFIS"] 
            (M.elems $ (view' abs_vars m)  `M.difference` (view' variables m))
            (M.elems $ witnessDef <$> m!.init_witness))

init_fis_po :: RawMachineAST -> M ()
init_fis_po m = 
        with 
            (do _context (assert_ctx m) 
                POG.variables det_vars
                named_hyps $ uncurry (zeq . Word) <$> det_act)
            (emit_exist_goal [init_fis_lbl] 
                (M.elems $ nonDet_vars) 
                (M.elems $ new_act))
    where
        -- pvar = L.map prime $ M.elems $ (m!.variables) `M.union` (m!.abs_vars)
        (det_act,new_act) = splitDetInit vars $ m!.inits
        vars = (m!.variables)  `M.union` (m!.abs_vars)
        nonDet_vars = vars `M.difference` det_vars
        det_vars = symbol_table $ fst <$> det_act

_AssignExpr :: Prism' RawExpr (Var,RawExpr)
_AssignExpr = prism' (uncurry zeq) (preview [fun| (= $v $e) |]) . swapped . aside _Word . swapped

splitDetInit :: Map Name Var
             -> Map Label RawExpr
             -> ( Map Label (Var,RawExpr)
                , Map Label RawExpr )
splitDetInit vs acts = (det' & _Wrapped.traverse %~ distr, M.map zall $ M.unionWith (++) clash' nonDet')
    where
        acts' = conjuncts <$> acts
        nonDet :: Map Label (NonEmpty RawExpr) 
        nonDet' = M.map NE.toList nonDet
        det :: Map Label (NonEmpty (Var,RawExpr))
        (nonDet,det) = M.mapMaybe (nonEmpty.fst) &&& M.mapMaybe (nonEmpty.snd) $ M.map isDet acts'
        distr :: (a,(b,c)) -> (b,(a,c))
        distr (x,(y,z)) = (y,(x,z))
        isDet :: [RawExpr] -> ([RawExpr],[(Var,RawExpr)])
        isDet = partitionEithers . L.map (matching _AssignExpr)
        clash' :: Map Label [RawExpr]
        clash' = M.fromListWith (++) $ 
                M.toList clash & \xs -> [ (l,[Word v `zeq` e]) | (v,es) <- xs, (l,e) <- es ]
        det'  :: Map Var (Label,RawExpr)
        clash :: Map Var [(Label,RawExpr)]
        (clash,det') = mapEither onlyOne $ M.fromListWith (++) $ distrList $ M.toList det
        distrList :: [(t1, NonEmpty (t, t2))] -> [(t, [(t1, t2)])]
        distrList xs = [ (v,[(l,e)]) | (l,ne) <- xs, (v,e) <- NE.toList ne ]
            -- det & _Wrapped %~ _ . L.map sequence
            -- (_2 %~ pure) . sequence
        onlyOne [(v,x)] 
            | M.null (free_vars' vs x) = Right (v,x)
        onlyOne x   = Left x

type M = POGen

expected_leadsto_po :: ProgressProp' RawExpr -> ProgressProp' RawExpr -> M ()
expected_leadsto_po (LeadsTo vs p0 q0) (LeadsTo vs' p1 q1) = do
        emit_goal ["lhs"] $ zforall (vs ++ vs') p0 p1
        emit_goal ["rhs"] $ zforall (vs ++ vs') q1 q0

assume_old_guard :: HasExpr expr => EventMerging expr -> POCtx ()
assume_old_guard evt = do
    case evt^.abstract_evts of
        e :| [] -> named_hyps $ e^._2.old.guards
        _ :| (_:_) -> return ()

prop_tr :: RawMachineAST -> (Label, RawTransient) -> M ()
prop_tr m (pname, Tr fv xp' evt_lbl tr_hint) = provided (null inds) $ do
            with (do
                    prefix_label $ composite_label [pname,tr_lbl]
                    ctx 
                    named_hyps $ invariants m) $ do
                with (named_hyps $ singleton pname xp) $
                    forM_ (M.toList hint) $ \(v,(t,e)) -> do
                        emit_exist_goal ["WFIS",as_label v] [prime $ Var v t] [e]
                zipWithM_ stuff (NE.toList evt_lbl) es
                following
    where
        TrHint hint' lt_fine = tr_hint
        hint :: Map Name (Type,RawExpr)
        hint = hint' & traverse._2 %~ asExpr
        xp = asExpr xp'
        stuff evt_lbl evt = 
            with def_ctx $ do
                    enablement
                    negation
            where
                grd  = evt^.new.guards
                sch0 = evt^.new.coarse_sched
                -- sch1 = evt^.new.fine_sched
                sch  = evt^.new.schedules
                act  = ba_predicate m evt
                ind  = evt^.new.indices
                ind1 = (evt^.new.indices) `M.intersection` hint
                param_ctx  = POG.variables (evt^.new.params)
                enablement = do
                        emit_goal [as_label evt_lbl, "EN"] 
                            (          asExpr xp 
                            `zimplies` (new_dummy ind $ zall $ asExpr <$> sch0))

                new_defs = flip L.map (M.elems ind1) 
                        $ \(Var n t) -> (setSuffix "param" n, mk_fun [] (setSuffix "param" n) [] t)
                new_hyps = flip L.map (M.toList hint)
                        $ \(x,(_,e)) -> rename (addPrime x) (setSuffix "param" x) e
                def_ctx = do
                    POG.functions (M.fromList new_defs)
                    POG.nameless_hyps new_hyps
                negation = with (do 
                                    param_ctx
                                    assume_old_guard evt
                                    named_hyps $ M.map (new_dummy ind) sch
                                    named_hyps $ M.map (new_dummy ind) act
                                    named_hyps $ M.map (new_dummy ind) grd)
                      $ do
                        emit_goal [as_label evt_lbl,"NEG"] 
                            $ xp `zimplies` (znot $ primed vars xp) 
        vars = M.unions 
                    [ m!.variables
                    , m!.abs_vars
                    , m!.definedSymbols
                    ]
        all_ind = M.elems $ M.unions $ fv : L.zipWith local_ind (NE.toList evt_lbl) es
        inds    = L.map (fmap1 $ setSuffix "param") $ M.elems 
                        $ M.unions (L.map (view indices) es) `M.difference` hint
        es      = L.map (upward_event m.Right) (NE.toList evt_lbl)
        
        local_ind :: EventId -> RawEventMerging -> Map Name Var
        local_ind lbl e = renameAll' (add_suffix suff) $ e^.indices
            where
                suff = mk_suff $ pretty lbl
        new_ind :: EventId -> RawEventMerging -> RawExpr -> RawExpr
        new_ind lbl e = make_unique suff (e^.indices)
            where
                suff = mk_suff $ pretty lbl
            -- (M.elems ind) 
        tagged_sched :: EventId -> RawEventMerging -> Map Label RawExpr
        tagged_sched lbl e = M.map (new_ind lbl e) $ e^.new.coarse_sched & traverse %~ asExpr
        all_csch  = concatMap M.elems $ L.zipWith tagged_sched (NE.toList evt_lbl) es
            
            -- we take the disjunction of the fine schedules of 
            -- all the events involved in the transient predicate
        all_fsch  =
            zsome $ L.zipWith (\lbl e -> (new_ind lbl e . zall) $ e^.new.fine_sched & traverse %~ asExpr) (NE.toList evt_lbl) es
            -- fine $ new_sched evt
        following = with (prefix_label "leadsto") $
                case lt_fine of
                    Just lbl
                        | not $ all_fsch == ztrue ->
                            expected_leadsto_po 
                                (LeadsTo all_ind
                                        (zall $ xp : all_csch)
                                        all_fsch) 
                                (progs ! lbl)
                        | otherwise -> error $ 
                               [s|transient predicate %s's side condition doesn't |] (pretty pname) 
                            ++ [s|match the fine schedule of event %s|]
                                        (intercalate "," $ L.map pretty (NE.toList evt_lbl))
                    Nothing
                        | not $ all_fsch == ztrue -> do
                            emit_goal [] $ zforall all_ind
                                    (zall $ xp : all_csch) 
                                    all_fsch
                        | otherwise -> return ()
        ctx = do
                _context $ assert_ctx m 
                _context $ step_ctx m 
                dummy
        dummy = POG.variables fv
        progs = (m!.props.progress) `M.union` (m!.inh_props.progress)

mk_suff :: String -> String
mk_suff = LU.replace ":" "-" 

prop_co :: RawMachineAST -> (Label, Constraint' RawExpr) -> M ()
prop_co m (pname, Co fv xp) = 
    with
        (do _context $ step_ctx m
            POG.variables $ symbol_table fv
            named_hyps $ invariants m)
        $ forM_ evts $ \(evt_lbl,evt) -> do
            let grd  = evt^.new.guards
                act  = ba_predicate m evt
            with 
                (do named_hyps $ grd
                    named_hyps $ act
                    -- nameless_hyps $ _ $ evt^.abstract_evts
                    POG.variables $ evt^.indices
                    POG.variables $ evt^.params)
                (emit_goal [skipOrLabel evt_lbl,co_lbl,pname] $ forall_fv xp)
    where
        evts = M.toList (conc_events m)
        forall_fv xp = if L.null fv then xp else zforall fv ztrue xp

prop_saf :: RawMachineAST
         -> (Label, SafetyProp' RawExpr) -> M ()
prop_saf m = prop_saf' m Nothing

prop_saf' :: RawMachineAST -> Maybe EventId 
          -> (Label, SafetyProp' RawExpr) -> M ()
prop_saf' m excp (pname, Unless fv p q) = 
    with
        (do _context $ step_ctx m
            POG.variables $ symbol_table fv
            named_hyps $ invariants m) $ do
        let excps = maybe [] (NE.toList.view concrete_evts.downward_event m.Right) excp
            inds :: Map SkipOrEvent (Map Name Var)
            inds  = M.map (view indices) $ M.fromList excps
        forM_ evts $ \(evt_lbl,evt) -> do
            let grd = evt^.new.guards
                act = ba_predicate m evt
                ind = findWithDefault M.empty (Right evt_lbl) inds
                fvs = symbol_table fv 
                neq x = znot $ Word x `zeq` Word (suff x)
                isExcp = Right evt_lbl `M.member` inds
                rng | isExcp    = zsome $ L.map neq $ elems inter
                    | otherwise = ztrue
                inter = fvs `M.intersection` ind
                diff  = fvs `M.difference` ind
            with 
                (do named_hyps $ grd
                    named_hyps $ act
                    -- nameless_hyps $ _ $ evt^.abstract_evts
                    POG.variables $ evt^.new.indices
                    POG.variables $ evt^.new.params)
                (emit_goal [as_label evt_lbl,"SAF",pname] $ 
                    zforall (elems diff ++ L.map suff (elems ind))
                        rng
                        $ new_dummy inter $
                            zimplies (p `zand` znot q) 
                                     (primed (vars `M.union` (m!.definedSymbols)) 
                                            $ p `zor` q))
    where
        evts = rights $ L.map (\(x,y) -> (,y) <$> x) $ M.toList $ all_upwards m
        vars = (m!.variables) `M.union` (m!.abs_vars)
        suff = add_suffix "param"

inv_po :: RawMachineAST -> (Label, RawExpr) -> M ()
inv_po m (pname, xp) = 
    do  with (do _context $ step_ctx m
                 named_hyps $ invariants m)
            $ forM_ (M.toList $ nonSkipUpwards m) $ \(evt_lbl,evt) -> do
                let grd  = evt^.new.guards
                    act  = ba_predicate m evt
                    vars = view' variables m `M.union` view' abs_vars m `M.union` view' definedSymbols m
                with 
                    (do named_hyps $ grd
                        assume_old_guard evt
                        named_hyps $ act
                        named_hyps $ M.map ba_pred $ evt^.abs_actions
                        POG.variables $ old_indices evt
                        POG.variables $ evt^.new.indices
                        POG.variables $ evt^.new.params)
                    (emit_goal [as_label evt_lbl,inv_lbl,pname] 
                        (primed vars xp))
        with (do _context $ assert_ctx m
                 named_hyps $ m!.inits 
                 named_hyps $ M.mapKeys as_label $ witnessDef <$> m!.init_witness)
            $ emit_goal [inv_init_lbl, pname] xp

wit_wd_po :: RawMachineAST -> (EventId, RawEventMerging) -> M ()
wit_wd_po m (lbl, evt) = 
        with (do _context $ step_ctx m
                 POG.variables $ evt^.new.indices
                 POG.variables $ evt^.new.params
                 named_hyps $ invariants m
                 prefix_label $ as_label lbl
                 named_hyps $ evt^.new.guards
                 named_hyps $ ba_predicate' (m!.variables) (evt^.new.actions))
        (do
            emit_goal ["WWD"] $ well_definedness $ zall 
                $ M.elems $ witnessDef <$> evt^.witness
            emit_goal ["WWD"] $ well_definedness $ zall 
                $ M.elems $ witnessDef <$> evt^.param_witness)

old_indices :: RawEventMerging -> Map Name Var
old_indices evt = M.unions $ evt^.partsOf (abstract_evts.traverse._2.old.indices)

wit_fis_po :: Pre => RawMachineAST -> (EventId, RawEventMerging) -> M ()
wit_fis_po m (lbl, evt) = 
        with (do _context $ step_ctx m
                 POG.variables $ m!.del_vars
                 POG.variables $ evt^.new.indices
                 POG.variables $ evt^.new.params
                 named_hyps $ invariants m
                 prefix_label $ as_label lbl
                 named_hyps $ evt^.new.guards
                 named_hyps $ ba_predicate' (m!.variables) (evt^.new.actions))
        (do 
            let old_ind = old_indices evt
                new_ind = evt^.new.params
            emit_exist_goal ["WFIS"] pvar 
                $ M.elems $ witnessDef <$> evt^.witness
            emit_exist_goal ["WFIS"] (M.elems $ old_ind `M.difference` new_ind)
                $ M.elems $ witnessDef <$> evt^.param_witness)
    where
        pvar = L.map prime $ M.elems $ view' abs_vars m `M.difference` view' variables m

ind_wit_wd_po :: RawMachineAST -> (EventId, RawEventSplitting) -> M ()
ind_wit_wd_po m (lbl, evts) = 
        with (do _context $ step_ctx m
                 named_hyps $ invariants m
                 prefix_label $ as_label lbl
                 named_hyps $ evts^.old.coarse_sched
                 named_hyps $ evts^.old.fine_sched) $ do
            forM_ (evts^.evt_pairs) $ \evt -> do
                with (POG.variables $ evt^.new.indices) $
                    emit_goal ["IWWD",evt^.concrete._1.to as_label] $ well_definedness $ zall 
                        $ M.elems $ witnessDef <$> evt^.ind_witness

ind_wit_fis_po :: RawMachineAST -> (EventId, RawEventSplitting) -> M ()
ind_wit_fis_po m (lbl, evts) = 
        with (do _context $ step_ctx m
                 --POG.variables $ evt^.old.indices
                 --POG.variables $ evt^.old.params
                 named_hyps $ invariants m
                 prefix_label $ as_label lbl
                 named_hyps $ evts^.old.coarse_sched
                 named_hyps $ evts^.old.fine_sched) $ do
            forM_ (evts^.evt_pairs) $ \evt -> do
                let pvar = evt^.added.indices
                emit_exist_goal ["IWFIS"] (M.elems pvar)
                    $ M.elems $ witnessDef <$> ((evt^.ind_witness) `M.intersection` pvar)

removeSkip :: NonEmpty (SkipOrEvent, t) -> [(EventId, t)]
removeSkip = rights.fmap (view distrLeft).NE.toList

-- | When using witnesses with event indices:
-- | as /\ cs.i
-- | either 
-- |     ∀i:: as => cs.i
-- | or
-- |     as ↦ (∃i:: cs.i)
-- |     cs.i  unless  ¬as
-- | or
-- |     witness: i = f.x
-- |     as ↦ i = f.x ∧ cs.i
-- |     i = f.x ∧ cs.i  unless  ¬as
csched_ref_safety :: OldNewPair k -> RawEventSplitting -> [(Label,RawSafetyProp)]
csched_ref_safety (old,new) ev = ev^.concrete_evts.to removeSkip & traverse %~ (as_label *** safe)
    where
        ind cevt = M.elems $ M.union (cevt^.indices) (ev^.indices)
        safe :: ConcrEvent' RawExpr -> RawSafetyProp
        safe cevt = Unless (ind cevt)
                    (zall new_sch) 
                    (znot $ zall $ (ev^.coarse_sched) `M.intersection` old) 
                where
                    new_sch = elems $ (cevt^.coarse_sched) `M.intersection` new

replace_csched_po :: RawMachineAST -> (EventId,RawEventSplitting) -> M ()
replace_csched_po m (lbl,evt') = do 
    let old_c = evt'^.old.coarse_sched
        old_f = evt'^.old.fine_sched
    forM_ (L.zip [0..] $ evt'^.c_sched_ref) $ \(i,ref) -> do
        let nb  = label $ show (i :: Int)
        with (do 
                prefix_label $ as_label lbl
                prefix_label "C_SCH/delay"
                prefix_label nb ) $ do
            with (do
                    prefix_label "saf") $
                forM_ (csched_ref_safety (oldNewPair (evt'^.abstrEvent') ref) evt') 
                    $ prop_saf' m (Just lbl)
            with (do
                    _context $ assert_ctx m
                    _context $ step_ctx m
                    POG.variables $ evt'^.old.indices
                    POG.variables $ evt'^.concrete_evts.traverse._2.new.indices
                    named_hyps $ invariants m ) $ do
                let (plbl,prog) = ref^.sch_prog
                    new_part_c  = NE.map new_coarse_scheds $ evt'^.evt_pairs
                    new_coarse_scheds e = (e^.added.coarse_sched) `M.intersection` view add ref
                        --  we don't need (_ `M.union` keep_c) because,
                        --  whenever 'old ∧ keep_c' are true forever,
                        --  that includes that keep_c is true forever
                        --  and therefore, provided 'new' eventually
                        --  holds, it will hold at the same time as
                        --  'keep_c'
                    LeadsTo vs p0 q0  = prog
                with (do
                        POG.variables $ symbol_table vs
                        named_hyps old_c
                        named_hyps $ M.mapKeys as_label $ witnessDef <$> evt'^.ind_witness
                        named_hyps old_f) $ 
                    emit_goal ["prog",plbl,"lhs"] p0
                with (do
                        POG.variables $ symbol_table vs) $ do
                            --  For the next set of proof obligations there are
                            --  two possibilities: (1) either we are faced with
                            --  a regular one-to-one refinement or (2) we have
                            --  an event splitting. If we have a one-to-one
                            --  refinement (1), we can prove that q ⇒ csched
                            --  one schedule at a time. Otherwise, we have to
                            --  prove one big disjunction.
                    let new_part' = case new_part_c of
                                        cs :| [] -> cs
                                        cs -> singleton "split" $ zsome $ NE.map zall cs
                    forM_ (M.toList new_part') $ \(lbl,sch) -> do
                        emit_goal ["prog",plbl,"rhs",lbl] $ fromRight'$
                            Right q0 .=> Right sch \/ mznot (Right $ zall old_c)

weaken_csched_po :: RawMachineAST -> (EventId,RawEventSplitting) -> M ()
weaken_csched_po m (lbl,evt) = do
            let weaken_sch :: NonEmpty (Map Label RawExpr, Map Label RawExpr)
                weaken_sch = do
                        e <- evt^.evt_pairs
                        let addRule = M.unions (L.map (view add) $ e^.c_sched_ref)
                            new     = e^.added.coarse_sched
                        return ( new `M.difference` addRule
                               , new `M.intersection` addRule )
                old_c = evt^.old.coarse_sched
            with (do
                    prefix_label $ as_label lbl
                    prefix_label "C_SCH/weaken"
                    _context $ assert_ctx m
                    _context $ step_ctx m
                    POG.variables $ evt^.indices
                    F.for_ (evt^.evt_pairs) $ \e -> -- indices
                        POG.variables $ e^.added.indices
                    named_hyps $ invariants m 
                    named_hyps $ M.mapKeys as_label $ witnessDef <$> evt^.ind_witness
                        --  old version admits old_f as assumption
                        --  why is it correct or needed?
                        --  named_hyps old_f
                    named_hyps old_c  ) $ do
                unless (isOneToOne evt) $
                    with (do
                            prefix_label "saf") $ do
                        let ref = unrefinedSched evt
                        forM_ (F.concat $ csched_ref_safety <$> ref <*> pure evt) 
                            $ prop_saf' m (Just lbl)
                case weaken_sch of
                    (m0,m1) :| [] -> 
                        with (named_hyps m1)
                        $ forM_ (M.toList $ m0) $ \(lbl,sch) -> do
                            emit_goal [lbl] sch
                    ms -> 
                        emit_goal [] $ zsome $ NE.map zall (fst <$> ms)

replace_fsched_po :: RawMachineAST -> (EventId,RawEventSplitting) -> M ()
replace_fsched_po m (lbl,aevt) = do
        let evts   = aevt^.evt_pairs.to NE.toList
            evts'  = L.zip (NE.toList $ aevt^.multiConcrete.to (NE.map fst)) evts
            old_c  = unions $ L.map (view $ old.coarse_sched) evts
            new_c  = L.nub $ concatMap (elems . view (new.coarse_sched)) evts
            old_f  = unions $ L.map (view $ old.fine_sched) evts
            new_fs = L.map (view $ new.fine_sched) evts
        with (do
                prefix_label $ as_label lbl
                prefix_label "F_SCH/replace"
                _context $ assert_ctx m
                _context $ step_ctx m
                named_hyps  $ invariants m) $ do
            case aevt^.f_sched_ref of
              Just (plbl,prog) -> do
                let LeadsTo vs p0 q0 = prog
                with (do
                        POG.variables $ symbol_table vs
                        POG.variables $ aevt^.old.indices
                        named_hyps old_c
                        named_hyps old_f ) $
                    emit_goal ["prog",plbl,"lhs"] p0
                forM_ evts' $ \(clbl,evt) -> 
                    with (do
                            POG.variables $ evt^.total.indices
                            named_hyps $ evt^.new.coarse_sched
                            named_hyps $ evt^.new.fine_sched ) $
                        forM_ (M.toList $ evt^.deleted.fine_sched) $ \(lbl,sch) ->
                            emit_goal ["str",lbl,skipOrLabel clbl] sch 
                case new_fs of
                  [new_f] -> do
                    with (do
                            POG.variables $ evts^.traverse.new.indices
                            POG.variables $ symbol_table vs) $ do
                        forM_ (M.toList new_f) $ \(lbl,sch) -> 
                            emit_goal ["prog",plbl,"rhs",lbl] $
                                    q0 `zimplies` sch
                  _ -> do
                    with (do
                            POG.variables $ evts^.traverse.new.indices
                            POG.variables $ symbol_table vs) $ do
                        emit_goal ["prog",plbl,"rhs"] $
                                q0 `zimplies` zsome (L.map zall new_fs)
              Nothing -> do
                let add_f  = L.map (zall . view (added.fine_sched)) evts
                    del_f  = L.map (zall . view (deleted.fine_sched)) evts
                    kept_f = intersections $ L.map (view $ kept.fine_sched) evts
                unless (new_fs == [old_f]) $
                    with (do
                            POG.variables $ aevt^.old.indices
                            POG.variables $ evts^.traverse.new.indices
                            nameless_hyps new_c
                            named_hyps old_c -- is this sound?
                            named_hyps kept_f) $
                        emit_goal ["eqv"] $ fromRight'$
                            Right (zsome add_f) .=. Right (zsome del_f)

intersections :: Ord k => [Map k a] -> Map k a
intersections []  = assertFalse' "intersection of empty list is undefined"
intersections [x] = x
intersections (x:xs) = x `intersection` intersections xs                                

strengthen_guard_po :: Pre => RawMachineAST -> (EventId,RawEventMerging) -> M ()
strengthen_guard_po m (lbl,evt) = 
        with (do
            prefix_label $ as_label lbl
            prefix_label "GRD/str"
            _context $ assert_ctx m
            _context $ step_ctx m
            POG.variables $ M.unions $ evt^.partsOf (abstract_evts.traverse._2.old.indices)
            POG.variables $ evt^.new.indices
            POG.variables $ evt^.new.params 
            named_hyps $ M.mapKeys as_label $ witnessDef <$> evt^.param_witness
            named_hyps $ invariants m 
            named_hyps $ evt^.new.guards ) $ do
        case evt^.evt_pairs of
          evt :| [] -> 
            forM_ (M.toList $ evt^.deleted.guards) $ \(lbl,grd) -> do
                emit_goal [lbl] grd
          es -> 
            emit_goal [] $ zsome $ NE.map (zall . M.elems . view (deleted.guards)) es

sim_po :: RawMachineAST -> (EventId, RawEventMerging) -> M ()
sim_po m (lbl, evt) = 
        with (do
                _context $ step_ctx m
                POG.variables $ evt^.new.indices
                POG.variables $ evt^.new.params 
                prefix_label $ as_label lbl
                prefix_label "SIM"
                named_hyps (invariants m)
                named_hyps (evt^.new.guards)
                -- nameless_hyps $ _ $ evt^.abstract_evts
                named_hyps (ba_predicate m evt) ) $
            forM_ (M.toList $ evt^.deleted_actions) $ \(albl,act) ->
                emit_goal [albl] $ ba_pred act

fis_po :: RawMachineAST -> (EventId, RawEventMerging) -> M ()
fis_po m (lbl, evt) = 
        with (do _context $ assert_ctx m
                 -- TODO: Only check feasibility of
                 -- (concrete) non-deterministic assignments
                 _context $ abstract_step_ctx m
                 POG.variables $ evt^.indices
                 POG.variables $ evt^.params 
                 POG.variables $ m!.del_vars
                 POG.variables $ (m!.variables) `M.difference` nonDet_vars
                 primed_vars $ m!.del_vars
                 named_hyps $ invariants m
                 -- nameless_hyps $ _ $ evt^.abstract_evts
                 named_hyps $ ba_predicate' (m!.abs_vars) $ evt^.abs_actions
                 named_hyps $ evt^.new.guards
                 named_hyps $ review _AssignExpr <$> det_act)
            (emit_exist_goal [as_label lbl, fis_lbl] pvar 
                $ M.elems $ ba_predicate' nonDet_vars $ new_act)
    where
        pvar = L.map prime $ M.elems $ (m!.variables) `M.union` (m!.abs_vars)
        (det_act,new_act) = splitNonDet $ evt^.new_actions 
        nonDet_vars = frame new_act

splitNonDet :: forall expr. Map Label (Action' expr) 
            -> ( Map Label (Var,expr)
               , Map Label (Action' expr) )
splitNonDet acts = (det' & _Wrapped.traverse %~ distr, clash' `M.union` nonDet)
    where
        (nonDet,det) = mapEither isDet acts
        distr :: (a,(b,c)) -> (b,(a,c))
        distr (x,(y,z)) = (y,(x,z))
        isDet = matching _Assign
        clash' :: Map Label (Action' expr)
        clash' = clash & _Wrapped %~ \xs -> [ (l,Assign v e) | (v,es) <- xs, (l,e) <- es ]
        det'  :: Map Var (Label,expr)
        clash :: Map Var [(Label,expr)]
        (clash,det') = mapEither onlyOne $ M.fromListWith (++) $ distrList $ M.toList det
        distrList xs = [ (v,[(l,e)]) | (l,(v,e)) <- xs ]
        onlyOne [x] = Right x
        onlyOne x   = Left x

tr_wd_po :: RawMachineAST -> (Label, RawTransient) -> M ()
tr_wd_po  m (lbl, Tr vs p _ (TrHint wit _)) = 
        with (do prefix_label lbl
                 prefix_label "TR"
                 _context $ step_ctx m
                 named_hyps $ invariants m) $
            do  emit_goal ["WD"]
                    $ well_definedness $ zforall (elems vs) ztrue p
                forM_ (M.toList wit) $ \(n,(t,e)) -> 
                    with (do
                        POG.variables $ 
                                    symbol_table [prime $ Var n t]
                            `M.union` vs
                        POG.named_hyps $ singleton lbl p
                        ) $
                    emit_goal ["WD","witness",as_label n] $ 
                        well_definedness e

prog_wd_po :: RawMachineAST -> (ProgId, ProgressProp' RawExpr) -> M ()
prog_wd_po m (lbl, LeadsTo vs p q) = 
        with (do prefix_label $ as_label lbl
                 prefix_label "PROG"
                 _context $ step_ctx m
                 named_hyps $ invariants m) $
            do  emit_goal ["WD","lhs"]
                    $ well_definedness $ zforall vs ztrue p
                emit_goal ["WD","rhs"]
                    $ well_definedness $ zforall vs ztrue q

saf_wd_po :: RawMachineAST -> (Label, SafetyProp' RawExpr) -> M ()
saf_wd_po m (lbl, Unless vs p q) = 
        with (do prefix_label lbl
                 prefix_label "SAF"
                 _context $ step_ctx m
                 named_hyps $ invariants m) $
            do  emit_goal ["WD","lhs"]
                    $ zforall vs ztrue $ (znot q) `zimplies` (well_definedness p)
                emit_goal ["WD","rhs"]
                    $ well_definedness $ zforall vs ztrue q

co_wd_po :: RawMachineAST -> (Label, Constraint' RawExpr) -> M ()
co_wd_po m (lbl, Co vs p) = 
        with (do prefix_label lbl
                 prefix_label "CO"
                 _context $ step_ctx m
                 nameless_hyps $ M.elems $
                    M.map (primed vars) 
                        $ invariants m
                 named_hyps $ invariants m)
             $ emit_goal ["WD"]
                $ well_definedness $ zforall vs ztrue p
    where
        vars = M.unions [ view' variables m
                        , view' abs_vars m
                        , view' definedSymbols m
                        ]

inv_wd_po :: RawMachineAST -> M ()
inv_wd_po m = 
        with (do _context $ assert_ctx m
                 named_hyps $ m!.inh_props.inv
                 named_hyps $ m!.inh_props.inv_thm
                     )
            $ do
                let wd = well_definedness $ zall $ m!.props.inv
                emit_goal ["INV", "WD"] wd

init_wd_po :: RawMachineAST -> M ()
init_wd_po m = 
        with (do _context $ assert_ctx m
                 named_hyps $ m!.inh_props.inv
                 named_hyps $ m!.inh_props.inv_thm)
            $ do
                emit_goal ["INIT", "WD"] 
                    $ well_definedness $ zall $ m!.inits

incremental_wd_po :: Label
                  -> Map Label RawExpr  -- 
                  -> Map Label RawExpr  -- 
                  -> M ()
incremental_wd_po lbl old new = do
    let del  = old `M.difference` new
        add  = new `M.difference` old
    if M.null del then 
        with (do
                named_hyps old) $
            emit_goal [lbl] 
                $ well_definedness 
                $ zall add
    else
        emit_goal [lbl] 
            $ well_definedness 
            $ zall new

evt_wd_po :: RawMachineAST -> (EventId, RawEventMerging) -> M ()
evt_wd_po m (lbl, evts) = 
        with (do prefix_label $ as_label lbl
                 prefix_label "WD"
                 _context $ assert_ctx m
                 POG.variables $ evts^.new.indices
                 named_hyps $ invariants m) $ do
            let f ln = case evts^.evt_pairs of
                          evt :| [] -> evt^.ln
                          _ -> M.empty
            -- case evts^.evt_pairs of
            --   evt :| [] -> do
            incremental_wd_po "C_SCH"
                (f $ old.coarse_sched)
                (evts^.new.coarse_sched)
            with (named_hyps $ evts^.new.coarse_sched) $
                incremental_wd_po "F_SCH"
                    (f $ old.fine_sched)
                    (evts^.new.fine_sched)
            with (POG.variables $ evts^.new.params) $ do
                incremental_wd_po "GRD" 
                    (f $ old.guards) 
                    (evts^.new.raw_guards)
              -- es -> _
            with (POG.variables $ evts^.new.params) $ do
                with (do prefix_label "ACT"
                         assume_old_guard evts
                         named_hyps $ evts^.new.guards
                         _context $ step_ctx m) $ do
                    let p k _ = k `M.notMember` (evts^.old_actions)
                    forM_ (M.toList $ M.filterWithKey p $ evts^.new.actions) $ \(tag,bap) -> 
                        emit_goal [tag] 
                            $ well_definedness $ ba_pred bap

evt_eql_po :: RawMachineAST -> (EventId, RawEventMerging) -> M ()
evt_eql_po  m (_lbl, evts) = 
    with (do _context $ step_ctx m
             named_hyps $ invariants m ) $
    void $ T.forM (evts^.evt_pairs) $ \evt -> 
        with (do named_hyps $ evt^.total.guards
                 named_hyps $ ba_predicate m evt
                 prefix_label $ skipOrLabel $ evt^.concrete._1
                 prefix_label $ skipOrLabel $ evt^.abstract._1
                 prefix_label "EQL"
                 _context $ evt_live_ctx evt
                 _context $ evt_saf_ctx evt)
            (forM_ (M.elems $ evt^.eql_vars) $ \v -> do
                emit_goal [as_label $ v^.name] 
                    $ Word (prime v) `zeq` Word v )

sch_po :: RawMachineAST -> (EventId, RawEventMerging) -> M ()
sch_po m (lbl, evts) = 
    forM_ (evts^.evt_pairs.to NE.toList) $ \evt ->
        with (do prefix_label $ as_label lbl
                 prefix_label sch_lbl
                 _context $ assert_ctx m
                 _context $ evt_live_ctx evt
                 POG.variables ind
                 named_hyps hyp) $ do
            let removed_sched sch = not $ M.null $ evt^.deleted.sch
                added_grd = not $ M.null $ evt^.added.raw_guards
                removed_c_sch = removed_sched coarse_sched
                removed_f_sch = removed_sched fine_sched
            if M.null param
                then do 
                    when (removed_c_sch || removed_f_sch) $
                        forM_ (M.toList $ evt^.kept.raw_guards) 
                            $ \(lbl,grd) -> 
                            emit_goal [lbl] grd  
                    forM_ (M.toList $ evt^.added.raw_guards) 
                        $ \(lbl,grd) -> 
                        emit_goal [lbl] grd  
            else if removed_c_sch || removed_f_sch || added_grd
                then emit_exist_goal [] (M.elems param) (M.elems $ evt^.new.guards)
                else return ()
    where
        -- grd   = evt^.new.guards
        c_sch = evts^.new.coarse_sched
        f_sch = evts^.new.fine_sched
        param = evts^.new.params
        ind   = (evts^.new.indices) `merge` (evts^.new.params)
        hyp   = invariants m `M.union` f_sch `M.union` c_sch

thm_wd_po :: RawMachineAST -> M ()
thm_wd_po m = 
        with (do _context $ assert_ctx m
                 named_hyps $ m!.inh_props.inv
                 named_hyps $ m!.inh_props.inv_thm
                 named_hyps $ m!.props.inv) $ do
            let wd = well_definedness $ zall $ m!.props.inv_thm
            unless (wd == ztrue) $ 
                emit_goal ["THM", "WD"] wd 


thm_po :: RawMachineAST -> (Label, RawExpr) -> M ()
thm_po m (lbl, xp) = 
    with (do
            prefix_label thm_lbl
            prefix_label lbl
            _context $ assert_ctx m
            named_hyps inv)
        $ emit_goal [] xp
    where
        inv = invariants_only m

allAutomaticTransients :: Label -> ProofTree -> [(Label,RawTransient)]
allAutomaticTransients lbl (view cell -> Cell (Inference prop r ps _ _)) =
           ((lbl',) <$> automaticTransient prop r)
        ++ foldMapOf traverse (allAutomaticTransients lbl') ps
    where
        lbl' = lbl </> rule_name r

allAutomaticSafety :: Label -> ProofTree -> [(Label,RawSafetyProp)]
allAutomaticSafety lbl (view cell -> Cell (Inference prop r ps _ _)) = 
           ((lbl',) <$> automaticSafety prop r)
        ++ foldMapOf traverse (allAutomaticSafety lbl') ps
    where
        lbl' = lbl </> rule_name r

refinement_po :: RawMachineAST -> ProofTree -> POGen ()
refinement_po m (view cell -> Cell (Inference prog n hp ht hs)) = do
        with (prefix_label $ rule_name n) $ do
            liveness_po prog n (view goal <$> hp) ht (fst <$> hs)
            for_ hp $ refinement_po m

add_suffix :: Pre 
           => String -> Var -> Var
add_suffix = fmap1 . setSuffix

new_dummy :: Pre => Map Name Var -> RawExpr -> RawExpr
new_dummy = make_unique "param"

--check :: Calculation -> IO (Either [Error] [(Validity, Int)])
--check c = runEitherT $ do
--        pos <- hoistEither $ obligations' empty_ctx empty_sequent c
--        rs  <- lift $ forM pos $ uncurry discharge
--        let ln = L.filter ((/= Valid) . fst) $ L.zip rs [0..]
--        return ln

dump :: String -> Map Label Sequent -> IO ()
dump name pos = do
        withFile (name ++ ".z") WriteMode (\h -> do
            forM_ (M.toList pos) (\(lbl, po) -> do
                hPutStrLn h ([s|(echo \\"> %s\\")\n(push)|] $ pretty lbl)
                hPutStrLn h (z3_code po)
                hPutStrLn h "(pop)"
                hPutStrLn h ("; end of " ++ pretty lbl)
                ) )

verify_all :: Map Label Sequent -> IO (Map Label Bool)
verify_all pos' = do
    let xs         = M.toList pos'
        lbls       = L.map fst xs 
    ys <- map_failures (lbls !) 
            $ discharge_all xs
    rs <- forM (L.zip lbls ys) $ \(lbl,r) -> do
            case r of
                Valid -> do
                    return (lbl, True) 
                _     -> do
                    return (lbl, False)
    return $ M.fromList rs
