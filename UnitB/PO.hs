{-# LANGUAGE BangPatterns,OverloadedStrings,ImplicitParams #-}
    -- Behavior hiding
module UnitB.PO 
    ( proof_obligation, theory_po
    , step_ctx, evt_live_ctx
    , theory_ctx, theory_facts
    , evt_saf_ctx, invariants, assert_ctx
    , str_verify_machine, raw_machine_pos
    , verify_all, prop_saf, prop_tr
    , tr_wd_po, saf_wd_po
    , verify_changes, verify_machine
    , smoke_test_machine, dump, used_types )
where

    -- Modules
import Logic.Proof
import           Logic.Proof.POGenerator hiding ( variables )
import qualified Logic.Proof.POGenerator as POG
import Logic.Theory
import Logic.WellDefinedness

import UnitB.AST
import UnitB.Expr

import Z3.Z3

    -- Libraries
import Control.Lens hiding (indices,Context,Context',(.=))
import Control.Monad hiding (guard)

import           Data.Either
import           Data.Either.Combinators
import           Data.Map as M hiding 
                    ( map, foldl, foldr
                    , delete, filter, null
                    , (\\), mapMaybe )
import qualified Data.Map as M
import           Data.List as L hiding (inits, union,insert)
import           Data.List.NonEmpty as NE hiding (inits,(!!))
import           Data.List.Utils as LU (replace)
import qualified Data.Traversable as T

import System.IO

import Utilities.Format
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

-- forWithKeyM = flip traverse

assert_ctx :: RawMachine -> Context
assert_ctx m =
          (Context M.empty (view' variables m `M.union` view' del_vars m) M.empty M.empty M.empty)

step_ctx :: RawMachine -> Context
step_ctx m = merge_all_ctx 
        [  Context M.empty (prime_all $ vars `M.union` abs) M.empty M.empty M.empty
        ,  assert_ctx m ]
    where
        abs  = m!.abs_vars
        vars = m!.variables
        prime_all vs = mapKeys (++ "'") $ M.map prime_var vs
        prime_var (Var n t) = (Var (n ++ "@prime") t)

abstract_step_ctx :: RawMachine -> Context
abstract_step_ctx m = merge_all_ctx 
        [  Context M.empty (prime_all $ view' variables m) M.empty M.empty M.empty
        ,  assert_ctx m ]
    where
        prime_all vs = mapKeys (++ "'") $ M.map prime_var vs
        prime_var (Var n t) = (Var (n ++ "@prime") t)

evt_saf_ctx :: HasConcrEvent' event RawExpr => event -> Context
evt_saf_ctx evt  = Context M.empty (evt^.new.params) M.empty M.empty M.empty

evt_live_ctx :: HasConcrEvent' event RawExpr => event -> Context
evt_live_ctx evt = Context M.empty (evt^.new.indices) M.empty M.empty M.empty

primed_vars :: Map String Var -> POCtx ()
primed_vars = POG.variables . M.mapKeys (++"'") . M.map prime

skipOrLabel :: SkipOrEvent -> Label
skipOrLabel lbl = fromRight "SKIP" $ as_label <$> lbl

invariants :: RawMachine -> Map Label RawExpr
invariants m = 
                  (_inv p0) 
        `M.union` (_inv_thm p0) 
        `M.union` (_inv p1)
        `M.union` (_inv_thm p1)
    where
        p0 = m!.props
        p1 = m!.inh_props

invariants_only :: RawMachine -> Map Label RawExpr
invariants_only m = 
                  (_inv p0) 
        `M.union` (_inv p1)
    where
        p0 = m!.props
        p1 = m!.inh_props

raw_machine_pos :: IsExpr expr => Machine' expr -> (Map Label Sequent)
raw_machine_pos m' = eval_generator $ 
                with (do
                        _context $ theory_ctx (m!.theory)
                        set_syntactic_props syn
                        nameless_hyps $ M.elems unnamed 
                        named_hyps $ named_f
                        ) $ do
                    forM_ (M.toList $ _transient p) $ \tr -> do
                        prop_tr m tr
                        tr_wd_po m tr
                    forM_ (M.toList $ _safety p) $ \saf -> do
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
                        replace_csched_po m ev
                        weaken_csched_po  m ev
                        replace_fsched_po m ev
                    forM_  (M.toList $ nonSkipUpwards m) $ \ev -> do
                        evt_wd_po m ev
                        wit_wd_po m ev
                        wit_fis_po m ev
                        fis_po m ev
                    mapM_ (prog_wd_po m) $ M.toList $ _progress p
                    mapM_ (ref_po m) $ M.toList $ m!.derivation
    where 
        m = raw m'
        syn = mconcat $ L.map (view syntacticThm) $ all_theories $ m!.theory
        p = m!.props
        unnamed = theory_facts (m!.theory) `M.difference` named_f
        named_f = theory_facts (m!.theory) { _extends = M.empty }

proof_obligation :: IsExpr expr => Machine' expr -> Either [Error] (Map Label Sequent)
proof_obligation m = do
        let pos = raw_machine_pos m
        forM_ (M.toList $ m!.props.proofs) (\(lbl,p) -> do
            let li = line_info p
            if lbl `M.member` pos
                then return ()
                else Left [Error 
                    (format "a proof is provided for non-existant proof obligation {0}" lbl)
                        li])
        xs <- forM (M.toList pos) (\(lbl,po) -> do
            case M.lookup lbl $ m!.props.proofs of
                Just c ->
                    proof_po c lbl po
                Nothing -> 
                    return [(lbl,po)])
        ys <- theory_po (m!.theory)
        return $ M.fromList (concat xs) `M.union` ys

ref_po :: RawMachine -> (ProgId, Rule) -> M ()
ref_po m (lbl, Rule r) = 
        with (do
                prefix_label $ label $ m!.name
                prefix_label $ as_label lbl
                prefix_label "REF"
                prefix_label $ rule_name r) 
            $ refinement_po r m

theory_po :: Theory -> Either [Error] (Map Label Sequent)
theory_po th = do
        xs <- mapM (uncurry f) $ M.toList $ M.mapWithKey g thm
        return $ M.fromList $ concat xs
    where
--        axm = M.filterKeys (not . (`S.member` theorems th)) $ fact th
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

init_sim_po :: RawMachine -> M ()
init_sim_po m = 
    with 
        (do prefix_label $ _name m
            prefix_label "INIT"
            prefix_label "SIM"
            _context (assert_ctx m)
            named_hyps $ m!.inits
            named_hyps $ M.mapKeys (label . view name) $ m!.init_witness)
        (forM_ (M.toList $ m!.del_inits) $ \(lbl,p) -> do
            emit_goal assert [lbl] p)

init_wit_wd_po :: RawMachine -> M ()
init_wit_wd_po m =
    with 
        (do prefix_label $ _name m
            _context (assert_ctx m)
            named_hyps $ m!.inits)
        (emit_goal assert ["INIT/WWD"] 
            (well_definedness $ zall $ getExpr <$> m!.init_witness))

init_witness_fis_po :: RawMachine -> M ()
init_witness_fis_po m =
    with 
        (do prefix_label $ _name m
            _context (assert_ctx m)
            named_hyps $ m!.inits)
        (emit_exist_goal assert ["INIT/WFIS"] 
            (M.elems $ (view' abs_vars m)  `M.difference` (view' variables m))
            (M.elems $ m!.init_witness))

init_fis_po :: RawMachine -> M ()
init_fis_po m = 
    with 
        (do prefix_label $ _name m
            _context (assert_ctx m) )
        (emit_exist_goal assert [init_fis_lbl] 
            (M.elems $ (view' variables m)  `M.union` (view' abs_vars m)) 
            (M.elems $ m!.inits))

type M = POGen

expected_leadsto_po :: ProgressProp' RawExpr -> ProgressProp' RawExpr -> M ()
expected_leadsto_po (LeadsTo vs p0 q0) (LeadsTo vs' p1 q1) = do
        emit_goal assert ["lhs"] $ zforall (vs ++ vs') p0 p1
        emit_goal assert ["rhs"] $ zforall (vs ++ vs') q1 q0

assume_old_guard :: IsExpr expr => EventMerging expr -> POCtx ()
assume_old_guard evt = do
    case evt^.abstract_evts of
        e :| [] -> named_hyps $ e^._2.old.guards
        _ :| (_:_) -> return ()

prop_tr :: RawMachine -> (Label, RawTransient) -> M ()
prop_tr m (pname, Tr fv xp' evt_lbl tr_hint) = assert (null inds) $ do
            with (do
                    prefix_label (_name m)
                    prefix_label $ composite_label [tr_lbl, pname]
                    ctx 
                    named_hyps $ invariants m) $ do
                with (named_hyps $ singleton pname xp) $
                    forM_ (M.toList hint) $ \(v,(t,e)) -> do
                        emit_exist_goal assert ["WFIS",label v] [prime $ Var v t] [e]
                zipWithM_ stuff evt_lbl es
                following
    where
        TrHint hint' lt_fine = tr_hint
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
                enablement = emit_goal assert [as_label evt_lbl, "EN"] 
                            (          asExpr xp 
                            `zimplies` (new_dummy ind $ zall $ asExpr <$> sch0))

                new_defs = flip L.map (M.elems ind1) 
                        $ \(Var n t) -> (n ++ "@param", mk_fun [] (n ++ "@param") [] t)
                new_hyps = flip L.map (M.toList hint)
                        $ \(x,(_,e)) -> rename (x ++ "@prime") (x ++ "@param") e
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
                        emit_goal assert [as_label evt_lbl,"NEG"] 
                            $ xp `zimplies` (znot $ primed (m!.variables) xp) 
        all_ind = M.elems $ M.unions $ fv : L.zipWith local_ind evt_lbl es
        inds    = L.map (add_suffix "@param") $ M.elems 
                        $ M.unions (L.map (view indices) es) `M.difference` hint
        es      = L.map (upward_event m.Right) evt_lbl
        
        local_ind :: EventId -> RawEventMerging -> Map String Var
        local_ind lbl e = M.mapKeys (++ suff) $ M.map (add_suffix suff) $ e^.indices
            where
                suff = mk_suff $ "@" ++ show lbl
        new_ind :: EventId -> RawEventMerging -> RawExpr -> RawExpr
        new_ind lbl e = make_unique suff (e^.indices)
            where
                suff = mk_suff $ "@" ++ show lbl
            -- (M.elems ind) 
        tagged_sched :: EventId -> RawEventMerging -> Map Label RawExpr
        tagged_sched lbl e = M.map (new_ind lbl e) $ e^.new.coarse_sched & traverse %~ asExpr
        all_csch  = concatMap M.elems $ L.zipWith tagged_sched evt_lbl es
            
            -- we take the disjunction of the fine schedules of 
            -- all the events involved in the transient predicate
        all_fsch  =
            zsome $ L.zipWith (\lbl e -> (new_ind lbl e . zall) $ e^.new.fine_sched & traverse %~ asExpr) evt_lbl es
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
                        | otherwise -> error $ format (
                               "transient predicate {0}'s side condition doesn't "
                            ++ "match the fine schedule of event {1}"
                            ) pname (intercalate "," $ L.map show evt_lbl)
                    Nothing
                        | not $ all_fsch == ztrue ->
                            emit_goal assert [] $ zforall all_ind
                                    (zall $ xp : all_csch) 
                                    all_fsch
                        | otherwise -> return ()
        ctx = do
                _context $ assert_ctx m 
                _context $ step_ctx m 
                dummy
        dummy = POG.variables fv
        progs = (m!.props.progress) `M.union` (m!.inh_props.progress)
        mk_suff suff = LU.replace ":" "-" suff

prop_co :: RawMachine -> (Label, Constraint' RawExpr) -> M ()
prop_co m (pname, Co fv xp) = 
    with
        (do prefix_label $ _name m
            _context $ step_ctx m
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
                (emit_goal assert [skipOrLabel evt_lbl,co_lbl,pname] $ forall_fv xp)
    where
        evts = M.toList (conc_events m)
        forall_fv xp = if L.null fv then xp else zforall fv ztrue xp

prop_saf :: RawMachine -> (Label, SafetyProp' RawExpr) -> M ()
prop_saf m (pname, Unless fv p q excp) = 
    with
        (do prefix_label $ _name m
            _context $ step_ctx m
            POG.variables $ symbol_table fv
            named_hyps $ invariants m)
        $ forM_ evts $ \(evt_lbl,evt) -> do
            let grd  = evt^.new.guards
                act  = ba_predicate m evt
                ind = maybe M.empty (view indices . (conc_events m !)) (Right <$> excp)
                fvs = symbol_table fv 
                neq x = znot $ Word x `zeq` Word (suff x)
                rng = maybe ztrue 
                        (const $ zsome $ L.map neq $ elems inter)
                        excp
                inter = fvs `M.intersection` ind
                diff  = fvs `M.difference` ind
            with 
                (do named_hyps $ grd
                    named_hyps $ act
                    -- nameless_hyps $ _ $ evt^.abstract_evts
                    POG.variables $ evt^.new.indices
                    POG.variables $ evt^.new.params)
                (emit_goal assert [as_label evt_lbl,"SAF",pname] $ 
                    zforall (elems diff ++ L.map suff (elems ind))
                        rng
                        $ new_dummy inter $
                            zimplies (p `zand` znot q) 
                                     (primed vars $ p `zor` q))
    where
        evts = rights $ L.map (\(x,y) -> (,y) <$> x) $ M.toList $ all_upwards m
        vars = m!.variables
        suff = add_suffix "@param"

inv_po :: RawMachine -> (Label, RawExpr) -> M ()
inv_po m (pname, xp) = 
    do  with (do prefix_label $ _name m
                 _context $ step_ctx m
                 named_hyps $ invariants m)
            $ forM_ (M.toList $ nonSkipUpwards m) $ \(evt_lbl,evt) -> do
                let grd  = evt^.new.guards
                    act  = ba_predicate m evt
                with 
                    (do named_hyps $ grd
                        assume_old_guard evt
                        named_hyps $ act
                        named_hyps $ M.map ba_pred $ evt^.abs_actions
                        POG.variables $ evt^.new.indices
                        POG.variables $ evt^.new.params)
                    (emit_goal assert [as_label evt_lbl,inv_lbl,pname] 
                        (primed (view' variables m `M.union` view' abs_vars m) xp))
        with (do _context $ assert_ctx m
                 named_hyps $ m!.inits 
                 named_hyps $ M.mapKeys (label . view name) (m!.init_witness))
            $ emit_goal assert [_name m, inv_init_lbl, pname] xp

wit_wd_po :: RawMachine -> (EventId, RawEventMerging) -> M ()
wit_wd_po m (lbl, evt) = 
        with (do _context $ step_ctx m
                 POG.variables $ evt^.new.indices
                 POG.variables $ evt^.new.params
                 named_hyps $ invariants m
                 prefix_label $ _name m
                 prefix_label $ as_label lbl
                 named_hyps $ evt^.new.guards
                 -- nameless_hyps $ _ $ evt^.abstract_evts
                 named_hyps $ ba_predicate' (m!.variables) (evt^.new.actions))
            (emit_goal assert ["WWD"] $ well_definedness $ zall 
                $ M.elems $ evt^.witness)

wit_fis_po :: RawMachine -> (EventId, RawEventMerging) -> M ()
wit_fis_po m (lbl, evt) = 
        with (do _context $ step_ctx m
                 POG.variables $ m!.del_vars
                 POG.variables $ evt^.new.indices
                 POG.variables $ evt^.new.params
                 named_hyps $ invariants m
                 prefix_label $ _name m
                 prefix_label $ as_label lbl
                 named_hyps $ evt^.new.guards
                 -- nameless_hyps $ _ $ evt^.abstract_evts
                 named_hyps $ ba_predicate' (m!.variables) (evt^.new.actions))
            (emit_exist_goal assert ["WFIS"] pvar 
                $ M.elems $ evt^.witness)
    where
        pvar = L.map prime $ M.elems $ view' abs_vars m `M.difference` view' variables m

replace_csched_po :: RawMachine -> (EventId,RawEventSplitting) -> M ()
replace_csched_po m (lbl,evt') = do 
        -- TODO: generate the safety property rather than reading it
    case evt' of 
        EvtS ae (ce :| []) -> do
            let evt = EvtRef ae ce
            with (do
                    prefix_label $ _name m
                    prefix_label $ as_label lbl
                    prefix_label "C_SCH/delay"
                    _context $ assert_ctx m
                    _context $ step_ctx m
                    POG.variables $ evt^.new.indices
                    named_hyps $ invariants m ) $ do
                let old_c = evt^.old.coarse_sched
                    old_f = evt^.old.fine_sched
                forM_ (L.zip [0..] $ evt^.c_sched_ref) $ \(i,ref) -> do
                    let (plbl,prog) = ref^.sch_prog
                        (slbl,saf)  = ref^.sch_saf
                        keep_c      = (evt^.new.coarse_sched) `M.intersection` view keep ref
                        new_part_c  = ((evt^.added.coarse_sched) `M.intersection` view add ref) `M.union` keep_c
                        nb  = label $ show (i :: Int)
                        LeadsTo vs p0 q0  = prog
                        Unless us p1 q1 _ = saf
                    with (do
                            POG.variables $ symbol_table vs
                            named_hyps old_c
                            named_hyps old_f) $ 
                        emit_goal assert [nb,"prog",plbl,"lhs"] p0
                    with (do
                            POG.variables $ symbol_table vs) $
                        forM_ (M.toList new_part_c) $ \(lbl,sch) -> do
                            emit_goal assert [nb,"prog",plbl,"rhs",lbl] $ $typeCheck$
                                Right q0 .=> Right sch
                    with (do
                            POG.variables $ symbol_table us) $ do
                        emit_goal assert [nb,"saf",slbl,"lhs"] $ $typeCheck$
                                Right p1 .==. mzall (M.map Right new_part_c)
                        emit_goal assert [nb,"saf",slbl,"rhs"] $ $typeCheck$
                                Right q1 .=> mznot (mzall $ M.map Right old_c)
                            -- the above used to include .=> ... \/ not old_f
                            -- it does not seem sound and I removed it
                            -- it broke one of the test cases
        _ -> assert (L.null (evt'^.c_sched_ref)) (return ())

weaken_csched_po :: RawMachine -> (EventId,RawEventSplitting) -> M ()
weaken_csched_po m (lbl,evt) = do
    -- case evt' of 
    --     EvtS ae (ce :| []) -> do
            let -- evt = EvtRef ae ce 
                weaken_sch = do
                        e <- evt^.evt_pairs
                        return $ (e^.added.coarse_sched) `M.difference` M.unions (L.map (view add) $ e^.c_sched_ref)
                -- weaken_sch  = case weaken_sch' of
                --                 m :| [] -> _
                --                 ms -> _
                -- weaken_sch = (evt^.added.coarse_sched) `M.difference` M.unions (L.map add $ evt^.c_sched_ref)

                old_c = evt^.old.coarse_sched
            with (do
                    prefix_label $ _name m
                    prefix_label $ as_label lbl
                    prefix_label "C_SCH/weaken"
                    _context $ assert_ctx m
                    _context $ step_ctx m
                    POG.variables $ evt^.indices
                    T.forM (evt^.evt_pairs) $ \e -> -- indices
                        POG.variables $ e^.added.indices
                    named_hyps $ invariants m 
                        -- old version admits old_f as assumption
                        -- why is it correct or needed?
                        -- named_hyps old_f
                    named_hyps old_c) $ do
                case weaken_sch of
                    m :| [] -> 
                        forM_ (M.toList m) $ \(lbl,sch) -> do
                            emit_goal assert [lbl] sch
                    ms -> 
                        emit_goal assert [] $ zsome $ NE.map zall ms

replace_fsched_po :: RawMachine -> (EventId,RawEventSplitting) -> M ()
replace_fsched_po m (lbl,aevt) = do
        let evts   = aevt^.evt_pairs.to NE.toList
            -- _ = _
            evts'  = L.zip (NE.toList $ aevt^.multiConcrete.to (NE.map fst)) evts
            -- evt   = _
            old_c  = unions $ L.map (view $ old.coarse_sched) evts
            new_c  = L.nub $ concatMap (elems . view (new.coarse_sched)) evts
            old_f  = unions $ L.map (view $ old.fine_sched) evts
            new_fs = L.map (view $ new.fine_sched) evts
        with (do
                prefix_label $ _name m
                prefix_label $ as_label lbl
                prefix_label "F_SCH/replace"
                -- POG.variables $ _^.new.indices
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
                    emit_goal assert ["prog",plbl,"lhs"] p0
                forM_ evts' $ \(clbl,evt) -> 
                    with (do
                            POG.variables $ evt^.total.indices
                            named_hyps $ evt^.new.coarse_sched
                            named_hyps $ evt^.new.fine_sched ) $
                        forM_ (M.toList $ evt^.deleted.fine_sched) $ \(lbl,sch) ->
                            emit_goal assert ["str",lbl,skipOrLabel clbl] sch 
                case new_fs of
                  [new_f] -> do
                    with (do
                            POG.variables $ evts^.traverse.new.indices
                            POG.variables $ symbol_table vs) $ do
                        forM_ (M.toList new_f) $ \(lbl,sch) -> 
                            emit_goal assert ["prog",plbl,"rhs",lbl] $
                                    q0 `zimplies` sch
                  _ -> do
                    with (do
                            POG.variables $ evts^.traverse.new.indices
                            POG.variables $ symbol_table vs) $ do
                        emit_goal assert ["prog",plbl,"rhs"] $
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
                        emit_goal assert ["eqv"] $ $typeCheck$
                            Right (zsome add_f) .=. Right (zsome del_f)

intersections :: Ord k => [Map k a] -> Map k a
intersections []  = error "intersection of empty list is undefined"
intersections [x] = x
intersections (x:xs) = x `intersection` intersections xs                                

strengthen_guard_po :: RawMachine -> (EventId,RawEventMerging) -> M ()
strengthen_guard_po m (lbl,evt) = 
        with (do
            prefix_label $ _name m
            prefix_label $ as_label lbl
            prefix_label "GRD/str"
            _context $ assert_ctx m
            _context $ step_ctx m
            POG.variables $ evt^.new.indices
            POG.variables $ evt^.new.params 
            named_hyps $ invariants m 
            named_hyps $ evt^.new.guards ) $ do
        case evt^.evt_pairs of
          evt :| [] ->
            forM_ (M.toList $ evt^.deleted.guards) $ \(lbl,grd) -> do
                emit_goal assert [lbl] grd
          es -> emit_goal assert [] $ zsome $ NE.map (zall . M.elems . view (deleted.guards)) es

sim_po :: RawMachine -> (EventId, RawEventMerging) -> M ()
sim_po m (lbl, evt) = 
        with (do
                _context $ step_ctx m
                POG.variables $ evt^.new.indices
                POG.variables $ evt^.new.params 
                prefix_label $ _name m
                prefix_label $ as_label lbl
                prefix_label "SIM"
                named_hyps (evt^.new.guards)
                -- nameless_hyps $ _ $ evt^.abstract_evts
                named_hyps (ba_predicate m evt) ) $
            forM_ (M.toList $ evt^.deleted_actions) $ \(albl,act) ->
                emit_goal assert [albl] $ ba_pred act

fis_po :: RawMachine -> (EventId, RawEventMerging) -> M ()
fis_po m (lbl, evt) = 
        with (do _context $ assert_ctx m
                 -- TODO: Only check feasibility of
                 -- (concrete) non-deterministic assignments
                 _context $ abstract_step_ctx m
                 POG.variables $ evt^.indices
                 POG.variables $ evt^.params 
                 POG.variables $ m!.del_vars
                 primed_vars $ m!.del_vars
                 named_hyps $ invariants m
                 -- nameless_hyps $ _ $ evt^.abstract_evts
                 named_hyps $ ba_predicate' (m!.abs_vars) $ evt^.abs_actions
                 named_hyps $ evt^.new.guards)
            (emit_exist_goal assert [_name m, as_label lbl, fis_lbl] pvar 
                $ M.elems $ ba_predicate' (m!.variables) $ evt^.new_actions)
    where
        pvar = L.map prime $ M.elems $ view' variables m `M.union` view' abs_vars m

tr_wd_po :: RawMachine -> (Label, RawTransient) -> M ()
tr_wd_po  m (lbl, Tr vs p _ (TrHint wit _)) = 
        with (do prefix_label $ _name m
                 prefix_label lbl
                 prefix_label "TR"
                 _context $ step_ctx m
                 named_hyps $ invariants m) $
            do  emit_goal assert ["WD"]
                    $ well_definedness $ zforall (elems vs) ztrue p
                forM_ (M.toList wit) $ \(n,(t,e)) -> 
                    with (do
                        POG.variables $ 
                                    symbol_table [prime $ Var n t]
                            `M.union` vs
                        POG.named_hyps $ singleton lbl p
                        ) $
                    emit_goal assert ["WD","witness",label n] $ 
                        well_definedness e

prog_wd_po :: RawMachine -> (ProgId, ProgressProp' RawExpr) -> M ()
prog_wd_po m (lbl, LeadsTo vs p q) = 
        with (do prefix_label $ _name m
                 prefix_label $ as_label lbl
                 prefix_label "PROG"
                 _context $ step_ctx m
                 named_hyps $ invariants m) $
            do  emit_goal assert ["WD","lhs"]
                    $ well_definedness $ zforall vs ztrue p
                emit_goal assert ["WD","rhs"]
                    $ well_definedness $ zforall vs ztrue q

saf_wd_po :: RawMachine -> (Label, SafetyProp' RawExpr) -> M ()
saf_wd_po m (lbl, Unless vs p q _) = 
        with (do prefix_label $ _name m
                 prefix_label lbl
                 prefix_label "SAF"
                 _context $ step_ctx m
                 named_hyps $ invariants m) $
            do  emit_goal assert ["WD","lhs"]
                    $ zforall vs ztrue $ (znot q) `zimplies` (well_definedness p)
                emit_goal assert ["WD","rhs"]
                    $ well_definedness $ zforall vs ztrue q

co_wd_po :: RawMachine -> (Label, Constraint' RawExpr) -> M ()
co_wd_po m (lbl, Co vs p) = 
        with (do prefix_label $ _name m
                 prefix_label lbl
                 prefix_label "CO"
                 _context $ step_ctx m
                 nameless_hyps $ M.elems $
                    M.map (primed $ view' variables m) $ invariants m
                 named_hyps $ invariants m)
             $ emit_goal assert ["WD"]
                $ well_definedness $ zforall vs ztrue p

inv_wd_po :: RawMachine -> M ()
inv_wd_po m = 
        with (do prefix_label $ _name m
                 _context $ assert_ctx m
                 named_hyps $ m!.inh_props.inv
                 named_hyps $ m!.inh_props.inv_thm)
            $ emit_goal assert ["INV", "WD"] 
                $ well_definedness $ zall $ m!.props.inv

init_wd_po :: RawMachine -> M ()
init_wd_po m = 
        with (do prefix_label $ _name m
                 _context $ assert_ctx m
                 named_hyps $ m!.inh_props.inv
                 named_hyps $ m!.inh_props.inv_thm)
            $ emit_goal assert ["INIT", "WD"] 
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
            emit_goal assert [lbl] 
                $ well_definedness 
                $ zall add
    else
        emit_goal assert [lbl] 
            $ well_definedness 
            $ zall new

evt_wd_po :: RawMachine -> (EventId, RawEventMerging) -> M ()
evt_wd_po m (lbl, evts) = 
        with (do prefix_label $ _name m
                 prefix_label $ as_label lbl
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
                    (evts^.new.guards)
              -- es -> _
            with (POG.variables $ evts^.new.params) $ do
                with (do prefix_label "ACT"
                         assume_old_guard evts
                         named_hyps $ evts^.new.guards
                         _context $ step_ctx m) $ do
                    let p k _ = k `M.notMember` (evts^.old_actions)
                    forM_ (M.toList $ M.filterWithKey p $ evts^.new.actions) $ \(tag,bap) -> 
                        emit_goal assert [tag] 
                            $ well_definedness $ ba_pred bap

evt_eql_po :: RawMachine -> (EventId, RawEventMerging) -> M ()
evt_eql_po  m (_lbl, evts) = 
    with (do prefix_label $ _name m
             _context $ step_ctx m
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
                emit_goal assert [label $ v^.name] 
                    $ Word (prime v) `zeq` Word v )

sch_po :: RawMachine -> (EventId, RawEventMerging) -> M ()
sch_po m (lbl, evts) = 
    forM_ (evts^.evt_pairs.to NE.toList) $ \evt ->
        with (do prefix_label $ _name m
                 prefix_label $ as_label lbl
                 prefix_label sch_lbl
                 _context $ assert_ctx m
                 _context $ evt_live_ctx evt
                 POG.variables ind
                 named_hyps hyp) $ do
            let removed_sched sch = not $ M.null $ evt^.deleted.sch
                added_grd = not $ M.null $ evt^.added.guards
                removed_c_sch = removed_sched coarse_sched
                removed_f_sch = removed_sched fine_sched
            if M.null param
                then do 
                    when (removed_c_sch || removed_f_sch) $
                        forM_ (M.toList $ evt^.kept.guards) 
                            $ \(lbl,grd) -> 
                            emit_goal assert [lbl] grd  
                    forM_ (M.toList $ evt^.added.guards) 
                        $ \(lbl,grd) -> 
                        emit_goal assert [lbl] grd  
            else if removed_c_sch || removed_f_sch || added_grd
                then emit_exist_goal assert [] (M.elems param) (M.elems $ evt^.new.guards)
                else return ()
    where
        -- grd   = evt^.new.guards
        c_sch = evts^.new.coarse_sched
        f_sch = evts^.new.fine_sched
        param = evts^.new.params
        ind   = (evts^.new.indices) `merge` (evts^.new.params)
        hyp   = invariants m `M.union` f_sch `M.union` c_sch

thm_wd_po :: RawMachine -> M ()
thm_wd_po m = 
        with (do prefix_label $ _name m
                 _context $ assert_ctx m
                 named_hyps $ m!.inh_props.inv
                 named_hyps $ m!.inh_props.inv_thm
                 named_hyps $ m!.props.inv) $ do
            let wd = well_definedness $ zall $ m!.props.inv_thm
            unless (wd == ztrue) $ 
                emit_goal assert ["THM", "WD"] wd 


thm_po :: RawMachine -> (Label, RawExpr) -> M ()
thm_po m (lbl, xp) = 
    with (do
            prefix_label $ _name m
            prefix_label thm_lbl
            prefix_label lbl
            _context $ assert_ctx m
            named_hyps inv)
        $ emit_goal assert [] xp
    where
        inv = invariants_only m

add_suffix :: String -> Var -> Var
add_suffix suf (Var n t) = Var (n ++ suf) t

new_dummy :: Map String Var -> RawExpr -> RawExpr
new_dummy = make_unique "@param"

verify_machine :: Machine -> IO (Int, Int)
verify_machine m = do
    (s,i,j) <- str_verify_machine m
    putStrLn s
    return (i,j)

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
                hPutStrLn h (format "(echo \"> {0}\")\n(push)" lbl)
                hPutStrLn h (L.unlines $ L.map f $ z3_code po)
                hPutStrLn h "(pop)"
                hPutStrLn h ("; end of " ++ show lbl)
                ) )
    where
        f x = pretty_print' x

verify_all :: Map Label Sequent -> IO (Map Label Bool)
verify_all pos' = do
    let xs         = M.toList pos'
        lbls       = L.map fst xs 
    ys <- map_failures (lbls !!) 
            $ discharge_all xs
    rs <- forM (L.zip lbls ys) $ \(lbl,r) -> do
--    rs <- forM xs $ \(lbl, po) -> do
--            r <- discharge po
            case r of
                Valid -> do
                    return (lbl, True) 
                _     -> do
                    return (lbl, False)
    return $ M.fromList rs

verify_changes :: Machine -> Map Label (Bool,Sequent) -> IO (Map Label (Bool,Sequent), String,Int)
verify_changes m old_pos = do
        case proof_obligation m of
            Right pos -> do
--                dump (show $ _name m) pos
                let new_pos = differenceWith f pos old_pos
                res <- verify_all new_pos
                let { h k p0 = (
                    case M.lookup k res of
                        Just b  -> (b,p0)
                        Nothing -> old_pos ! k) }
                let all_pos = M.mapWithKey h pos 
                (res,_,_) <- format_result (M.map fst all_pos)
                return (all_pos,res, M.size new_pos)
            Left msgs -> 
                return (old_pos,L.unlines $ L.map report msgs,0)
    where
        f p0 (_,p1)
            | p0 == p1  = Nothing 
            | otherwise = Just p0
                 
str_verify_machine :: IsExpr expr => Machine' expr -> IO (String,Int,Int)
str_verify_machine m = 
        case proof_obligation m of
            Right pos -> do
--                dump (show $ _name m) pos
                xs <- verify_all pos
                format_result xs
            Left msgs -> return (L.unlines $ L.map report msgs,0,0)

smoke_test_machine :: Machine -> IO (String)
smoke_test_machine m =
        case proof_obligation m of 
            Right pos -> do
                rs <- flip filterM (M.toList pos) $ \(lbl,po) -> do
                    r <- smoke_test lbl po
                    return $ r == Valid
                return $ L.unlines $ L.map (show . fst) rs
            Left msgs -> return (L.unlines $ L.map report msgs)

format_result :: Map Label Bool -> IO (String,Int,Int)
format_result xs' = do
        let rs    = L.map f $ M.toList xs'
            total = L.length rs
            passed = L.length $ L.filter fst rs
            xs = "passed " ++ (show passed) ++ " / " ++ show total
            ys = L.map snd rs ++ [xs]
        return (L.unlines ys, passed, total)
    where
        f (y,True)  = (True, "  o  " ++ show y)
        f (y,False) = (False," xxx " ++ show y)
