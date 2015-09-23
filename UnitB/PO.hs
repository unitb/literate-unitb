{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
    -- Behavior hiding
module UnitB.PO 
    ( proof_obligation, theory_po
    , step_ctx, evt_live_ctx
    , theory_ctx, theory_facts
    , evt_saf_ctx, invariants, assert_ctx
    , str_verify_machine, raw_machine_pos
    , verify_all, prop_saf, prop_tr
    , tr_wd_po, saf_wd_po
    , check, verify_changes, verify_machine
    , smoke_test_machine, dump, used_types )
where

    -- Modules
import Logic.Expr
import Logic.Proof
import           Logic.Proof.POGenerator hiding ( variables )
import qualified Logic.Proof.POGenerator as POG
import Logic.Theory hiding (assert)
import Logic.WellDefinedness

import           UnitB.AST

import Z3.Z3

    -- Libraries
-- import Control.Arrow
import Control.Exception
import Control.Lens hiding (indices,Context,Context',(.=))
import Control.Monad hiding (guard)
import Control.Monad.Trans
import Control.Monad.Trans.Either

import           Data.Map as M hiding 
                    ( map, foldl, foldr
                    , delete, filter, null
                    , (\\), mapMaybe )
import qualified Data.Map as M
import           Data.Monoid
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

assert_ctx :: Machine -> Context
assert_ctx m =
          (Context M.empty (variables m `M.union` del_vars m) M.empty M.empty M.empty)
step_ctx :: Machine -> Context
step_ctx m = merge_all_ctx 
        [  Context M.empty (prime_all $ variables m `M.union` abs_vars m) M.empty M.empty M.empty
        ,  assert_ctx m ]
    where
        prime_all vs = mapKeys (++ "'") $ M.map prime_var vs
        prime_var (Var n t) = (Var (n ++ "@prime") t)

evt_saf_ctx :: HasConcrEvent event => event -> Context
evt_saf_ctx evt  = Context M.empty (evt^.new.params) M.empty M.empty M.empty

evt_live_ctx :: HasConcrEvent event => event -> Context
evt_live_ctx evt = Context M.empty (evt^.new.indices) M.empty M.empty M.empty



invariants :: Machine -> Map Label Expr
invariants m = 
                  (_inv p0) 
        `M.union` (_inv_thm p0) 
        `M.union` (_inv p1)
        `M.union` (_inv_thm p1)
    where
        p0 = props m
        p1 = inh_props m

invariants_only :: Machine -> Map Label Expr
invariants_only m = 
                   (_inv p0) 
        `M.union` (_inv p1)
    where
        p0 = props m
        p1 = inh_props m 

raw_machine_pos :: Machine -> (Map Label Sequent)
raw_machine_pos m = eval_generator $ 
                with (do
                        _context $ theory_ctx (theory m)
                        set_syntactic_props syn
                        nameless_hyps $ M.elems unnamed 
                        named_hyps $ named_f) $ do
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
                    forM_  (M.toList $ all_upwards m) $ \ev -> do
                        strengthen_guard_po m ev
                        evt_wd_po m ev
                        evt_eql_po m ev
                        sch_po m ev
                    -- forM_ (all_refs m) $ \ev -> do
                    forM_  (M.toList $ all_downwards m) $ \ev -> do
                        replace_csched_po m ev
                        weaken_csched_po  m ev
                        replace_fsched_po m ev
                    forM_ (all_refs m) $ sim_po m
                    forM_  (M.toList $ all_upwards m) $ \ev -> do
                        wit_wd_po m ev
                        wit_fis_po m ev
                        fis_po m ev
                    mapM_ (prog_wd_po m) $ M.toList $ _progress p
                    mapM_ (ref_po m) $ M.toList $ derivation m
    where          
        syn = mconcat $ L.map (view syntacticThm) $ all_theories $ theory m
        p = props m
        unnamed = theory_facts (theory m) `M.difference` named_f
        named_f = theory_facts (theory m) { extends = M.empty }

proof_obligation :: Machine -> Either [Error] (Map Label Sequent)
proof_obligation m = do
        let pos = raw_machine_pos m
        forM_ (M.toList $ _proofs $ props $ m) (\(lbl,p) -> do
            let li = line_info p
            if lbl `M.member` pos
                then return ()
                else Left [Error 
                    (format "a proof is provided for non-existant proof obligation {0}" lbl)
                        li])
        xs <- forM (M.toList pos) (\(lbl,po) -> do
            case M.lookup lbl $ _proofs $ props $ m of
                Just c ->
                    proof_po c lbl po
                Nothing -> 
                    return [(lbl,po)])
        ys <- theory_po (theory m)
        return $ M.fromList (concat xs) `M.union` ys

ref_po :: Machine -> (Label, Rule) -> M ()
ref_po m (lbl, Rule r) = 
        with (do
                prefix_label $ _name m
                prefix_label lbl
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
                        [ (x,[(y,())]) | (x,y) <- thm_depend th ]
        depend x  = thm `M.intersection` findWithDefault M.empty x dep
        (thm,axm) = M.partitionWithKey p $ th ^. fact
        p k _     = k `M.member` theorems th

        g lbl x   = empty_sequent & named .~ (depend lbl `M.union` axm) 
                                  & goal .~ x
        keys k    = composite_label ["THM",k]
        f lbl po = result
          where
            result = case keys lbl `M.lookup` theorems th of
                        Just (Just proof) -> do
                            xs <- proof_po proof (keys lbl) po'
                            return xs
                        _ -> return [(keys lbl, po')]
            po' = po & context  %~ (`merge_ctx` theory_ctx th)
                     & nameless %~ (concatMap 
                            (M.elems . theory_facts) 
                            (elems $ extends th) ++) 

init_sim_po :: Machine -> M ()
init_sim_po m = 
    with 
        (do prefix_label $ _name m
            prefix_label "INIT"
            prefix_label "SIM"
            _context (assert_ctx m)
            named_hyps $ inits m
            named_hyps $ M.mapKeys (label . name) $ init_witness m)
        (forM_ (M.toList $ del_inits m) $ \(lbl,p) -> do
            emit_goal [lbl] p)

init_wit_wd_po :: Machine -> M ()
init_wit_wd_po m =
    with 
        (do prefix_label $ _name m
            _context (assert_ctx m)
            named_hyps $ inits m)
        (emit_goal ["INIT/WWD"] 
            (well_definedness $ zall $ init_witness m))

init_witness_fis_po :: Machine -> M ()
init_witness_fis_po m =
    with 
        (do prefix_label $ _name m
            _context (assert_ctx m)
            named_hyps $ inits m)
        (emit_exist_goal ["INIT/WFIS"] 
            (M.elems $ abs_vars m  `M.difference` variables m) 
            (M.elems $ init_witness m))

init_fis_po :: Machine -> M ()
init_fis_po m = 
    with 
        (do prefix_label $ _name m
            _context (assert_ctx m))
        (emit_exist_goal [init_fis_lbl] 
            (M.elems $ variables m  `M.union` abs_vars m) 
            (M.elems $ inits m))

type M = POGen

expected_leadsto_po :: ProgressProp -> ProgressProp -> M ()
expected_leadsto_po (LeadsTo vs p0 q0) (LeadsTo vs' p1 q1) = do
        emit_goal ["lhs"] $ zforall (vs ++ vs') p0 p1
        emit_goal ["rhs"] $ zforall (vs ++ vs') q1 q0

assume_old_guard :: EventMerging -> POCtx ()
assume_old_guard evt = do
    case evt^.abstract_evts of
        e :| [] -> named_hyps $ e^._2.old.guards
        _ :| (_:_) -> return ()

prop_tr :: Machine -> (Label, Transient) -> M ()
prop_tr m (pname, Tr fv xp evt_lbl tr_hint) = do
            with (do
                prefix_label $ _name m
                prefix_label $ composite_label [tr_lbl, pname]
                ctx 
                named_hyps $ invariants m)
            $ do
                with (named_hyps $ singleton pname xp) $
                    forM_ (M.toList hint) $ \(v,(t,e)) -> do
                        emit_exist_goal ["WFIS",label v] [prime $ Var v t] [e]
                existential inds $ do
                    zipWithM_ stuff evt_lbl es
                    following
    where
        TrHint hint lt_fine = tr_hint
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
                param_ctx = POG.variables (evt^.new.params)
                enablement = emit_goal [evt_lbl, "EN"] 
                            (          xp 
                            `zimplies` (new_dummy ind $ zall sch0))

                new_defs = flip L.map (M.elems ind1) 
                        $ \(Var n t) -> (n ++ "@param", mk_fun [] (n ++ "@param") [] t)
                new_hyps = flip L.map (M.toList hint)
                        $ \(x,(_,e)) -> rename (x ++ "@prime") (x ++ "@param") e
                def_ctx = do
                    POG.functions (M.fromList new_defs)
                    POG.nameless_hyps new_hyps
                negation = with (do param_ctx
                                    assume_old_guard evt
                                    named_hyps $ M.map (new_dummy ind) sch
                                    named_hyps $ M.map (new_dummy ind) act
                                    named_hyps $ M.map (new_dummy ind) grd )
                      $ emit_goal [evt_lbl,"NEG"] $ xp `zimplies` (znot $ primed (variables m) xp) 
        all_ind = M.elems $ M.unions $ fv : L.zipWith local_ind evt_lbl es
        inds    = L.map (add_suffix "@param") $ M.elems 
                        $ M.unions (L.map (view indices) es) `M.difference` hint
        es      = L.map (upward_event m) evt_lbl
        
        local_ind :: Label -> EventMerging -> Map String Var
        local_ind lbl e = M.mapKeys (++ suff) $ M.map (add_suffix suff) $ e^.indices
            where
                suff = mk_suff $ "@" ++ show lbl
        new_ind :: Label -> EventMerging -> Expr -> Expr
        new_ind lbl e = make_unique suff (e^.indices)
            where
                suff = mk_suff $ "@" ++ show lbl
            -- (M.elems ind) 
        tagged_sched :: Label -> EventMerging -> Map Label Expr
        tagged_sched lbl e = M.map (new_ind lbl e) $ e^.new.coarse_sched
        all_csch  = concatMap M.elems $ L.zipWith tagged_sched evt_lbl es
            
            -- we take the disjunction of the fine schedules of 
            -- all the events involved in the transient predicate
        all_fsch  =
            zsome $ L.zipWith (\lbl e -> (new_ind lbl e . zall) $ e^.new.fine_sched) evt_lbl es
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
                            emit_goal [] $ zforall all_ind
                                    (zall $ xp : all_csch) 
                                    all_fsch
                        | otherwise -> return ()
        ctx = do
                _context $ assert_ctx m 
                _context $ step_ctx m 
                dummy
        dummy = POG.variables fv
        progs = _progress (props m) `M.union` _progress (inh_props m)
        mk_suff suff = LU.replace ":" "-" suff

prop_co :: Machine -> (Label, Constraint) -> M ()
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
                (emit_goal [evt_lbl,co_lbl,pname] $ forall_fv xp)
    where
        evts = M.toList (M.insert 
                ("SKIP") 
                skip_event 
                (conc_events m))
        forall_fv xp = if L.null fv then xp else zforall fv ztrue xp

prop_saf :: Machine -> (Label, SafetyProp) -> M ()
prop_saf m (pname, Unless fv p q excp) = 
    with
        (do prefix_label $ _name m
            _context $ step_ctx m
            POG.variables $ symbol_table fv
            named_hyps $ invariants m)
        $ forM_ evts $ \(evt_lbl,evt) -> do
            let grd  = evt^.new.guards
                act  = ba_predicate m evt
                ind = maybe M.empty (view indices . (conc_events m !)) excp
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
                (emit_goal [evt_lbl,"SAF",pname] $ 
                    zforall (elems diff ++ L.map suff (elems ind))
                        rng
                        $ new_dummy inter $
                            zimplies (p `zand` znot q) 
                                     (primed vars $ p `zor` q))
    where
        evts = M.toList $ all_upwards m
        vars = variables m
        suff = add_suffix "@param"

inv_po :: Machine -> (Label, Expr) -> M ()
inv_po m (pname, xp) = 
    do  with (do prefix_label $ _name m
                 _context $ step_ctx m
                 named_hyps $ invariants m)
            $ forM_ (M.toList $ all_upwards m) $ \(evt_lbl,evt) -> do
                let grd  = evt^.new.guards
                    act  = ba_predicate m evt
                with 
                    (do named_hyps $ grd
                        assume_old_guard evt
                        named_hyps $ act
                        named_hyps $ M.map ba_pred $ evt^.deleted_actions
                        POG.variables $ evt^.new.indices
                        POG.variables $ evt^.new.params)
                    (emit_goal [evt_lbl,inv_lbl,pname] 
                        (primed (variables m `M.union` abs_vars m) xp))
        with (do _context $ assert_ctx m
                 named_hyps $ inits m 
                 named_hyps $ M.mapKeys (label . name) (init_witness m))
            $ emit_goal [_name m, inv_init_lbl, pname] xp

wit_wd_po :: Machine -> (Label, EventMerging) -> M ()
wit_wd_po m (lbl, evt) = 
        with (do _context $ step_ctx m
                 POG.variables $ evt^.new.indices
                 POG.variables $ evt^.new.params
                 named_hyps $ invariants m
                 prefix_label $ _name m
                 prefix_label lbl
                 named_hyps $ evt^.new.guards
                 -- nameless_hyps $ _ $ evt^.abstract_evts
                 named_hyps $ ba_predicate' (variables m) (evt^.new.actions))
            (emit_goal ["WWD"] $ well_definedness $ zall 
                $ M.elems $ evt^.witness)

wit_fis_po :: Machine -> (Label, EventMerging) -> M ()
wit_fis_po m (lbl, evt) = 
        with (do _context $ step_ctx m
                 POG.variables $ evt^.new.indices
                 POG.variables $ evt^.new.params
                 named_hyps $ invariants m
                 prefix_label $ _name m
                 prefix_label lbl
                 named_hyps $ evt^.new.guards
                 -- nameless_hyps $ _ $ evt^.abstract_evts
                 named_hyps $ ba_predicate' (variables m) (evt^.new.actions))
            (emit_exist_goal ["WFIS"] pvar 
                $ M.elems $ evt^.witness)
    where
        pvar = L.map prime $ M.elems $ abs_vars m `M.difference` variables m


replace_csched_po :: Machine -> (Label,EventSplitting) -> M ()
replace_csched_po m (lbl,evt') = do 
        -- assert (L.null (L.drop 1 xs) 
        -- || L.null (evt^.c_sched_ref)) $ do
    case evt' of 
        EvtS ae (ce :| []) -> do
            let evt = EvtRef ae ce 
            with (do
                    prefix_label $ _name m
                    prefix_label lbl
                    prefix_label "C_SCH/delay"
                    _context $ assert_ctx m
                    _context $ step_ctx m
                    POG.variables $ evt^.new.indices
                    named_hyps $ invariants m ) $ do
            let old_c = evt^.old.coarse_sched
                old_f = evt^.old.fine_sched
            forM_ (L.zip [0..] $ evt^.c_sched_ref) $ \(i,ref) -> do
                let (plbl,prog) = sch_prog ref
                    (slbl,saf)  = sch_saf ref
                    keep_c      = (evt^.new.coarse_sched) `M.intersection` keep ref
                    new_part_c  = ((evt^.added.coarse_sched) `M.intersection` add ref) `M.union` keep_c
                    nb  = label $ show (i :: Int)
                    LeadsTo vs p0 q0  = prog
                    Unless us p1 q1 _ = saf
                with (do
                        POG.variables $ symbol_table vs
                        named_hyps old_c
                        named_hyps old_f) $ 
                    emit_goal [nb,"prog",plbl,"lhs"] p0
                with (do
                        POG.variables $ symbol_table vs) $
                    forM_ (M.toList new_part_c) $ \(lbl,sch) -> do
                        emit_goal [nb,"prog",plbl,"rhs",lbl] $ $fromJust$
                            Right q0 .=> Right sch
                with (do
                        POG.variables $ symbol_table us) $ do
                    emit_goal [nb,"saf",slbl,"lhs"] $ $fromJust$
                            Right p1 .== mzall (M.map Right new_part_c)
                    emit_goal [nb,"saf",slbl,"rhs"] $ $fromJust$
                            Right q1 .=> mznot (mzall $ M.map Right old_c)
                        -- the above used to include .=> ... \/ not old_f
                        -- it does not seem sound and I removed it
                        -- it broke one of the test cases
        _ -> assert (L.null (evt'^.c_sched_ref)) (return ())

weaken_csched_po :: Machine -> (Label,EventSplitting) -> M ()
weaken_csched_po m (lbl,evt) = do
    -- case evt' of 
    --     EvtS ae (ce :| []) -> do
            let -- evt = EvtRef ae ce 
                weaken_sch = do
                        e <- evt^.evt_pairs
                        return $ (e^.added.coarse_sched) `M.difference` M.unions (L.map add $ e^.c_sched_ref)
                -- weaken_sch  = case weaken_sch' of
                --                 m :| [] -> _
                --                 ms -> _
                -- weaken_sch = (evt^.added.coarse_sched) `M.difference` M.unions (L.map add $ evt^.c_sched_ref)

                old_c = evt^.old.coarse_sched
            with (do
                    prefix_label $ _name m
                    prefix_label lbl
                    prefix_label "C_SCH/weaken"
                    _context $ assert_ctx m
                    _context $ step_ctx m
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
                            emit_goal [lbl] sch
                    ms -> 
                        emit_goal [] $ zsome $ NE.map zall ms

replace_fsched_po :: Machine -> (Label,EventSplitting) -> M ()
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
                prefix_label lbl
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
                        named_hyps old_c
                        named_hyps old_f ) $
                    emit_goal ["prog",plbl,"lhs"] p0
                forM_ evts' $ \(clbl,evt) -> 
                    with (do
                            named_hyps $ evt^.new.coarse_sched
                            named_hyps $ evt^.new.fine_sched ) $
                        forM_ (M.toList $ evt^.deleted.fine_sched) $ \(lbl,sch) ->
                            emit_goal ["str",lbl,clbl] sch 
                case new_fs of
                  [new_f] -> do
                    with (do
                            POG.variables $ symbol_table vs) $ do
                        forM_ (M.toList new_f) $ \(lbl,sch) -> 
                            emit_goal ["prog",plbl,"rhs",lbl] $
                                    q0 `zimplies` sch
                  _ -> do
                    with (do
                            POG.variables $ symbol_table vs) $ do
                        emit_goal ["prog",plbl,"rhs"] $
                                q0 `zimplies` zsome (L.map zall new_fs)
              Nothing -> do
                let add_f  = L.map (zall . view (added.fine_sched)) evts
                    del_f  = L.map (zall . view (deleted.fine_sched)) evts
                    kept_f = intersections $ L.map (view $ kept.fine_sched) evts
                unless (new_fs == [old_f]) $
                    with (do
                            nameless_hyps new_c
                            named_hyps old_c -- is this sound?
                            named_hyps kept_f) $
                        emit_goal ["eqv"] $ $fromJust$
                            Right (zsome add_f) .= Right (zsome del_f)

intersections :: Ord k => [Map k a] -> Map k a
intersections []  = error "intersection of empty list is undefined"
intersections [x] = x
intersections (x:xs) = x `intersection` intersections xs                                

strengthen_guard_po :: Machine -> (Label,EventMerging) -> M ()
strengthen_guard_po m (lbl,evt) = 
        with (do
            prefix_label $ _name m
            prefix_label lbl
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
                emit_goal [lbl] grd
          es -> emit_goal [] $ zsome $ NE.map (zall . M.elems . view (deleted.guards)) es

sim_po :: Machine -> EventRef -> M ()
sim_po m evt = 
        with (do
                _context $ step_ctx m
                POG.variables $ evt^.new.indices
                POG.variables $ evt^.new.params 
                prefix_label $ _name m
                let lbl  = evt^.concrete._1
                    lbl' = evt^.abstract._1
                prefix_label lbl
                prefix_label lbl'
                prefix_label "SIM"
                named_hyps (evt^.new.guards)
                -- nameless_hyps $ _ $ evt^.abstract_evts
                named_hyps (ba_predicate m evt) ) $
            forM_ (M.toList $ evt^.deleted.actions) $ \(albl,act) ->
                emit_goal [albl] $ ba_pred act

fis_po :: Machine -> (Label, EventMerging) -> M ()
fis_po m (lbl, evt) = 
        with (do _context $ assert_ctx m
                 POG.variables $ evt^.indices
                 POG.variables $ evt^.params 
                 named_hyps $ invariants m
                 -- nameless_hyps $ _ $ evt^.abstract_evts
                 named_hyps $ evt^.new.guards)
            (emit_exist_goal [_name m, lbl, fis_lbl] pvar 
                $ M.elems $ ba_predicate m evt)
    where
        pvar = L.map prime $ M.elems $ variables m `M.union` abs_vars m

tr_wd_po :: Machine -> (Label, Transient) -> M ()
tr_wd_po  m (lbl, Tr vs p _ (TrHint wit _)) = 
        with (do prefix_label $ _name m
                 prefix_label lbl
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
                    emit_goal ["WD","witness",label n] $ 
                        well_definedness e

prog_wd_po :: Machine -> (Label, ProgressProp) -> M ()
prog_wd_po m (lbl, LeadsTo vs p q) = 
        with (do prefix_label $ _name m
                 prefix_label lbl
                 prefix_label "PROG"
                 _context $ step_ctx m
                 named_hyps $ invariants m) $
            do  emit_goal ["WD","lhs"]
                    $ well_definedness $ zforall vs ztrue p
                emit_goal ["WD","rhs"]
                    $ well_definedness $ zforall vs ztrue q

saf_wd_po :: Machine -> (Label, SafetyProp) -> M ()
saf_wd_po m (lbl, Unless vs p q _) = 
        with (do prefix_label $ _name m
                 prefix_label lbl
                 prefix_label "SAF"
                 _context $ step_ctx m
                 named_hyps $ invariants m) $
            do  emit_goal ["WD","lhs"]
                    $ zforall vs ztrue $ (znot q) `zimplies` (well_definedness p)
                emit_goal ["WD","rhs"]
                    $ well_definedness $ zforall vs ztrue q

co_wd_po :: Machine -> (Label, Constraint) -> M ()
co_wd_po m (lbl, Co vs p) = 
        with (do prefix_label $ _name m
                 prefix_label lbl
                 prefix_label "CO"
                 _context $ step_ctx m
                 nameless_hyps $ M.elems $
                    M.map (primed $ variables m) $ invariants m
                 named_hyps $ invariants m)
             $ emit_goal ["WD"]
                $ well_definedness $ zforall vs ztrue p

inv_wd_po :: Machine -> M ()
inv_wd_po m = 
        with (do prefix_label $ _name m
                 _context $ assert_ctx m
                 named_hyps $ _inv $ inh_props m
                 named_hyps $ _inv_thm $ inh_props m)
            $ emit_goal ["INV", "WD"] 
                $ well_definedness $ zall $ _inv $ props m

init_wd_po :: Machine -> M ()
init_wd_po m = 
        with (do prefix_label $ _name m
                 _context $ assert_ctx m
                 named_hyps $ _inv $ inh_props m
                 named_hyps $ _inv_thm $ inh_props m)
            $ emit_goal ["INIT", "WD"] 
                $ well_definedness $ zall $ inits m

incremental_wd_po :: Label
                  -> Map Label Expr  -- 
                  -> Map Label Expr  -- 
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

evt_wd_po :: Machine -> (Label, EventMerging) -> M ()
evt_wd_po m (lbl, evts) = 
        with (do prefix_label $ _name m
                 prefix_label lbl
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
                        emit_goal [tag] 
                            $ well_definedness $ ba_pred bap

evt_eql_po :: Machine -> (Label, EventMerging) -> M ()
evt_eql_po  m (_lbl, evts) = 
    with (do prefix_label $ _name m
             _context $ step_ctx m
             named_hyps $ invariants m ) $
    void $ T.forM (evts^.evt_pairs) $ \evt -> 
        with (do named_hyps $ evt^.total.guards
                 named_hyps $ ba_predicate m evt
                 prefix_label $ evt^.concrete._1
                 prefix_label $ evt^.abstract._1
                 prefix_label "EQL"
                 _context $ evt_live_ctx evt
                 _context $ evt_saf_ctx evt)
            (forM_ (M.elems $ evt^.eql_vars) $ \v -> do
                emit_goal [label $ name v] 
                    $ Word (prime v) `zeq` Word v )

sch_po :: Machine -> (Label, EventMerging) -> M ()
sch_po m (lbl, evts) = 
    forM_ (evts^.evt_pairs.to NE.toList) $ \evt ->
        with (do prefix_label $ _name m
                 prefix_label lbl
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
                            emit_goal [lbl] grd  
                    forM_ (M.toList $ evt^.added.guards) 
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

thm_wd_po :: Machine -> M ()
thm_wd_po m = 
        with (do prefix_label $ _name m
                 _context $ assert_ctx m
                 named_hyps $ _inv $ inh_props m
                 named_hyps $ _inv_thm $ inh_props m
                 named_hyps $ _inv $ props m) $ do
            let wd = well_definedness $ zall $ _inv_thm $ props m
            unless (wd == ztrue) $ 
                emit_goal ["THM", "WD"] wd 


thm_po :: Machine -> (Label, Expr) -> M ()
thm_po m (lbl, xp) = 
    with (do
            prefix_label $ _name m
            prefix_label thm_lbl
            prefix_label lbl
            _context $ assert_ctx m
            named_hyps inv)
        $ emit_goal [] xp
    where
        inv = invariants_only m

add_suffix :: String -> Var -> Var
add_suffix suf (Var n t) = Var (n ++ suf) t

new_dummy :: Map String Var -> Expr -> Expr
new_dummy = make_unique "@param"

verify_machine :: Machine -> IO (Int, Int)
verify_machine m = do
    (s,i,j) <- str_verify_machine m
    putStrLn s
    return (i,j)

check :: Calculation -> IO (Either [Error] [(Validity, Int)])
check c = runEitherT $ do
        pos <- hoistEither $ obligations' empty_ctx empty_sequent c
        rs  <- lift $ forM pos $ uncurry discharge
        let ln = L.filter ((/= Valid) . fst) $ L.zip rs [0..]
        return ln

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
                 
str_verify_machine :: Machine -> IO (String,Int,Int)
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
