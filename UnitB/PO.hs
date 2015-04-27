{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
    -- Behavior hiding
module UnitB.PO 
    ( proof_obligation, theory_po
    , step_ctx, evt_live_ctx
    , theory_ctx, theory_facts, dummy_ctx
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
import Logic.Theory
import Logic.WellDefinedness

import           UnitB.AST
import           UnitB.POGenerator hiding ( variables )
import qualified UnitB.POGenerator as POG

import Z3.Z3

    -- Libraries
import Control.Monad hiding (guard)
import Control.Monad.Trans
import Control.Monad.Trans.Either

import           Data.Map as M hiding 
                    ( map, foldl, foldr
                    , delete, filter, null
                    , (\\), mapMaybe )
import qualified Data.Map as M
import           Data.List as L hiding (inits, union,insert)
import           Data.List.Utils as LU (replace)

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

evt_saf_ctx :: Event -> Context
evt_saf_ctx evt  = Context M.empty (params evt) M.empty M.empty M.empty

evt_live_ctx :: Event -> Context
evt_live_ctx evt = Context M.empty (indices evt) M.empty M.empty M.empty

dummy_ctx :: Machine -> Context
dummy_ctx m = Context M.empty (dummies $ theory m) M.empty M.empty M.empty


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
                        context $ theory_ctx (theory m)
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
                    forM_  (M.toList $ events m) $ \ev -> do
                        replace_csched_po m ev
                        replace_fsched_po m ev
                        weaken_csched_po m ev
                        strengthen_guard_po m ev
                        sim_po m ev
                        wit_wd_po m ev
                        wit_fis_po m ev
                        fis_po m ev
                        evt_wd_po m ev
                        evt_eql_po m ev
                        sch_po m ev
                    mapM_ (prog_wd_po m) $ M.toList $ _progress p
                    mapM_ (ref_po m) $ M.toList $ derivation m
    where            
        p = props m
        unnamed = theory_facts (theory m) `M.difference` named_f
        named_f = theory_facts (theory m) { extends = M.empty }

proof_obligation :: Machine -> Either [Error] (Map Label Sequent)
proof_obligation m = do
        let { pos = raw_machine_pos m }
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
        xs <- mapM (uncurry f) $ toList $ M.mapWithKey g thm
        return $ fromList $ concat xs
    where
--        axm = M.filterKeys (not . (`S.member` theorems th)) $ fact th
        dep       = M.map M.fromList $ M.fromListWith (++) 
                        [ (x,[(y,())]) | (x,y) <- thm_depend th ]
        depend x  = thm `M.intersection` findWithDefault M.empty x dep
        (thm,axm) = M.partitionWithKey p $ fact th
        p k _     = k `M.member` theorems th

        g lbl x   = Sequent empty_ctx [] (depend lbl `M.union` axm) x
        keys k    = composite_label ["THM",k]
        f lbl (Sequent a b c d) = result
          where
            result = case keys lbl `M.lookup` theorems th of
                        Just (Just proof) -> do
                            xs <- proof_po proof (keys lbl) po
                            return xs
                        _ -> return [(keys lbl, po)]
            po = Sequent 
                (a `merge_ctx` theory_ctx th)
                (concatMap 
                    (M.elems . theory_facts) 
                    (elems $ extends th) ++ b) 
                c d

init_sim_po :: Machine -> M ()
init_sim_po m = 
    with 
        (do prefix_label $ _name m
            prefix_label "INIT"
            prefix_label "SIM"
            context (assert_ctx m)
            named_hyps $ inits m
            named_hyps $ M.mapKeys (label . name) $ init_witness m)
        (forM_ (M.toList $ del_inits m) $ \(lbl,p) -> do
            emit_goal [lbl] p)

init_wit_wd_po :: Machine -> M ()
init_wit_wd_po m =
    with 
        (do prefix_label $ _name m
            context (assert_ctx m)
            named_hyps $ inits m)
        (emit_goal ["INIT/WWD"] 
            (well_definedness $ zall $ init_witness m))

init_witness_fis_po :: Machine -> M ()
init_witness_fis_po m =
    with 
        (do prefix_label $ _name m
            context (assert_ctx m)
            named_hyps $ inits m)
        (emit_exist_goal ["INIT/WFIS"] 
            (M.elems $ abs_vars m  `M.difference` variables m) 
            (M.elems $ init_witness m))

init_fis_po :: Machine -> M ()
init_fis_po m = 
    with 
        (do prefix_label $ _name m
            context (assert_ctx m))
        (emit_exist_goal [init_fis_lbl] 
            (M.elems $ variables m  `M.union` abs_vars m) 
            (M.elems $ inits m))

type M = POGen

expected_leadsto_po :: ProgressProp -> ProgressProp -> M ()
expected_leadsto_po (LeadsTo vs p0 q0) (LeadsTo vs' p1 q1) = do
        emit_goal ["lhs"] $ zforall (vs ++ vs') p0 p1
        emit_goal ["rhs"] $ zforall (vs ++ vs') q1 q0

prop_tr :: Machine -> (Label, Transient) -> M ()
prop_tr m (pname, Transient fv xp evt_lbl tr_hint) = do
            with (do
                prefix_label $ _name m
                prefix_label $ composite_label [tr_lbl, pname]
                ctx 
                named_hyps $ invariants m)
            $ do
                with (named_hyps $ singleton pname xp) $
                    forM_ (toList hint) $ \(v,(t,e)) -> do
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
                grd  = all_guards evt
                sch0 = coarse $ new_sched evt
                sch1 = fine $ new_sched evt
                sch  = sch0 `M.union` sch1
                act  = ba_predicate m evt
                ind  = indices evt
                ind1 = indices evt `M.intersection` hint
                param_ctx = POG.variables (params evt)
                enablement = emit_goal [evt_lbl, "EN"] 
                            (          xp 
                            `zimplies` (new_dummy ind $ zall sch0))

                new_defs = flip map (M.elems ind1) 
                        $ \(Var n t) -> (n ++ "@param", mk_fun [] (n ++ "@param") [] t)
                new_hyps = flip map (M.toList hint)
                        $ \(x,(_,e)) -> rename (x ++ "@prime") (x ++ "@param") e
                def_ctx = do
                    POG.functions (M.fromList new_defs)
                    POG.nameless_hyps new_hyps
                negation = with (do param_ctx
                                    named_hyps 
                                        $ M.map 
                                            (new_dummy ind) 
                                            (M.unions [sch,grd,act]))
                      $ emit_goal [evt_lbl,"NEG"] $ xp `zimplies` (znot $ primed (variables m) xp) 
        all_ind = M.elems $ M.unions $ fv : zipWith local_ind evt_lbl es
        inds    = map (add_suffix "@param") $ M.elems 
                        $ M.unions (map indices es) `M.difference` hint
        es      = map (events m !) evt_lbl
        
        local_ind :: Label -> Event -> Map String Var
        local_ind lbl e = M.mapKeys (++ suff) $ M.map (add_suffix suff) $ indices e
            where
                suff = mk_suff $ "@" ++ show lbl
        new_ind :: Label -> Event -> Expr -> Expr
        new_ind lbl e = make_unique suff (indices e)
            where
                suff = mk_suff $ "@" ++ show lbl
            -- (M.elems ind) 
        tagged_sched :: Label -> Event -> Map Label Expr
        tagged_sched lbl e = M.map (new_ind lbl e) $ coarse $ new_sched e
        all_csch  = concatMap M.elems $ zipWith tagged_sched evt_lbl es
            
            -- we take the disjunction of the fine schedules of 
            -- all the events involved in the transient predicate
        all_fsch  =
            zsome $ zipWith (\lbl e -> (new_ind lbl e . zall) $ fine (new_sched e)) evt_lbl es
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
                            ) pname (intercalate "," $ map show evt_lbl)
                    Nothing
                        | not $ all_fsch == ztrue ->
                            emit_goal [] $ zforall all_ind
                                    (zall $ xp : all_csch) 
                                    all_fsch
                        | otherwise -> return ()
        ctx = do
                POG.context $ assert_ctx m 
                POG.context $ step_ctx m 
                dummy
        dummy = POG.variables fv
        progs = _progress (props m) `M.union` _progress (inh_props m)
        mk_suff suff = LU.replace ":" "-" suff

prop_co :: Machine -> (Label, Constraint) -> M ()
prop_co m (pname, Co fv xp) = 
    with
        (do prefix_label $ _name m
            context $ step_ctx m
            context $ dummy_ctx m
            named_hyps $ invariants m)
        $ forM_ evts $ \(evt_lbl,evt) -> do
            let grd  = all_guards evt
                act  = ba_predicate m evt
            with 
                (do named_hyps $ grd
                    named_hyps $ act
                    POG.variables $ indices evt
                    POG.variables $ params evt)
                (emit_goal [evt_lbl,co_lbl,pname] $ forall_fv xp)
    where
        evts = toList (M.insert 
                ("SKIP") 
                empty_event 
                (events $ m))
        forall_fv xp = if L.null fv then xp else zforall fv ztrue xp

prop_saf :: Machine -> (Label, SafetyProp) -> M ()
prop_saf m (pname, Unless fv p q excp) = 
    with
        (do prefix_label $ _name m
            context $ step_ctx m
            context $ dummy_ctx m
            named_hyps $ invariants m)
        $ forM_ evts $ \(evt_lbl,evt) -> do
            let grd  = all_guards evt
                act  = ba_predicate m evt
                ind = maybe M.empty (indices . (events m !)) excp
                fvs = symbol_table fv 
                neq x = znot $ Word x `zeq` Word (suff x)
                rng = maybe ztrue 
                        (const $ zsome $ map neq $ elems inter)
                        excp
                inter = fvs `M.intersection` ind
                diff  = fvs `M.difference` ind
            with 
                (do named_hyps $ grd
                    named_hyps $ act
                    POG.variables $ indices evt
                    POG.variables $ params evt)
                (emit_goal [evt_lbl,"SAF",pname] $ 
                    zforall (elems diff ++ map suff (elems ind))
                        rng
                        $ new_dummy inter $
                            zimplies (p `zand` znot q) 
                                     (primed vars $ p `zor` q))
    where
        evts = toList $ events $ m
        vars = variables m
        suff = add_suffix "@param"

inv_po :: Machine -> (Label, Expr) -> M ()
inv_po m (pname, xp) = 
    do  with (do prefix_label $ _name m
                 context $ step_ctx m
                 named_hyps $ invariants m)
            $ forM_ (toList $ events m) $ \(evt_lbl,evt) -> do
                let grd  = all_guards evt
                    act  = ba_predicate m evt
                with 
                    (do named_hyps $ grd
                        named_hyps $ act
                        named_hyps $ M.map ba_pred $ del_acts evt
                        POG.variables $ indices evt
                        POG.variables $ params evt)
                    (emit_goal [evt_lbl,inv_lbl,pname] 
                        (primed (variables m `M.union` abs_vars m) xp))
        with (do context $ assert_ctx m
                 named_hyps $ inits m 
                    `M.union` M.mapKeys (label . name) (init_witness m))
            $ emit_goal [_name m, inv_init_lbl, pname] xp

wit_wd_po :: Machine -> (Label, Event) -> M ()
wit_wd_po m (lbl, evt) = 
        with (do context $ step_ctx m
                 POG.variables $ indices evt
                 POG.variables $ params evt
                 named_hyps $ invariants m
                 prefix_label $ _name m
                 prefix_label lbl
                 named_hyps $ all_guards evt
                 named_hyps $ ba_predicate' (variables m) (actions evt))
            (emit_goal ["WWD"] $ well_definedness $ zall 
                $ M.elems $ witness evt)

wit_fis_po :: Machine -> (Label, Event) -> M ()
wit_fis_po m (lbl, evt) = 
        with (do context $ step_ctx m
                 POG.variables $ indices evt
                 POG.variables $ params evt
                 named_hyps $ invariants m
                 prefix_label $ _name m
                 prefix_label lbl
                 named_hyps $ all_guards evt
                 named_hyps $ ba_predicate' (variables m) (actions evt))
            (emit_exist_goal ["WFIS"] pvar 
                $ M.elems $ witness evt)
    where
        pvar = map prime $ M.elems $ abs_vars m `M.difference` variables m


replace_csched_po :: Machine -> (Label,Event) -> M ()
replace_csched_po m (lbl,evt) = do
        with (do
                prefix_label $ _name m
                prefix_label lbl
                prefix_label "C_SCH/delay"
                POG.context $ assert_ctx m
                POG.context $ step_ctx m
                POG.variables $ indices evt
                named_hyps $ invariants m ) $ do
        let old_c = coarse $ old_sched evt
            old_f = fine $ old_sched evt
        forM_ (zip [0..] $ c_sched_ref evt) $ \(i,ref) -> do
            let (plbl,prog) = sch_prog ref
                (slbl,saf)  = sch_saf ref
                keep_c     = coarse (new_sched evt) `M.intersection` keep ref
                new_part_c = (coarse (added_sched evt) `M.intersection` add ref) `M.union` keep_c
                nb = label $ show (i :: Int)
                LeadsTo vs p0 q0  = prog
                Unless us p1 q1 _ = saf
            with (do
                    POG.variables $ symbol_table vs
                    named_hyps old_c
                    named_hyps old_f) $ 
                emit_goal [nb,"prog",plbl,"lhs"] p0
            with (do
                    POG.variables $ symbol_table vs) $
                forM_ (toList new_part_c) $ \(lbl,sch) -> do
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

weaken_csched_po :: Machine -> (Label,Event) -> M ()
weaken_csched_po m (lbl,evt) = do
        let weaken_sch = coarse (added_sched evt) `M.difference` M.unions (L.map add $ c_sched_ref evt)
            old_c = coarse $ old_sched evt
        with (do
                prefix_label $ _name m
                prefix_label lbl
                prefix_label "C_SCH/weaken"
                POG.context $ assert_ctx m
                POG.context $ step_ctx m
                POG.variables $ indices evt
                named_hyps $ invariants m 
                    -- old version admits old_f as assumption
                    -- why is it correct or needed?
                    -- named_hyps old_f
                named_hyps old_c) $ do
        forM_ (M.toList weaken_sch) $ \(lbl,sch) -> do
            emit_goal [lbl] sch

replace_fsched_po :: Machine -> (Label,Event) -> M ()
replace_fsched_po m (lbl,evt) = do
        let old_c = coarse $ old_sched evt
            new_c = coarse $ new_sched evt
            old_f = fine $ old_sched evt
            new_f = fine $ new_sched evt
        with (do
                prefix_label $ _name m
                prefix_label lbl
                prefix_label "F_SCH/replace"
                POG.context $ assert_ctx m
                POG.context $ step_ctx m
                POG.variables $ indices evt
                named_hyps $ invariants m) $ do
            case f_sched_ref evt of
                Just (plbl,prog) -> do
                    let LeadsTo vs p0 q0 = prog
                    with (do
                            POG.variables $ symbol_table vs) $ do
                        with (do
                                named_hyps old_c
                                named_hyps old_f ) $
                            emit_goal ["prog",plbl,"lhs"] p0
                        forM_ (M.toList new_f) $ \(lbl,sch) -> 
                            emit_goal ["prog",plbl,"rhs",lbl] $
                                    q0 `zimplies` sch
                    with (do
                            named_hyps new_c
                            named_hyps new_f ) $
                        forM_ (M.toList $ fine $ deleted_sched evt) $ \(lbl,sch) ->
                            emit_goal ["str",lbl] sch 
                Nothing -> do
                    let add_f = fine $ added_sched evt
                        del_f = fine $ deleted_sched evt
                        kept_f = fine $ kept_sched evt
                    unless (new_f == old_f) $
                        with (do
                                named_hyps new_c
                                named_hyps old_c -- is this sound?
                                named_hyps kept_f) $
                            emit_goal ["eqv"] $ $fromJust$
                                Right (zall add_f) .= Right (zall del_f)
                                
strengthen_guard_po :: Machine -> (Label,Event) -> M ()
strengthen_guard_po m (lbl,evt) = 
        with (do
                prefix_label $ _name m
                prefix_label lbl
                prefix_label "GRD/str"
                POG.context $ assert_ctx m
                POG.context $ step_ctx m
                POG.variables $ indices evt
                POG.variables $ params evt
                named_hyps $ invariants m 
                named_hyps $ new_guard evt ) $ do
        forM_ (toList $ deleted_guard evt) $ \(lbl,grd) -> do
            emit_goal [lbl] grd

sim_po :: Machine -> (Label, Event) -> M ()
sim_po m (lbl, evt) = 
        with (do
                context $ step_ctx m
                POG.variables $ indices evt
                POG.variables $ params evt
                prefix_label $ _name m
                prefix_label lbl
                prefix_label "SIM"
                named_hyps (all_guards evt)
                named_hyps (ba_predicate m evt) ) $
            forM_ (M.toList $ del_acts evt) $ \(albl,act) ->
                emit_goal [albl] $ ba_pred act

fis_po :: Machine -> (Label, Event) -> M ()
fis_po m (lbl, evt) = 
        with (do context $ assert_ctx m
                 POG.variables $ indices evt
                 POG.variables $ params evt
                 named_hyps $ invariants m
                 named_hyps $ all_guards evt)
            (emit_exist_goal [_name m, lbl, fis_lbl] pvar 
                $ M.elems $ ba_predicate m evt)
    where
        pvar = map prime $ M.elems $ variables m `M.union` abs_vars m

tr_wd_po :: Machine -> (Label, Transient) -> M ()
tr_wd_po  m (lbl, Transient vs p _ (TrHint wit _)) = 
        with (do prefix_label $ _name m
                 prefix_label lbl
                 prefix_label "TR"
                 context $ step_ctx m
                 named_hyps $ invariants m) $
            do  emit_goal ["WD"]
                    $ well_definedness $ zforall (elems vs) ztrue p
                forM_ (toList wit) $ \(n,(t,e)) -> 
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
                 context $ step_ctx m
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
                 context $ step_ctx m
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
                 context $ step_ctx m
                 nameless_hyps $ M.elems $
                    M.map (primed $ variables m) $ invariants m
                 named_hyps $ invariants m)
             $ emit_goal ["WD"]
                $ well_definedness $ zforall vs ztrue p

inv_wd_po :: Machine -> M ()
inv_wd_po m = 
        with (do prefix_label $ _name m
                 context $ assert_ctx m
                 named_hyps $ _inv $ inh_props m
                 named_hyps $ _inv_thm $ inh_props m)
            $ emit_goal ["INV", "WD"] 
                $ well_definedness $ zall $ invariants_only m

init_wd_po :: Machine -> M ()
init_wd_po m = 
        with (do prefix_label $ _name m
                 context $ assert_ctx m
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

evt_wd_po :: Machine -> (Label, Event) -> M ()
evt_wd_po m (lbl, evt) = 
        with (do prefix_label $ _name m
                 prefix_label lbl
                 prefix_label "WD"
                 context $ assert_ctx m
                 POG.variables $ indices evt
                 named_hyps $ invariants m) $ do
            incremental_wd_po "C_SCH"
                (coarse $ old_sched evt)
                (coarse $ new_sched evt)
            with (named_hyps $ coarse $ new_sched evt) $
                incremental_wd_po "F_SCH"
                    (fine $ old_sched evt)
                    (fine $ new_sched evt)
            with (POG.variables $ params evt) $ do
                incremental_wd_po "GRD" 
                    (old_guard evt) (new_guard evt)
                with (do prefix_label "ACT"
                         named_hyps $ all_guards evt
                         context $ step_ctx m) $ do
                    let p k _ = k `M.notMember` old_acts evt
                    forM_ (toList $ M.filterWithKey p $ actions evt) $ \(tag,bap) -> 
                        emit_goal [tag] 
                            $ well_definedness $ ba_pred bap

evt_eql_po :: Machine -> (Label, Event) -> M ()
evt_eql_po  m (lbl, evt) = 
    with (do prefix_label $ _name m
             prefix_label lbl
             prefix_label "EQL"
             context $ evt_live_ctx evt
             context $ evt_saf_ctx evt
             context $ step_ctx m
             named_hyps $ invariants m
             named_hyps $ all_guards evt
             named_hyps $ ba_predicate m evt)
        (forM_ (M.elems $ eql_vars evt) $ \v -> do
            emit_goal [label $ name v] 
                $ Word (prime v) `zeq` Word v )

sch_po :: Machine -> (Label, Event) -> M ()
sch_po m (lbl, evt) = 
    with (do prefix_label $ _name m
             prefix_label lbl
             prefix_label sch_lbl
             context $ assert_ctx m
             context $ evt_live_ctx evt
             POG.variables ind
             named_hyps hyp)
         $ if M.null param
                then if removed_c_sch || removed_f_sch 
                    then forM_ (toList grd) $ \(lbl,grd) -> 
                        emit_goal [lbl] grd  
                    else forM_ (toList $ grd `M.difference` old_guard evt) 
                        $ \(lbl,grd) -> emit_goal [lbl] grd  
            else if removed_c_sch || removed_f_sch || added_grd
                then emit_exist_goal [] (M.elems param) (M.elems grd)
                else return ()
    where
        grd   = new_guard evt
        c_sch = coarse $ new_sched evt
        f_sch = fine $ new_sched evt
        removed_sched sch = not $ M.null $ sch (old_sched evt) `M.difference` sch (new_sched evt)
        removed_c_sch = removed_sched coarse
        removed_f_sch = removed_sched fine
        added_grd = not $ M.null $ new_guard evt `M.difference` old_guard evt
        param = params evt
        ind   = indices evt `merge` params evt
        hyp   = invariants m `M.union` f_sch `M.union` c_sch

thm_wd_po :: Machine -> M ()
thm_wd_po m = 
        with (do prefix_label $ _name m
                 context $ assert_ctx m
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
            context $ assert_ctx m
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
        let ln = filter ((/= Valid) . fst) $ zip rs [0..]
        return ln

dump :: String -> Map Label Sequent -> IO ()
dump name pos = do
        withFile (name ++ ".z") WriteMode (\h -> do
            forM_ (M.toList pos) (\(lbl, po) -> do
                hPutStrLn h (format "(echo \"> {0}\")\n(push)" lbl)
                hPutStrLn h (unlines $ map f $ z3_code po)
                hPutStrLn h "(pop)"
                hPutStrLn h ("; end of " ++ show lbl)
                ) )
    where
        f x = pretty_print' x

verify_all :: Map Label Sequent -> IO (Map Label Bool)
verify_all pos' = do
    let xs         = M.toList pos'
        lbls       = map fst xs 
    ys <- map_failures (lbls !!) 
            $ discharge_all xs
    rs <- forM (zip lbls ys) $ \(lbl,r) -> do
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
                return (old_pos,unlines $ map report msgs,0)
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
            Left msgs -> return (unlines $ map report msgs,0,0)

smoke_test_machine :: Machine -> IO (String)
smoke_test_machine m =
        case proof_obligation m of 
            Right pos -> do
                rs <- flip filterM (M.toList pos) $ \(lbl,po) -> do
                    r <- smoke_test lbl po
                    return $ r == Valid
                return $ unlines $ map (show . fst) rs
            Left msgs -> return (unlines $ map report msgs)

format_result :: Map Label Bool -> IO (String,Int,Int)
format_result xs' = do
        let rs    = map f $ M.toList xs'
            total = length rs
            passed = length $ filter fst rs
            xs = "passed " ++ (show passed) ++ " / " ++ show total
            ys = map snd rs ++ [xs]
        return (unlines ys, passed, total)
    where
        f (y,True)  = (True, "  o  " ++ show y)
        f (y,False) = (False," xxx " ++ show y)
