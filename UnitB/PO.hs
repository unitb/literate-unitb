{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE OverloadedStrings #-}
module UnitB.PO 
    ( proof_obligation, theory_po
    , step_ctx, evt_live_ctx
    , theory_ctx, theory_facts, dummy_ctx
    , evt_saf_ctx, invariants, assert_ctx
    , str_verify_machine, raw_machine_pos
    , verify_all, prop_saf, prop_tr
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
import Control.Monad.Trans.Class
import Control.Monad.Trans.Either

import           Data.Map as M hiding 
                    ( map, foldl, foldr
                    , delete, filter, null
                    , (\\), mapMaybe )
import qualified Data.Map as M
import qualified Data.Set as S
import           Data.Maybe as MM 
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
          (Context M.empty (variables m) M.empty M.empty M.empty)
step_ctx :: Machine -> Context
step_ctx m = merge_all_ctx 
        [  Context M.empty (prime_all $ variables m) M.empty M.empty M.empty
        ,  Context M.empty (variables m) M.empty M.empty M.empty ]
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
                   (inv p0) 
        `M.union` (inv_thm p0) 
        `M.union` (inv p1)
        `M.union` (inv_thm p1)
    where
        p0 = props m
        p1 = inh_props m

invariants_only :: Machine -> Map Label Expr
invariants_only m = 
                   (inv p0) 
        `M.union` (inv p1)
    where
        p0 = props m
        p1 = inh_props m 

raw_machine_pos :: Machine -> (Map Label Sequent)
raw_machine_pos m = pos
    where
        pos = M.map f $ 
               (eval_generator $ do
                    forM_ (M.toList $ transient p) $ \tr -> do
                        prop_tr m tr
                        tr_wd_po m tr
                    forM_ (M.toList $ safety p) $ \saf -> do
                        prop_saf m saf
                        saf_wd_po m saf
                    forM_ (M.toList $ constraint p) $ \co -> do
                        prop_co m co 
                        co_wd_po m co
                    init_fis_po m
                    inv_wd_po m
                    init_wd_po m
                    mapM_ (inv_po m) $ M.toList $ inv p
                    mapM_ (thm_po m) $ M.toList $ inv_thm p
                    forM_  (M.toList $ events m) $ \ev -> do
                        fis_po m ev
                        evt_wd_po m ev
                        evt_eql_po m ev
                        sch_po m ev
                    mapM_ (prog_wd_po m) $ M.toList $ progress p
                    mapM_ (ref_po m) $ M.toList $ derivation m
                    )
        p = props m
        f (Sequent a b c d) = Sequent 
                (a `merge_ctx` theory_ctx (theory m))
                (M.elems unnamed ++ b) 
                (named_f `M.union` c)
                d
          where
            unnamed = theory_facts (theory m) `M.difference` named_f
            named_f = theory_facts (theory m) { extends = M.empty }

proof_obligation :: Machine -> Either [Error] (Map Label Sequent)
proof_obligation m = do
        let { pos = raw_machine_pos m }
        forM_ (M.toList $ proofs $ props $ m) (\(lbl,p) -> do
            let li = line_info p
            if lbl `M.member` pos
                then return ()
                else Left [Error 
                    (format "a proof is provided for non-existant proof obligation {0}" lbl)
                        li])
        xs <- forM (M.toList pos) (\(lbl,po) -> do
            case M.lookup lbl $ proofs $ props $ m of
                Just c ->
                    proof_po c lbl po
                Nothing -> 
                    return [(lbl,po)])
        return $ M.fromList $ concat xs

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

init_fis_po :: Machine -> M ()
init_fis_po m = 
    with 
        (do prefix_label $ _name m
            context (assert_ctx m))
        (emit_exist_goal [init_fis_lbl] 
            (M.elems $ variables m) 
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
            $ existential inds $ do
                zipWithM_ stuff evt_lbl es
                following
                -- emit_goal [] $ exist_ind (zall $ [enablement,fa_negation] ++ map snd following)
    where
        TrHint hint lt_fine = tr_hint
        stuff evt_lbl evt = 
            with def_ctx $ do
                    enablement
                    negation
            where
                grd  = new_guard evt
                sch0 = coarse $ new_sched evt
                sch1 = fromList $ maybeToList $ fine $ new_sched evt
                sch  = sch0 `M.union` sch1
                act  = ba_predicate m evt
                ind  = indices evt
                ind1 = indices evt `M.intersection` hint
                param_ctx = POG.variables (params evt)
                enablement = emit_goal [evt_lbl, "EN"] 
                            (          xp 
                            `zimplies` (new_dummy ind $ zall (M.elems sch0)))

                new_defs = flip map (M.toList ind1) 
                        $ \(x,Var n t) -> (n ++ "@param", Def [] (n ++ "@param") [] t $ hint ! x)
                def_ctx = definitions (M.fromList new_defs)
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
        all_fsch  = do
            fs <- zipWithM (\lbl e -> (new_ind lbl e . snd) `liftM` fine (new_sched e)) evt_lbl es
            return $ zsome fs :: Maybe Expr
            -- fine $ new_sched evt
        following = with (prefix_label "leadsto") $
                case (lt_fine, all_fsch) of
                    (Just lbl, Just fsch) ->
                        expected_leadsto_po 
                            (LeadsTo all_ind
                                    (zall $ xp : all_csch) 
                                    fsch) 
                            (progs ! lbl)
                    (Nothing,Just fsch) ->
                        emit_goal [] $ zforall all_ind
                                (zall $ xp : all_csch) 
                                fsch
                    (Nothing,Nothing) -> return ()
                    _                 -> error $ format (
                               "transient predicate {0}'s side condition doesn't "
                            ++ "match the fine schedule of event {1}"
                            ) pname (intercalate "," $ map show evt_lbl)
        ctx = do
                POG.context $ assert_ctx m 
                POG.context $ step_ctx m 
                dummy
        dummy = POG.variables fv
        progs = progress (props m) `M.union` progress (inh_props m)
        mk_suff suff = LU.replace ":" "-" suff

prop_co :: Machine -> (Label, Constraint) -> M ()
prop_co m (pname, Co fv xp) = 
    with
        (do prefix_label $ _name m
            context $ step_ctx m
            context $ dummy_ctx m
            named_hyps $ invariants m)
        $ forM_ evts $ \(evt_lbl,evt) -> do
            let grd  = new_guard evt
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
            let grd  = new_guard evt
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
                let grd  = new_guard evt
                    act  = ba_predicate m evt
                with 
                    (do named_hyps $ grd
                        named_hyps $ act
                        POG.variables $ indices evt
                        POG.variables $ params evt)
                    (emit_goal [evt_lbl,inv_lbl,pname] 
                        (primed (variables m) xp))
        with (do context $ assert_ctx m
                 named_hyps $ inits m)
            $ emit_goal [_name m, inv_init_lbl, pname] xp

fis_po :: Machine -> (Label, Event) -> M ()
fis_po m (lbl, evt) = 
        with (do context $ assert_ctx m
                 POG.variables $ indices evt
                 POG.variables $ params evt
                 named_hyps $ invariants m
                 named_hyps $ new_guard evt)
            (emit_exist_goal [_name m, lbl, fis_lbl] pvar 
                $ M.elems $ ba_predicate m evt)
    where
        pvar = map prime $ M.elems $ variables m

tr_wd_po :: Machine -> (Label, Transient) -> M ()
tr_wd_po  m (lbl, Transient vs p _ _) = 
        with (do prefix_label $ _name m
                 prefix_label lbl
                 prefix_label "TR"
                 context $ step_ctx m
                 named_hyps $ invariants m) $
            do  emit_goal ["WD"]
                    $ well_definedness $ zforall (elems vs) ztrue p

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
                 named_hyps $ inv $ inh_props m
                 named_hyps $ inv_thm $ inh_props m)
            $ emit_goal ["INV", "WD"] 
                $ well_definedness $ zall $ elems $ invariants m

init_wd_po :: Machine -> M ()
init_wd_po m = 
        with (do prefix_label $ _name m
                 context $ assert_ctx m
                 named_hyps $ inv $ inh_props m
                 named_hyps $ inv_thm $ inh_props m)
            $ emit_goal ["INIT", "WD"] 
                $ well_definedness $ zall $ elems $ inits m

evt_wd_po :: Machine -> (Label, Event) -> M ()
evt_wd_po m (lbl, evt) = 
        with (do prefix_label $ _name m
                 prefix_label lbl
                 prefix_label "WD"
                 context $ assert_ctx m
                 POG.variables $ indices evt
                 named_hyps $ invariants m)
            (do emit_goal ["C_SCH"] 
                    $ well_definedness $ zall $ elems 
                    $ coarse $ new_sched evt
                emit_goal ["F_SCH"]
                    $ well_definedness $ zall $ map snd $ maybeToList 
                    $ fine $ new_sched evt
                with (POG.variables $ params evt)
                    (do emit_goal ["GRD"]
                            $ well_definedness $ zall $ elems
                            $ new_guard evt
                        with (do prefix_label "ACT"
                                 named_hyps $ new_guard evt
                                 context $ step_ctx m) $ do
                            let p k _ = k `S.notMember` old_acts evt
                            forM_ (toList $ M.filterWithKey p $ actions evt) $ \(tag,bap) -> 
                                emit_goal [tag] 
                                    $ well_definedness $ ba_pred bap)
                )

evt_eql_po :: Machine -> (Label, Event) -> M ()
evt_eql_po  m (lbl, evt) = 
    with (do prefix_label $ _name m
             prefix_label lbl
             prefix_label "EQL"
             context $ evt_live_ctx evt
             context $ evt_saf_ctx evt
             context $ step_ctx m
             named_hyps $ invariants m
             named_hyps $ new_guard evt
             named_hyps $ ba_predicate m evt)
        (forM_ (S.toList $ eql_vars evt) $ \v -> do
            emit_goal [label $ name v] 
                $ Word (prime v) `zeq` Word v )

    -- todo: partition the existential quantifier
sch_po :: Machine -> (Label, Event) -> M ()
sch_po m (lbl, evt) = 
    with (do prefix_label $ _name m
             prefix_label lbl
             context $ assert_ctx m
             context $ evt_live_ctx evt
             POG.variables ind
             named_hyps hyp)
         $ emit_goal [sch_lbl] $ zexists (M.elems param) ztrue $ zall grd
    where
        grd   = M.elems $ new_guard evt
        c_sch = coarse $ new_sched evt
        f_sch = M.fromList $ maybeToList $ fine $ new_sched evt
        param = params evt
        ind   = indices evt `merge` params evt
        hyp   = invariants m `M.union` f_sch `M.union` c_sch

thm_po :: Machine -> (Label, Expr) -> M ()
thm_po m (lbl, xp) = 
    with (do
            prefix_label $ _name m
            prefix_label lbl
            prefix_label thm_lbl
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
        pos <- hoistEither $ obligations empty_ctx empty_sequent c
        rs  <- lift $ forM pos discharge
        let ln = filter ((/= Valid) . fst) $ zip rs [0..]
        return ln

dump :: String -> Map Label Sequent -> IO ()
dump name pos = do
        withFile (name ++ ".z") WriteMode (\h -> do
            forM_ (M.toList pos) (\(lbl, po) -> do
                hPutStrLn h (format "(echo \"> {0}\")\n(push)" lbl)
                hPutStrLn h (concat $ map f $ z3_code po)
                hPutStrLn h "(pop)"
                hPutStrLn h ("; end of " ++ show lbl)
                ) )
    where
        f x = pretty_print' x

verify_all :: Map Label Sequent -> IO (Map Label Bool)
verify_all pos = do
    let xs = M.toList pos
    let (lbls,pos) = unzip xs 
    ys <- map_failures (lbls !!) 
            $ discharge_all pos
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
                rs <- flip filterM (M.toList pos) $ \(_,po) -> do
                    r <- smoke_test po
                    return $ r == Valid
                return $ unlines $ map (show . fst) rs
            Left msgs -> return (unlines $ map report msgs)

format_result :: Map Label Bool -> IO (String,Int,Int)
format_result xs = do
        let rs    = map f $ M.toList xs
        let total = length rs
        let passed = length $ filter fst rs
        let xs = "passed " ++ (show passed) ++ " / " ++ show total
        let ys = map snd rs ++ [xs]
        return (unlines ys, passed, total)
    where
        f (y,True)  = (True, "  o  " ++ show y)
        f (y,False) = (False," xxx " ++ show y)
