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
import Control.Monad.Trans
import Control.Monad.Trans.Either

import           Data.Map as M hiding 
                    ( map, foldl, foldr
                    , delete, filter, null
                    , (\\), mapMaybe )
import qualified Data.Map as M
import           Data.Maybe as MM ( maybeToList, isJust ) 
import           Data.List as L hiding (inits, union,insert)

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

skip_event :: Machine -> Event
skip_event m = empty_event { action = 
    M.fromList $ zip 
        (map (\i -> label ("S" ++ show i)) [0 ..])
        (map (\v -> primed (variables m) (Word v) `zeq` (Word v))  
            $ M.elems $ variables m) }

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
        pos = M.map f $ M.unions (
               (map (uncurry $ prop_tr m) $ M.toList $ transient p)
            ++ (map (uncurry $ prop_co m) $ M.toList $ constraint p)
            ++ (map (uncurry $ prop_saf m) $ M.toList $ safety p)
            ++ [init_fis_po m]
            ++ (map (uncurry $ inv_po m) $ M.toList $ inv p) 
            ++ (map (uncurry $ sch_po m) $ M.toList $ events m)
            ++ (map (uncurry $ fis_po m) $ M.toList $ events m)
            ++ (map (uncurry $ thm_po m) $ M.toList $ inv_thm p)
            ++ [inv_wd_po m]
            ++ [init_wd_po m]
            ++ (map (uncurry $ tr_wd_po m) $ M.toList $ transient p)
            ++ (map (uncurry $ co_wd_po m) $ M.toList $ constraint p)
            ++ (map (uncurry $ saf_wd_po m) $ M.toList $ safety p)
            ++ (map (uncurry $ prog_wd_po m) $ M.toList $ progress p)
            ++ (map (uncurry $ evt_wd_po m) $ M.toList $ events m)
            ++ (map (uncurry $ ref_po m) $ M.toList $ derivation p))
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

ref_po :: Machine -> Label -> Rule -> Map Label Sequent
ref_po m lbl (Rule r) = mapKeys f $ refinement_po r m
    where
        f x
            | show x == "" = composite_label [label $ name m, lbl,"REF",rule_name r]
            | otherwise    = composite_label [label $ name m, lbl,"REF",rule_name r,x]

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

init_fis_po :: Machine -> Map Label Sequent
init_fis_po m = eval_generator $ with 
        (do prefix_label $ _name m
            context (assert_ctx m))
        (emit_exist_goal [init_fis_lbl] 
            (M.elems $ variables m) 
            (M.elems $ inits m))

prop_tr :: Machine -> Label -> Transient -> Map Label Sequent
prop_tr m pname (Transient fv xp evt_lbl (TrHint hint lt_fine)) = 
    M.fromList 
        $ if M.null ind0 then 
            [ po0
            , po1
            ] ++ map (uncurry po) xps
          else
            [ po [] $ exist_ind $ zall $ xp0:xp1:map snd xps ]
    where
--        thm  = inv_thm p
        grd  = new_guard evt
        sch0 = coarse $ new_sched evt
        sch1 = fromList $ maybeToList $ fine $ new_sched evt
        sch  = sch0 `M.union` sch1
        act  = action evt
        evt  = events m ! evt_lbl
        ind  = indices evt
        ind0 = indices evt `M.difference` hint
        ind1 = indices evt `M.intersection` hint
        new_defs = flip map (M.toList ind1) 
                $ \(x,Var n t) -> (n ++ "@param", Def [] (n ++ "@param") [] t $ hint ! x)
        def_ctx = Context M.empty M.empty M.empty (M.fromList new_defs) M.empty
        param_ctx = Context M.empty (params evt) M.empty M.empty M.empty
        dummy = Context M.empty fv M.empty  M.empty  M.empty    
        exist_ind xp = zexists 
                    (map (add_suffix "@param") $ M.elems ind0) 
                    ztrue xp
        ctx = (           assert_ctx m 
                `merge_ctx` step_ctx m 
                `merge_ctx` dummy
                `merge_ctx` def_ctx) 
        po lbl xp = 
          ( (composite_label $ [_name m, evt_lbl, tr_lbl, pname] ++ lbl)
            , Sequent 
                ctx
                []
                (invariants m)
                xp)
        xp0 = (xp `zimplies` (new_dummy ind $ zall (M.elems sch0)))
        po0 = po ["EN"] xp0
        po1 = 
            ( (composite_label $ [_name m, evt_lbl, tr_lbl, pname, "NEG"])
            , Sequent 
                (ctx `merge_ctx` param_ctx)
                []
                (          invariants m 
                 `M.union` M.map (new_dummy ind) (M.unions [sch,grd,act]))
                $ xp `zimplies` (znot $ primed (variables m) xp) )
        xp1 = (zforall  
                    (M.elems $ params evt)
                    (xp `zand` (new_dummy ind $ zall (M.elems $ M.unions [sch, grd, act])))
                    (znot $ primed (variables m) xp) )
        xps = case (lt_fine, fine $ new_sched evt) of
                (Just lbl, Just (_,fsch)) ->
                    let (LeadsTo vs p q) = (progress (props m) `M.union` progress (inh_props m)) ! lbl in
                        [ (["EN/leadsto/lhs"],zforall vs ztrue $ zall (M.elems sch0) `zimplies` p)
                        , (["EN/leadsto/rhs"],zforall vs ztrue $ q `zimplies` fsch) 
                        ]
                (Nothing,Nothing) -> []
                _                 -> error $ format (
                           "transient predicate {0}'s side condition doesn't "
                        ++ "match the fine schedule of event {1} ({2},{3})"
                        )
                    pname evt_lbl (isJust lt_fine) (isJust $ fine $ new_sched evt)

prop_co :: Machine -> Label -> Constraint -> Map Label Sequent
prop_co m pname (Co fv xp) = eval_generator $ with
        (do prefix_label $ _name m
            context $ step_ctx m
            context $ dummy_ctx m
            named_hyps $ invariants m)
        $ forM_ evts $ \(evt_lbl,evt) -> do
            let grd  = new_guard evt
                act  = action evt
            with 
                (do named_hyps $ grd
                    named_hyps $ act
                    POG.variables $ indices evt
                    POG.variables $ params evt)
                (emit_goal [evt_lbl,co_lbl,pname] $ forall_fv xp)
    where
        evts = toList (M.insert 
                ("SKIP") 
                (skip_event $ m) 
                (events $ m))
        forall_fv xp = if L.null fv then xp else zforall fv ztrue xp

prop_saf :: Machine -> Label -> SafetyProp -> Map Label Sequent
prop_saf m pname (Unless fv p q excp) = eval_generator $ with
        (do prefix_label $ _name m
            context $ step_ctx m
            context $ dummy_ctx m
            named_hyps $ invariants m)
        $ forM_ evts $ \(evt_lbl,evt) -> do
            let grd  = new_guard evt
                act  = action evt
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

inv_po :: Machine -> Label -> Expr -> Map Label Sequent
inv_po m pname xp = eval_generator $ 
    do  with (do prefix_label $ _name m
                 context $ step_ctx m
                 named_hyps $ invariants m)
            $ forM_ (toList $ events m) $ \(evt_lbl,evt) -> do
                let grd  = new_guard evt
                    act  = action evt
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

fis_po :: Machine -> Label -> Event -> Map Label Sequent
fis_po m lbl evt = eval_generator $
        with (do context $ assert_ctx m
                 POG.variables $ indices evt
                 POG.variables $ params evt
                 named_hyps $ invariants m
                 named_hyps $ new_guard evt)
        (emit_exist_goal [_name m, lbl, fis_lbl] pvar 
            $ M.elems $ action evt)
    where
        pvar = map prime $ M.elems $ variables m

tr_wd_po :: Machine -> Label -> Transient -> Map Label Sequent
tr_wd_po  m lbl (Transient vs p _ _) = eval_generator $
        with (do prefix_label $ _name m
                 prefix_label lbl
                 prefix_label "TR"
                 context $ step_ctx m
                 named_hyps $ invariants m) $
        do  emit_goal ["WD"]
                $ well_definedness $ zforall (elems vs) ztrue p

prog_wd_po :: Machine -> Label -> ProgressProp -> Map Label Sequent
prog_wd_po m lbl (LeadsTo vs p q) = eval_generator $
        with (do prefix_label $ _name m
                 prefix_label lbl
                 prefix_label "PROG"
                 context $ step_ctx m
                 named_hyps $ invariants m) $
        do  emit_goal ["WD","lhs"]
                $ well_definedness $ zforall vs ztrue p
            emit_goal ["WD","rhs"]
                $ well_definedness $ zforall vs ztrue q

saf_wd_po :: Machine -> Label -> SafetyProp -> Map Label Sequent
saf_wd_po m lbl (Unless vs p q _) = eval_generator $
        with (do prefix_label $ _name m
                 prefix_label lbl
                 prefix_label "SAF"
                 context $ step_ctx m
                 named_hyps $ invariants m) $
        do  emit_goal ["WD","lhs"]
                $ zforall vs ztrue $ (znot q) `zimplies` (well_definedness p)
            emit_goal ["WD","rhs"]
                $ well_definedness $ zforall vs ztrue q

co_wd_po :: Machine -> Label -> Constraint -> Map Label Sequent
co_wd_po m lbl (Co vs p) = eval_generator $
        with (do prefix_label $ _name m
                 prefix_label lbl
                 prefix_label "CO"
                 context $ step_ctx m
                 nameless_hyps $ M.elems $
                    M.map (primed $ variables m) $ invariants m
                 named_hyps $ invariants m)
         $ emit_goal ["WD"]
            $ well_definedness $ zforall vs ztrue p

inv_wd_po :: Machine -> Map Label Sequent
inv_wd_po m = eval_generator $ 
        with (do prefix_label $ _name m
                 context $ assert_ctx m
                 named_hyps $ inv $ inh_props m
                 named_hyps $ inv_thm $ inh_props m)
        $ emit_goal ["INV", "WD"] 
            $ well_definedness $ zall $ elems $ invariants m

init_wd_po :: Machine -> Map Label Sequent
init_wd_po m = eval_generator $
        with (do prefix_label $ _name m
                 context $ assert_ctx m
                 named_hyps $ inv $ inh_props m
                 named_hyps $ inv_thm $ inh_props m)
        $ emit_goal ["INIT", "WD"] 
            $ well_definedness $ zall $ elems $ inits m

evt_wd_po :: Machine -> Label -> Event -> Map Label Sequent
evt_wd_po m lbl evt = eval_generator $ 
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
                                 context $ step_ctx m) $
                            forM_ (toList $ M.map well_definedness 
                                    $ action evt) 
                                $ uncurry $ emit_goal . (:[]))
                            -- $ emit_goal ["ACT"]
                            --     $ well_definedness $ zall $ elems
                            --     $ action evt)
                )

    -- todo: partition the existential quantifier
sch_po :: Machine -> Label -> Event -> Map Label Sequent
sch_po m lbl evt = eval_generator $
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

thm_po :: Machine -> Label -> Expr -> Map Label Sequent
thm_po m lbl xp = M.singleton
        (composite_label [_name m, lbl, thm_lbl])
        (Sequent
            (assert_ctx m)
            []
            inv
            xp)
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
                return (old_pos,unlines $ map g msgs,0)
    where
        f p0 (_,p1)
            | p0 == p1  = Nothing 
            | otherwise = Just p0
        g (Error xs (LI _ i j)) = format "error ({0},{1}): {2}" i j (xs :: String) :: String
                 
str_verify_machine :: Machine -> IO (String,Int,Int)
str_verify_machine m = 
        case proof_obligation m of
            Right pos -> do
--                dump (show $ _name m) pos
                xs <- verify_all pos
                format_result xs
            Left msgs -> return (unlines $ map f msgs,0,0)
    where
        f (Error xs (LI _ i j)) = format "error ({0},{1}): {2}" i j (xs :: String) :: String

smoke_test_machine :: Machine -> IO (String)
smoke_test_machine m =
        case proof_obligation m of 
            Right pos -> do
                rs <- flip filterM (M.toList pos) $ \(_,po) -> do
                    r <- smoke_test po
                    return $ r == Valid
                return $ unlines $ map (show . fst) rs
            Left msgs -> return (unlines $ map f msgs)
    where
        f (Error xs (LI _ i j)) = format "error ({0},{1}): {2}" i j (xs :: String) :: String

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
