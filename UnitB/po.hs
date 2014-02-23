{-# LANGUAGE BangPatterns #-}
module UnitB.PO 
    ( proof_obligation, theory_po
    , step_ctx, evt_live_ctx
    , theory_ctx, theory_facts, dummy_ctx
    , evt_saf_ctx, invariants, assert_ctx
    , str_verify_machine, raw_machine_pos
    , verify_all
    , check, verify_changes, verify_machine
    , smoke_test_machine, dump, used_types )
where

    -- Modules
import Logic.Calculation
import Logic.Classes
import Logic.Const
import Logic.Expr
import Logic.Label

import UnitB.AST
import UnitB.Feasibility

import Z3.Z3

    -- Libraries
import Control.Monad hiding (guard)

import           Data.Map as M hiding 
                    ( map, foldl, foldr
                    , delete, filter, null
                    , (\\), mapMaybe )
import qualified Data.Map as M
import           Data.Maybe as MM ( maybeToList, isJust ) 
import           Data.List as L hiding (inits, union,insert)
import qualified Data.Set as S

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

skip_event m = empty_event { action = 
    M.fromList $ zip 
        (map (\i -> label ("S" ++ show i)) [0 ..])
        (map (\v -> primed (variables m) (Word v) `zeq` (Word v))  
            $ M.elems $ variables m) }

invariants m = 
            M.elems (inv p0) 
        ++  M.elems (inv_thm p0) 
        ++  M.elems (inv p1)
        ++  M.elems (inv_thm p1)
    where
        p0 = props m
        p1 = inh_props m

invariants_only m = 
            M.elems (inv p0) 
        ++  M.elems (inv p1)
    where
        p0 = props m
        p1 = inh_props m 

raw_machine_pos :: Machine -> (Map Label Sequent)
raw_machine_pos m = pos
    where
        pos = M.map f $ M.unions (
               (map (uncurry $ prop_tr m) $ M.toList $ transient p)
            ++ (map (uncurry $ prop_co m) $ M.toList $ constraint p)
            ++ [init_fis_po m]
            ++ (map (uncurry $ inv_po m) $ M.toList $ inv p) 
            ++ (map (uncurry $ sch_po m) $ M.toList $ events m)
            ++ (map (uncurry $ fis_po m) $ M.toList $ events m)
            ++ (map (uncurry $ thm_po m) $ M.toList $ inv_thm p)
            ++ (map (uncurry $ ref_po m) $ M.toList $ derivation p))
        p = props m
        f (Sequent a b d) = Sequent 
                (a `merge_ctx` theory_ctx ts (theory m))
                (M.elems (theory_facts ts (theory m))++b) 
                d
          where
            ts = S.unions $ map used_types $ d : b

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
                    proof_po (theory m) c lbl po
                Nothing -> 
                    return [(lbl,po)])
        return $ M.fromList $ concat xs

my_trace :: Show a => String -> a -> a
--my_trace x y = trace (format "{0}\n value: {1}\n" x y) y
my_trace _ y = y

ref_po :: Machine -> Label -> Rule -> Map Label Sequent
ref_po m lbl (Rule r) = mapKeys f $ refinement_po r m
    where
        f x
            | show x == "" = my_trace (format "name: {0}\nlabel: {1}\nrule: {2}\n" (name m) lbl (rule_name r)) $ composite_label [label $ name m, lbl,label "REF",rule_name r]
            | otherwise    = my_trace (format "name: {0}\nlabel: {1}\nrule: {2}\nx: {3}\n" (name m) lbl (rule_name r) x) $ composite_label [label $ name m, lbl,label "REF",rule_name r,x]

theory_po :: Theory -> Map Label Sequent
theory_po th = mapKeys keys $ M.map (f . g) thm
    where
--        axm = M.filterKeys (not . (`S.member` theorems th)) $ fact th
        (thm,axm) = M.partitionWithKey p $ fact th
        p k _ = k `S.member` theorems th
        g x = Sequent empty_ctx (M.elems axm) x
        keys k = composite_label [label "THM",k]
        f (Sequent a b d) = Sequent 
                (a `merge_ctx` theory_ctx ts th)
                (concatMap (M.elems . theory_facts ts) (elems $ extends th) ++ b) 
                d
          where
            ts = S.unions $ map used_types $ d : b

init_fis_po :: Machine -> Map Label Sequent
init_fis_po m = M.fromList $ flip map clauses $ \(vs,es) -> 
            ( composite_label $ [_name m, init_fis_lbl] ++ map (label . name) vs
            , po $ goal vs es)
    where
        po = Sequent (assert_ctx m) []
        clauses = partition_expr (M.elems $ variables m) (M.elems $ inits m)
        goal vs es = (zexists vs ztrue $ zall es)
 

prop_tr :: Machine -> Label -> Transient -> Map Label Sequent
prop_tr m pname (Transient fv xp evt_lbl hint lt_fine) = 
    M.fromList 
        $ if M.null ind0 then 
            [ po [label "EN"] xp0
            , po [label "NEG"] xp1
            ] ++ map (uncurry po) xps
          else
            [ po [] $ exist_ind $ zall $ xp0:xp1:map snd xps ]
    where
--        thm  = inv_thm p
        grd  = M.elems $ new_guard evt
        sch0 = M.elems $ coarse $ new_sched evt
        sch1 = map snd $ maybeToList $ fine $ new_sched evt
        sch  = sch0 ++ sch1
        act  = M.elems $ action evt
        evt  = events m ! evt_lbl
        ind  = indices evt
        ind0 = indices evt `M.difference` hint
        ind1 = indices evt `M.intersection` hint
        new_defs = flip map (M.toList ind1) 
                $ \(x,Var n t) -> (n ++ "@param", Def [] (n ++ "@param") [] t $ hint ! x)
        def_ctx = Context M.empty M.empty M.empty (M.fromList new_defs) M.empty
        dummy = Context M.empty fv M.empty  M.empty  M.empty    
        exist_ind xp = zexists 
                    (map (add_suffix "@param") $ M.elems ind0) 
                    ztrue xp
        po lbl xp = 
          ( (composite_label $ [_name m, evt_lbl, tr_lbl, pname] ++ lbl)
            , Sequent 
                (           assert_ctx m 
                `merge_ctx` step_ctx m 
                `merge_ctx` dummy
                `merge_ctx` def_ctx) 
                (invariants m)
                xp)
        xp0 = (xp `zimplies` (new_dummy ind $ zall sch0))
        xp1 = (zforall  
                    (M.elems $ params evt)
                    (xp `zand` (new_dummy ind $ zall (sch ++ grd ++ act)))
                    (znot $ primed (variables m) xp) )
        xps = case (lt_fine, fine $ new_sched evt) of
                (Just lbl, Just (_,fsch)) ->
                    let (LeadsTo vs p q) = (progress (props m) `M.union` progress (inh_props m)) ! lbl in
                        [ ([label "EN/leadsto/lhs"],zforall vs ztrue $ zall sch0 `zimplies` p)
                        , ([label "EN/leadsto/rhs"],zforall vs ztrue $ q `zimplies` fsch) 
                        ]
                (Nothing,Nothing) -> []
                _                 -> error $ format (
                           "transient predicate {0}'s side condition doesn't "
                        ++ "match the fine schedule of event {1} ({2},{3})"
                        )
                    pname evt_lbl (isJust lt_fine) (isJust $ fine $ new_sched evt)

prop_co :: Machine -> Label -> Constraint -> Map Label Sequent
prop_co m pname (Co fv xp) = 
        mapKeys po_name $ mapWithKey po 
            (M.insert 
                (label "SKIP") 
                (skip_event $ m) 
                (events $ m))
    where
        po _ evt = 
                (Sequent 
                    (step_ctx m `merge_ctx` dummy_ctx m) 
                    hyp
                    goal )
            where
                grd  = M.elems $ new_guard evt
                act  = M.elems $ action evt
                forall_fv xp = if L.null fv then xp else zforall fv ztrue xp
                hyp  = invariants m ++ grd ++ act
                goal = forall_fv xp
        po_name evt_lbl = composite_label [_name m, evt_lbl, co_lbl, pname]

inv_po m pname xp = 
        M.union 
            (mapKeys po_name $ mapWithKey po (events m))
            (M.singleton 
                (composite_label [_name m, inv_init_lbl, pname])
                (Sequent (assert_ctx m) hyp xp))
    where
        po _ evt = 
                (Sequent 
                    (            step_ctx m 
                     `merge_ctx` Context M.empty ind M.empty M.empty M.empty) 
                    (invariants m ++ grd ++ act)
                    (primed (variables m) xp))
            where
                grd = M.elems $ new_guard evt
                act = M.elems $ action evt
                ind = indices evt `merge` params evt
        po_name evt_lbl = composite_label [_name m, evt_lbl, inv_lbl, pname]
        hyp  = M.elems $ inits m

fis_po m lbl evt = M.fromList $ map f pos 
    where
        grd  = M.elems $ new_guard evt
        pvar = map prime $ M.elems $ variables m
        ind  = indices evt `merge` params evt
        pos  = partition_expr pvar $ M.elems $ action evt
        f (pvar, acts) =
            ( composite_label $ [_name m, lbl, fis_lbl] ++ map (label . name) pvar,
              Sequent 
                (assert_ctx m `merge_ctx` Context M.empty ind M.empty M.empty M.empty)
                hyp
                goal)
          where
            hyp  = invariants m ++ grd
            goal = zexists pvar ztrue $ zall acts

    -- todo: partition the existential quantifier
sch_po :: Machine -> Label -> Event -> Map Label Sequent
sch_po m lbl evt = M.singleton
        (composite_label [_name m, lbl, sch_lbl])
        (Sequent 
            (           assert_ctx m 
            `merge_ctx` evt_live_ctx evt
            `merge_ctx` Context M.empty ind M.empty M.empty M.empty)
            hyp
            goal)
    where
        grd   = M.elems $ new_guard evt
        c_sch = M.elems $ coarse $ new_sched evt
        f_sch = map snd $ maybeToList $ fine $ new_sched evt
        param = params evt
        ind   = indices evt `merge` params evt
        exist_param xp = zexists (M.elems param) ztrue xp
        hyp   = invariants m ++ f_sch ++ c_sch
        goal  = exist_param $ zall grd

thm_po m lbl xp = M.singleton
        (composite_label [_name m, lbl, thm_lbl])
        (Sequent
            (assert_ctx m)
            inv
            xp)
    where
        inv = invariants_only m

add_suffix suf (Var n t) = Var (n ++ suf) t

new_dummy = make_unique "@param"

verify_machine :: Machine -> IO (Int, Int)
verify_machine m = do
    (s,i,j) <- str_verify_machine m
    putStrLn s
    return (i,j)

check :: Theory -> Calculation -> IO (Either [Error] [(Validity, Int)])
check th c = embed 
            (obligations th empty_ctx c) 
            (\pos -> do
        rs <- forM pos discharge :: IO [Validity]
        let ln = filter ((/= Valid) . fst) $ zip rs [0..] :: [(Validity, Int)]
        return ln)

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
    ys <- discharge_all pos
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
                dump (show $ _name m) pos
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
                dump (show $ _name m) pos
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