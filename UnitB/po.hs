module UnitB.PO where

import Control.Monad hiding (guard)

import Data.Map as M hiding (map, foldl, foldr, delete, filter, null)
import qualified Data.Map as M
import Data.List hiding (inits, union,insert)

import System.IO
import System.IO.Unsafe

import UnitB.AST

import Z3.Z3
import Z3.Const
import Z3.Def
import Z3.Calculation

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
    -- Discharge POs using calculational proofs
    -- add theorem POs
    --      problem: In what order do we prove the theorems?
    -- add free variables to co and transient properties

tr_neg_lbl      = label "TR/NEG"
tr_en_lbl       = label "TR/EN"
co_lbl          = label "CO"
inv_lbl         = label "INV"
inv_init_lbl    = label "INIT/INV"
init_fis_lbl    = label "INIT/FIS"
fis_lbl         = label "FIS"
sch_lbl         = label "SCH"
thm_lbl         = label "THM"

theory_ctx (Theory d f c _) = merge_all_ctx (Context c f empty : map theory_ctx d)

theory_facts (Theory d _ _ f) = merge_all (f : map theory_facts d)

assert_ctx m = merge_all_ctx (
           Context (variables m) empty empty
        : (map theory_ctx $ theories m))

step_ctx m = merge_all_ctx (
           Context (prime_all $ variables m) empty empty
        :  Context (variables m) empty empty
        : (map theory_ctx $ theories m))
    where
        prime_all vs = mapKeys (++ "'") $ M.map prime_var vs
        prime_var (Var n t) = (Var (n ++ "_prime") t)

evt_saf_ctx evt  = Context (fromList $ map as_pair $ params evt) empty empty
evt_live_ctx evt = Context (fromList $ map as_pair $ indices evt) empty empty

skip_event m = empty_event { action = 
    fromList $ zip 
        (map (\i -> label ("S" ++ show i)) [0 ..])
        (map (\v -> primed (variables m) (Word v) `zeq` (Word v))  
            $ elems $ variables m) }

invariants p = elems (inv p) ++ elems (inv_thm p)

invariants_only p = elems (inv p)

proof_obligation :: Machine -> Map Label ProofObligation
proof_obligation m = unions (
           (map (uncurry $ prop_po m) $ toList $ program_prop p)
        ++ [init_fis_po m]
        ++ (map (uncurry $ inv_po m) $ toList $ inv p) 
        ++ (map (uncurry $ sch_po m) $ toList $ events m)
        ++ (map (uncurry $ fis_po m) $ toList $ events m)
        ++ (map (uncurry $ thm_po m) $ toList $ inv_thm p) )
    where
        p = props m

init_fis_po :: Machine -> Map Label ProofObligation
init_fis_po m = singleton (composite_label [_name m, init_fis_lbl]) po
    where
        po = ProofObligation (assert_ctx m) [] True goal
        goal 
            | M.null $ variables m  = ztrue
            | otherwise             = (zexists (elems $ variables m) $ zall $ inits m)

prop_po :: Machine -> Label -> ProgramProp -> Map Label ProofObligation
prop_po m pname (Transient fv xp evt_lbl) = 
        fromList [ 
            ( (composite_label [_name m, evt_lbl, tr_neg_lbl, pname]),
              (ProofObligation 
                (  step_ctx m 
                `merge_ctx` evt_live_ctx evt
                `merge_ctx` evt_saf_ctx evt
                `merge_ctx` dummy) 
                (xp:(invariants p ++ grd ++ sch ++ act)) 
                False
                (znot $ primed (variables m) xp)) ),
            ( (composite_label [_name m, evt_lbl, tr_en_lbl, pname]),
              (ProofObligation 
                (assert_ctx m `merge_ctx` dummy) 
                (invariants p)
                True
                (exist_ind (xp `zimplies` (zall sch)))) ) ]
    where
        p    = props m
        prop = program_prop p
        thm  = inv_thm p
        grd  = elems $ guard evt
        sch  = case c_sched evt of
                Just sch -> elems sch
                Nothing  -> [zfalse]
        act  = elems $ action evt
        evt  = events m ! evt_lbl
        ind  = indices evt
        dummy = Context (fromList $ map as_pair fv) empty empty
        exist_ind xp = if null ind then xp else zexists ind xp
prop_po m pname (Co fv xp) = --error "not implemented"
        mapKeys po_name $ mapWithKey po 
            (insert 
                (label "SKIP") 
                (skip_event $ m) 
                (events $ m))
    where
        p = props m
        po lbl evt = 
                (ProofObligation 
                    (step_ctx $ m) 
                    (invariants p ++ grd ++ act)
                    False
                    (forall_fv xp) )
            where
                grd = elems $ guard evt
                act = elems $ action evt
                forall_fv xp = if null fv then xp else zforall fv xp
        po_name evt_lbl = composite_label [_name m, evt_lbl, co_lbl, pname]

inv_po m pname xp = 
        union 
            (mapKeys po_name $ mapWithKey po (events m))
            (singleton 
                (composite_label [_name m, inv_init_lbl, pname])
                (ProofObligation (assert_ctx m) (inits m) False xp))
    where
        p = props m
        po lbl evt = 
                (ProofObligation 
                    (step_ctx m `merge_ctx` Context ind empty empty) 
                    (invariants p ++ grd ++ act)
                    False
                    (primed (variables m) xp))
            where
                grd = elems $ guard evt
                act = elems $ action evt
                ind = fromList $ map as_pair (indices evt ++ params evt)
        po_name evt_lbl = composite_label [_name m, evt_lbl, inv_lbl, pname]

fis_po m lbl evt = singleton
        (composite_label [_name m, lbl, fis_lbl])
        (ProofObligation 
            (assert_ctx m `merge_ctx` Context ind empty empty)
            (invariants p ++ grd)
            True
            (zexists pvar act))
    where
        p    = props m
        grd  = elems $ guard evt
--        sch  = elems $ c_sched evt
        act  = zall $ elems $ action evt
        pvar = map prime $ elems $ variables m
        ind  = fromList $ map as_pair (indices evt ++ params evt)

sch_po m lbl evt = singleton
        (composite_label [_name m, lbl, sch_lbl])
        (ProofObligation 
            (assert_ctx m `merge_ctx` evt_live_ctx evt)
            (invariants p ++ sch)
            True
            (exist_param $ zall grd))
    where
        p     = props m
        grd   = elems $ guard evt
        sch   = case c_sched evt of
                  Just sch -> elems sch
                  Nothing  -> [zfalse]
        param = params evt
        ind   = indices evt
        exist_param xp = if null param then xp else zexists param xp

thm_po m lbl xp = singleton
        (composite_label [_name m, lbl, thm_lbl])
        (ProofObligation
            (assert_ctx m)
            (invariants p)
            False
            xp)
    where
        p = props m

primed :: Map String Var -> Expr -> Expr
primed vs w@(Word (Var vn vt)) 
        | vn `member` vs    = Word (Var (vn ++ "_prime") vt)
        | otherwise         = w
primed _ c@(Const _ _)      = c
primed vs (FunApp f xs)     = FunApp f $ map (primed vs) xs
primed vs (Binder q d xp)   = Binder q d (primed (foldr M.delete vs (map name d)) xp)
primed _ x@(Number _)       = x

--act_decl :: Machine -> String -> [Decl]
--act_decl = error "not implemented"

verify_machine :: Machine -> IO (Int, Int)
verify_machine m = h_verify_machine stdout m

str_verify_machine :: Machine -> IO (String, Int, Int)
str_verify_machine m = -- unsafeInterleaveIO 
    (do
        let pos = proof_obligation m
--        let !() = unsafePerformIO (putStrLn 
--                ("checking proof: " ++ show (keys $ proofs $ props m)))
        rs <- forM (toList pos) (\(lbl, po) -> do
--            putStrLn $ show lbl
--            print po
            if lbl `member` proofs ps then do
--                let !() = unsafePerformIO (putStrLn ("check a proof... " ++ show lbl))
                r0 <- check (proofs ps ! lbl)
                r1 <- entails (goal_po (proofs ps ! lbl)) po
--                let !() = unsafePerformIO $ print r0
--                let !() = unsafePerformIO $ print r1
                case (r0,r1) of
                    ([], Valid) -> 
                        return (True, [" o " ++ show lbl])
                    (r0,r1) -> do
                        let xs = [" x " ++ show lbl]
                        ys <- if null r0
                            then return []
                            else return ["     " ++ "incorrect proof: " ++ show (map snd r0)]
                        zs <- case r1 of
                            Valid -> return []
                            x -> return ["     " ++ "proof does not match goal"]
                        return (False, xs ++ ys ++ zs)
            else do
                r <- discharge po
                case r of
                    Valid -> do
                        return (True, [" o " ++ show lbl])
                    x     -> do
                        return (False, [" x " ++ show lbl]))
        let total = length rs
        let passed = length $ filter fst rs
        let xs = "passed " ++ (show passed) ++ " / " ++ show total
        let ys = concatMap snd rs ++ [xs]
        return (unlines ys, passed, total))
    where
        ps = props m
        
h_verify_machine :: Handle -> Machine -> IO (Int, Int)
h_verify_machine h m = do
        rs <- forM (toList $ proof_obligation m) (\(lbl, po) -> do
            if lbl `member` proofs ps then do
                r0 <- check (proofs ps ! lbl)
                r1 <- entails (goal_po (proofs ps ! lbl)) po
                case (r0,r1) of
                    ([], Valid) -> (do
                        hPutStrLn h (" o " ++ show lbl)
                        return True)
                    (r0,r1) -> do
                        hPutStrLn h (" x " ++ show lbl)
                        if null r0 then
                            hPutStrLn h ("     " ++ "incorrect proof")
                        else return ()
                        case r1 of
                            Valid -> hPutStrLn h ("     " ++ "proof does not match goal")
                            x -> return ()
                        return False
            else do
                r <- discharge po
                case r of
                    Valid -> (do
                        hPutStrLn h (" o " ++ show lbl)
                        return True)
                    x     -> (do
                        hPutStrLn h (" x " ++ show lbl)
                        return False))
        let total = length rs
        let passed = length $ filter id rs
        hPutStrLn h ("passed " ++ (show passed) ++ " / " ++ show total)
        return (passed, total)
    where
        ps = props m