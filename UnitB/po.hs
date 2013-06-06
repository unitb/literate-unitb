module UnitB.PO where

import Control.Monad hiding (guard)

import Data.Map as M hiding (map, foldl, foldr, delete, filter, null)
import qualified Data.Map as M
import Data.List hiding (inits, union,insert)

import System.IO

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
inv_init_lbl    = label "INV/INIT"
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

proof_obligation :: PropertySet -> Map Label ProofObligation
proof_obligation p = unions (
           (map (uncurry $ prop_po p) $ toList $ prog_prop p)
        ++ (map (uncurry $ inv_po p) $ toList $ inv p) 
        ++ (map (uncurry $ sch_po p) $ toList $ events $ machine p)
        ++ (map (uncurry $ fis_po p) $ toList $ events $ machine p)
        ++ (map (uncurry $ thm_po p) $ toList $ inv_thm p) )

prop_po :: PropertySet -> Label -> ProgProp -> Map Label ProofObligation
prop_po p pname (Transient fv xp evt_lbl) = 
        fromList [ 
            ( (composite_label [_name m, evt_lbl, tr_neg_lbl, pname]),
              (ProofObligation 
                (  step_ctx m 
                `merge_ctx` evt_live_ctx evt
                `merge_ctx` evt_saf_ctx evt
                `merge_ctx` dummy) 
                (xp:(invariants p ++ grd ++ sch ++ act)) 
                (znot $ primed (variables m) xp)) ),
            ( (composite_label [_name m, evt_lbl, tr_en_lbl, pname]),
              (ProofObligation 
                (assert_ctx m `merge_ctx` dummy) 
                (invariants p)
                (exist_ind (xp `zimplies` (zall sch)))) ) ]
    where
        m    = machine p
        prop = prog_prop p
        thm  = inv_thm p
        grd  = elems $ guard evt
        sch  = elems $ c_sched evt
        act  = elems $ action evt
        evt  = events m ! evt_lbl
        ind  = indices evt
        dummy = Context (fromList $ map as_pair fv) empty empty
        exist_ind xp = if null ind then xp else zexists ind xp
prop_po p pname (Co fv xp) = --error "not implemented"
        mapKeys po_name $ mapWithKey po 
            (insert 
                (label "SKIP") 
                (skip_event $ machine p) 
                (events $ machine p))
    where
        po lbl evt = 
                (ProofObligation 
                    (step_ctx $ machine p) 
                    (invariants p ++ grd ++ act)
                    (forall_fv xp) )
            where
                grd = elems $ guard evt
                act = elems $ action evt
                forall_fv xp = if null fv then xp else zforall fv xp
        po_name evt_lbl = composite_label [_name $ machine p, evt_lbl, co_lbl, pname]

inv_po p pname xp = 
        union 
            (mapKeys po_name $ mapWithKey po (events $ machine p))
            (singleton 
                (composite_label [_name $ machine p, inv_init_lbl, pname])
                (ProofObligation (assert_ctx $ machine p) (inits $ machine p) xp))
    where
        po lbl evt = 
                (ProofObligation 
                    (step_ctx (machine p) `merge_ctx` Context ind empty empty) 
                    (invariants p ++ grd ++ act)
                    xp)
            where
                grd = elems $ guard evt
                act = elems $ action evt
                ind = fromList $ map as_pair (indices evt ++ params evt)
        po_name evt_lbl = composite_label [_name $ machine p, evt_lbl, inv_lbl, pname]

fis_po p lbl evt = singleton
        (composite_label [_name $ machine p, lbl, fis_lbl])
        (ProofObligation 
            (assert_ctx (machine p) `merge_ctx` Context ind empty empty)
            (invariants p ++ grd)
            (zexists pvar act))
    where
        grd  = elems $ guard evt
        sch  = elems $ c_sched evt
        act  = zall $ elems $ action evt
        pvar = map prime $ elems $ variables $ machine p
        ind  = fromList $ map as_pair (indices evt ++ params evt)

sch_po p lbl evt = singleton
        (composite_label [_name $ machine p, lbl, sch_lbl])
        (ProofObligation 
            (assert_ctx (machine p) `merge_ctx` evt_live_ctx evt)
            (invariants p ++ sch)
            (exist_param $ zall grd))
    where
        grd   = elems $ guard evt
        sch   = elems $ c_sched evt
        param = params evt
        ind   = indices evt
        exist_param xp = if null param then xp else zexists param xp

thm_po p lbl xp = singleton
        (composite_label [_name $ machine p, lbl, thm_lbl])
        (ProofObligation
            (assert_ctx $ machine p)
            (invariants p)
            xp)

primed :: Map String Var -> Expr -> Expr
primed vs w@(Word (Var vn vt)) 
        | vn `member` vs    = Word (Var (vn ++ "_prime") vt)
        | otherwise         = w
primed _ c@(Const _ _)      = c
primed vs (FunApp f xs)     = FunApp f $ map (primed vs) xs
primed vs (Binder q d xp)   = Binder q d (primed (foldr M.delete vs (map name d)) xp)

--act_decl :: Machine -> String -> [Decl]
--act_decl = error "not implemented"

verify_machine :: PropertySet -> IO (Int, Int)
verify_machine p = h_verify_machine stdout p

h_verify_machine :: Handle -> PropertySet -> IO (Int, Int)
h_verify_machine h ps = do
        rs <- forM (toList $ proof_obligation ps) (\(lbl, po) -> do
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