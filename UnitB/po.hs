module UnitB.PO where

import Control.Monad hiding (guard)

import Data.Map as M hiding (map, foldl, foldr, delete, filter, null)
import qualified Data.Map as M
import Data.List hiding (inits, union,insert)

import System.IO
import System.IO.Unsafe

import UnitB.AST
import UnitB.Theory
import UnitB.Calculation

import Z3.Z3

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

theory_ctx :: Theory -> Context
theory_ctx (Theory d ts f c _ dums) = 
    merge_all_ctx 
        (Context ts c f empty dums : map theory_ctx d)

theory_facts :: Theory -> Map Label Expr
theory_facts (Theory d _ _ _ f _) = 
    merge_all (f : map theory_facts d)

assert_ctx :: Machine -> Context
assert_ctx m = merge_ctx
          (Context empty (variables m) empty empty empty)
          (theory_ctx $ theory m)
step_ctx :: Machine -> Context
step_ctx m = merge_all_ctx 
        [  Context empty (prime_all $ variables m) empty empty empty
        ,  Context empty (variables m) empty empty empty
        , (theory_ctx $ theory m) ]
    where
        prime_all vs = mapKeys (++ "'") $ M.map prime_var vs
        prime_var (Var n t) = (Var (n ++ "@prime") t)

evt_saf_ctx :: Event -> Context
evt_saf_ctx evt  = Context empty (params evt) empty empty empty

evt_live_ctx :: Event -> Context
evt_live_ctx evt = Context empty (indices evt) empty empty empty

skip_event m = empty_event { action = 
    fromList $ zip 
        (map (\i -> label ("S" ++ show i)) [0 ..])
        (map (\v -> primed (variables m) (Word v) `zeq` (Word v))  
            $ elems $ variables m) }

invariants p = elems (inv p) ++ elems (inv_thm p)

invariants_only p = elems (inv p)

proof_obligation :: Machine -> Map Label ProofObligation
proof_obligation m = M.map f $ unions (
           (map (uncurry $ prop_po m) $ toList $ program_prop p)
        ++ [init_fis_po m]
        ++ (map (uncurry $ inv_po m) $ toList $ inv p) 
        ++ (map (uncurry $ sch_po m) $ toList $ events m)
        ++ (map (uncurry $ fis_po m) $ toList $ events m)
        ++ (map (uncurry $ thm_po m) $ toList $ inv_thm p) )
    where
        p = props m
        f (ProofObligation a b c d) = ProofObligation a (elems (theory_facts $ theory m)++b) c d

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
                (           step_ctx m 
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
        dummy = Context empty fv empty empty empty    
        exist_ind xp = if M.null ind then xp else zexists (elems ind) xp
prop_po m pname (Co fv xp) = 
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
                    (step_ctx m `merge_ctx` Context empty ind empty empty empty) 
                    (invariants p ++ grd ++ act)
                    False
                    (primed (variables m) xp))
            where
                grd = elems $ guard evt
                act = elems $ action evt
                ind = indices evt `merge` params evt
        po_name evt_lbl = composite_label [_name m, evt_lbl, inv_lbl, pname]

fis_po m lbl evt = singleton
        (composite_label [_name m, lbl, fis_lbl])
        (ProofObligation 
            (assert_ctx m `merge_ctx` Context empty ind empty empty empty)
            (invariants p ++ grd)
            True
            (zexists pvar act))
    where
        p    = props m
        grd  = elems $ guard evt
        act  = zall $ elems $ action evt
        pvar = map prime $ elems $ variables m
        ind  = indices evt `merge` params evt

sch_po :: Machine -> Label -> Event -> Map Label ProofObligation
sch_po m lbl evt = singleton
        (composite_label [_name m, lbl, sch_lbl])
        (ProofObligation 
            (           assert_ctx m 
            `merge_ctx` evt_live_ctx evt
            `merge_ctx` Context empty ind empty empty empty)
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
--        ind   = indices evt
        ind   = indices evt `merge` params evt
        exist_param xp = if M.null param then xp else zexists (M.elems param) xp

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
        | vn `member` vs    = Word (Var (vn ++ "@prime") vt)
        | otherwise         = w
primed _ c@(Const _ _)      = c
primed vs (FunApp f xs)     = FunApp f $ map (primed vs) xs
primed vs (Binder q d xp)   = Binder q d (primed (foldr M.delete vs (map name d)) xp)
--primed _ x@(Number _)       = x

verify_machine :: Machine -> IO (Int, Int)
verify_machine m = do
    (s,i,j) <- str_verify_machine m
    putStrLn s
    return (i,j)

str_verify_machine :: Machine -> IO (String, Int, Int)
str_verify_machine m = 
    (do
        let pos = proof_obligation m
        rs <- forM (toList pos) (\(lbl, po) -> do
            if lbl `member` proofs ps then do
                let p@(Calc _ _ _ steps li) = proofs ps ! lbl
                r0 <- check p
                r1 <- entails (goal_po p) po
                case (r0,r1) of
                    (Just [], Valid) -> 
                        return (True, ["  o  " ++ show lbl])
                    (r0,r1) -> do
                        let xs = [" xxx " ++ show lbl]
                        ys <- case r0 of
                            Just r0 -> do
                                    let (r2,r3) = break (1 <=) $ map snd r0
                                    if null r0
                                        then return []
                                        else
                                            let f (n,(_,_,_,k)) =  if n `elem` r3 
                                                                   then [
                                                                    "    invalid step:  " 
                                                                    ++ show k]
                                                                   else [] 
                                            in
                                            return $ map ("     " ++) ( [
                                                   "incorrect proof: "] 
                                                ++ ( if null r2 
                                                     then [] 
                                                     else ["    cannot prove a relationship " ++
                                                           "between the first and the last line: " ++ 
                                                           show li ] )
                                                ++ concatMap f (zip [1..] steps) )
                            Nothing -> return ["     type error in proof"]
                        zs <- case r1 of
                            Valid -> return []
                            x ->     return [
                                    "     "
                                ++ "proof does not match proof obligation: " ++ show li]
                        return (False, xs ++ ys ++ zs)
            else do
                r <- discharge po
                case r of
                    Valid -> do
                        return (True, ["  o  " ++ show lbl])
                    x     -> do
                        return (False, [" xxx " ++ show lbl]))
        let total = length rs
        let passed = length $ filter fst rs
        let xs = "passed " ++ (show passed) ++ " / " ++ show total
        let ys = concatMap snd rs ++ [xs]
        return (unlines ys, passed, total))
    where
        ps = props m
        