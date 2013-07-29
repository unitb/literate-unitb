{-# LANGUAGE BangPatterns #-}
module UnitB.PO where

    -- Modules
import UnitB.AST
import UnitB.Theory
import UnitB.Calculation
import UnitB.Operator

import Z3.Z3

    -- Libraries
import Control.Monad hiding (guard)

import Data.Map as M hiding (map, foldl, foldr, delete, filter, null)
import qualified Data.Map as M
import Data.List hiding (inits, union,insert)

import System.IO
import System.IO.Unsafe

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
    -- Discharge POs using calculational proofs
    -- add theorem POs
    --      problem: In what order do we prove the theorems?
    -- add free variables to co and transient properties

tr_neg_lbl      = label "TR/NEG"
tr_en_lbl       = label "TR/EN"
tr_lbl          = label "TR"
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

raw_machine_pos :: Machine -> (Map Label ProofObligation)
raw_machine_pos m = pos
    where
        pos = M.map f $ unions (
               (map (uncurry $ prop_po m) $ toList $ program_prop p)
            ++ [init_fis_po m]
            ++ (map (uncurry $ inv_po m) $ toList $ inv p) 
            ++ (map (uncurry $ sch_po m) $ toList $ events m)
            ++ (map (uncurry $ fis_po m) $ toList $ events m)
            ++ (map (uncurry $ thm_po m) $ toList $ inv_thm p))
        p = props m
        f (ProofObligation a b c d) = ProofObligation a (elems (theory_facts $ theory m)++b) c d

proof_obligation :: Machine -> Either [Error] (Map Label ProofObligation)
proof_obligation m = do
        let { pos = raw_machine_pos m }
        forM_ (toList $ proofs $ props $ m) (\(lbl,p) -> do
            let (i,j) = line_info p
            if lbl `member` pos
                then return ()
                else Left [(format "a proof is provided for non-existant proof obligation {0}" lbl,i,j)])
        xs <- forM (toList pos) (\(lbl,po) -> do
            case M.lookup lbl $ proofs $ props $ m of
                Just c ->
                    proof_po (theory m) c lbl po
                Nothing -> 
                    return [(lbl,po)])
        return $ fromList $ concat xs
    where
--        p = props m
--        f (ProofObligation a b c d) = ProofObligation a (elems (theory_facts $ theory m)++b) c d

init_fis_po :: Machine -> Map Label ProofObligation
init_fis_po m = singleton (composite_label [_name m, init_fis_lbl]) po
    where
        po = ProofObligation (assert_ctx m) [] True goal
        goal 
            | M.null $ variables m  = ztrue
            | otherwise             = (zexists (elems $ variables m) $ zall $ inits m)
 

prop_po :: Machine -> Label -> ProgramProp -> Map Label ProofObligation
prop_po m pname (Transient fv xp evt_lbl) = 
    fromList 
        [   ( (composite_label [_name m, evt_lbl, tr_lbl, pname])
            , (ProofObligation 
                (           assert_ctx m 
                `merge_ctx` step_ctx m 
                `merge_ctx` dummy) 
                (invariants p)
                True
                (exist_ind $ zand 
                        (xp `zimplies` (new_dummy ind $ zall sch))
                        (zimplies (xp `zand` (new_dummy ind $ zall (sch ++ grd ++ act)))
                                  (znot $ primed (variables m) xp)  )) )
           ) 
        ]
--        [   ( (composite_label [_name m, evt_lbl, tr_neg_lbl, pname])
--            , (ProofObligation 
--                (           step_ctx m 
--                `merge_ctx` evt_live_ctx evt
--                `merge_ctx` evt_saf_ctx evt
--                `merge_ctx` dummy) 
--                (invariants p ++ grd ++ sch ++ act)
--                False
--                (xp `zimplies` (znot $ primed (variables m) xp) ) ) )
--        ,   ( (composite_label [_name m, evt_lbl, tr_en_lbl, pname])
--            , (ProofObligation 
--                (assert_ctx m `merge_ctx` dummy) 
--                (invariants p)
--                True
--                (exist_ind (xp `zimplies` (zall sch)))) ) 
--        ]
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
        exist_ind xp = if M.null ind 
                then xp 
                else zexists 
                    (map (rename "@param") $ elems ind) 
                    xp
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

make_unique :: String -> Map String Var -> Expr -> Expr
make_unique suf vs w@(Word (Var vn vt)) 
        | vn `member` vs    = Word (Var (vn ++ suf) vt)
        | otherwise         = w
make_unique _ _ c@(Const _ _ _)    = c
make_unique suf vs (FunApp f xs)     = FunApp f $ map (make_unique suf vs) xs
make_unique suf vs (Binder q d xp)   = Binder q d (make_unique suf (foldr M.delete vs (map name d)) xp)

rename suf (Var n t) = Var (n ++ suf) t

new_dummy = make_unique "@param"

primed :: Map String Var -> Expr -> Expr
primed vs e = make_unique "@prime" vs e
--primed vs w@(Word (Var vn vt)) 
--        | vn `member` vs    = Word (Var (vn ++ "@prime") vt)
--        | otherwise         = w
--primed _ c@(Const _ _ _)    = c
--primed vs (FunApp f xs)     = FunApp f $ map (primed vs) xs
--primed vs (Binder q d xp)   = Binder q d (primed (foldr M.delete vs (map name d)) xp)
--primed _ x@(Number _)       = x

verify_machine :: Machine -> IO (Int, Int)
verify_machine m = do
    (s,i,j) <- str_verify_machine m
    putStrLn s
    return (i,j)

steps_po :: Theory -> Calculation -> Either [Error] [ProofObligation]
steps_po th (Calc d _ e0 [] _) = return []
steps_po th (Calc d g e0 ((r0, e1, a0,_):es) li) = do
    expr <- with_li li $ mk_expr r0 e0 e1
    tail <- steps_po th (Calc d g e1 es li)
    return $ ProofObligation (d `merge_ctx` theory_ctx th) (a0 ++ elems (theory_facts th)) False expr : tail

entails_goal_po th (Calc d g e0 es (i,j)) = do
            a <- with_li (i,j) assume
            return $ ProofObligation (d `merge_ctx` theory_ctx th) (a ++ elems (theory_facts th)) False g
    where
        assume = 
                fmap reverse $ foldM f [] (map (\(x,y,z) -> (mk_expr x y z)) $ zip3 rs xs ys)
        f xs mx = do 
            x <- mx
            return (x:xs)
        ys = map (\(_,x,_,_) -> x) es
        xs = take (length es) (e0:ys)
        rs = map (\(x,_,_,_) -> x) es

goal_po c = ProofObligation (context c) xs False (goal c)
    where
        xs = concatMap (\(_,_,x,_) -> x) $ following c

obligations :: Theory -> Calculation -> Either [Error] [ProofObligation]
obligations th c = do
        x  <- entails_goal_po th c
        ys <- steps_po th c
        return (x:ys)

pretty_print :: StrList -> [String]
pretty_print (Str xs) = [xs]
pretty_print (List []) = ["()"]
pretty_print (List ys@(x:xs)) = 
        case x of
            Str y    -> map (uncurry (++)) $ zip
                (("(" ++ y ++ " "):repeat (margin (length y + 2)))
                (collapse (concatMap pretty_print xs ++ [")"]))
            List _ -> map (uncurry (++)) $ zip
                ("( ":repeat (margin 2))
                (collapse (concatMap pretty_print ys ++ [" )"]))
    where
        margin n = take n (repeat ' ')
        collapse xs = 
            case reverse xs of
                y0:y1:ys -> reverse ( (y1++y0):ys )

proof_po th (ByCalc c) lbl po = do
        let y = entailment (goal_po c) po
        ys   <- obligations th c
        let f x = composite_label [lbl,label x]
        let step_lbls = map (("step "++) . show) [1..]
        let lbls = map f ("goal" : "relation" : step_lbls)
        return $ zip lbls (y:ys)

check :: Theory -> Calculation -> IO (Either [Error] [(Validity, Int)])
check th c = embed 
            (obligations th c) 
            (\pos -> do
--        let txt = (do
--            p <- pos
--            ("\n; ------------\n(push)" : (do
--                c <- z3_code p
--                return $ show $ as_tree c) ++ ["\n(pop)"] ))
--        putStrLn $ unlines txt
        rs <- forM pos discharge :: IO [Validity]
        let ln = filter (\(x,y) -> x /= Valid) $ zip rs [0..] :: [(Validity, Int)]
        return ln)

match_proof :: Machine -> Label -> ProofObligation -> Proof -> IO (Bool, [String])
match_proof m lbl po
            (ByCalc p@(Calc _ _ _ steps li)) = do
        r0 <- check (theory m) p
        r1 <- entails (goal_po p) po
--        let !() = unsafePerformIO (do
--            putStrLn "> verification results"
--            print r0
--            putStrLn "> entailment result"
--            print r1)
        x <- case (r0,r1) of
            (Right [], Valid) -> 
                return (True, ["  o  " ++ show lbl])
            (r0,r1) -> do
                let xs = [" xxx " ++ show lbl]
                ys <- case r0 of
                    Right r0 -> do
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
                    Left (xs) -> return [format "     type error in proof: {0}" xs]
                zs <- case r1 of
                    Valid -> return []
                    x ->     return [
                            "     "
                        ++ "proof does not match proof obligation: " ++ show li]
                return (False, xs ++ ys ++ zs)
        return x

dump :: String -> Map Label ProofObligation -> IO ()
dump name pos = do
        withFile (name ++ ".z") WriteMode (\h -> do
            forM_ (toList pos) (\(lbl, po) -> do
                hPutStrLn h (format "(echo \"> {0}\")\n(push)" lbl)
                hPutStrLn h (unlines $ map f $ z3_code po)
                hPutStrLn h "(pop)"
                ) )
    where
        f x@(Assert _) = unlines $ pretty_print (as_tree x)
--            unlines (map (uncurry (++)) $ zip
--                ("(Assert ":repeat "          ")
--                $ pretty_print (as_tree x)) ++ ")"
        f x          = show $ as_tree x
                
str_verify_machine :: Machine -> IO (String, Int, Int)
str_verify_machine m = 
        case proof_obligation m of
            Right pos -> do
                dump (show $ _name m) pos
                rs <- forM (toList pos) (\(lbl, po) -> do
--                    if lbl `member` proofs ps then do
--                        match_proof m lbl po (proofs ps ! lbl)
--                    else do
                        r <- discharge po
                        x <- case r of
                            Valid -> do
                                return (True, ["  o  " ++ show lbl])
                            x     -> do
                                return (False, [" xxx " ++ show lbl])
                        return x)
                let total = length rs
                let passed = length $ filter fst rs
                let xs = "passed " ++ (show passed) ++ " / " ++ show total
                let ys = concatMap snd rs ++ [xs]
                return (unlines ys, passed, total)
            Left msgs -> return (unlines $ map f msgs,0,0)
    where
        ps = props m
        f (xs,i,j) = format "error ({0},{1}): {2}" i j xs :: String
        