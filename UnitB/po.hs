{-# LANGUAGE BangPatterns #-}
module UnitB.PO 
    ( proof_obligation, step_ctx, evt_live_ctx
    , evt_saf_ctx, invariants, assert_ctx
    , str_verify_machine, raw_machine_pos
    , check, verify_changes, verify_machine
    , smoke_test_machine, dump )
where

    -- Modules
import UnitB.AST
import UnitB.Calculation
import UnitB.Operator
import UnitB.Label
import UnitB.Feasibility

import Z3.Z3

    -- Libraries
import Control.Monad hiding (guard)

import           Data.Map as M hiding 
                    ( map, foldl, foldr
                    , delete, filter, null
                    , (\\))
import qualified Data.Map as M
import           Data.Maybe ( maybeToList )
import           Data.List as L hiding (inits, union,insert)
import           Data.Set as S hiding (map,filter,foldr,(\\))
import qualified Data.Set as S (map)

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
--ref_mono_lbl      = label "REF/monotonicity"
--ref_impl_lbl      = label "REF/implication"
--ref_ind_lbl       = label "REF/induction"
--ref_disj_lbl      = label "REF/disjunction"
--ref_psp_lbl       = label "REF/PSP"
--ref_trade_lbl     = label "REF/trading"
--ref_trans_lbl     = label "REF/transitivity"
--ref_discharge_lbl = label "REF/discharge"

theory_ctx :: Theory -> Context
theory_ctx (Theory d ts f c _ dums) = 
    merge_all_ctx 
        (Context ts c f M.empty dums : map theory_ctx d)

theory_facts :: Theory -> Map Label Expr
theory_facts (Theory d _ _ _ f _) = 
    merge_all (f : map theory_facts d)

assert_ctx :: Machine -> Context
assert_ctx m = merge_ctx
          (Context M.empty (variables m) M.empty M.empty M.empty)
          (theory_ctx $ theory m)
step_ctx :: Machine -> Context
step_ctx m = merge_all_ctx 
        [  Context M.empty (prime_all $ variables m) M.empty M.empty M.empty
        ,  Context M.empty (variables m) M.empty M.empty M.empty
        , (theory_ctx $ theory m) ]
    where
        prime_all vs = mapKeys (++ "'") $ M.map prime_var vs
        prime_var (Var n t) = (Var (n ++ "@prime") t)

evt_saf_ctx :: Event -> Context
evt_saf_ctx evt  = Context M.empty (params evt) M.empty M.empty M.empty

evt_live_ctx :: Event -> Context
evt_live_ctx evt = Context M.empty (indices evt) M.empty M.empty M.empty

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
        f (Sequent a b d) = Sequent a (M.elems (theory_facts $ theory m)++b) d

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

ref_po :: Machine -> Label -> Rule -> Map Label Sequent
ref_po m lbl (Rule r) = mapKeys f $ refinement_po r m
    where
        f x
            | show x == "" = composite_label [label $ name m, lbl,label "REF",rule_name r]
            | otherwise    = composite_label [label $ name m, lbl,label "REF",rule_name r,x]

init_fis_po :: Machine -> Map Label Sequent
init_fis_po m = M.fromList $ flip map clauses $ \(vs,es) -> 
            ( composite_label $ [_name m, init_fis_lbl] ++ map (label . name) vs
            , po $ goal vs es)
    where
        po = Sequent (assert_ctx m) []
        clauses = partition_expr (M.elems $ variables m) (M.elems $ inits m)
        goal vs es = (zexists vs ztrue $ zall es)
 

prop_tr :: Machine -> Label -> Transient -> Map Label Sequent
prop_tr m pname (Transient fv xp evt_lbl n hint lt_fine) = 
    M.fromList 
        $ if M.null ind0 then 
            [ po [label "EN"] xp0
            , po [label "NEG"] xp1
            ] ++ map (uncurry po) xps
          else
            [ po [] $ exist_ind $ zall $ xp0:xp1:map snd xps ]
    where
--        thm  = inv_thm p
        grd  = M.elems $ guard evt
        schedules = list_schedules evt ! n
        sch0 = M.elems $ fst schedules
        sch1 = map snd $ maybeToList $ snd schedules
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
        xps = case (lt_fine, snd schedules) of
                (Just lbl, Just (_,fsch)) ->
                    let (LeadsTo vs p q) = (progress (props m) `M.union` progress (inh_props m)) ! lbl in
                        [ ([label "EN/leadsto/lhs"],zforall vs ztrue $ zall sch0 `zimplies` p)
                        , ([label "EN/leadsto/rhs"],zforall vs ztrue $ q `zimplies` fsch) 
                        ]
                (Nothing,Nothing) -> []
                _                 -> error $ format (
                           "transient predicate {0}'s side condition doesn't "
                        ++ "match the fine schedule of event {1}"
                        )
                    pname evt_lbl


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
                    (step_ctx $ m) 
                    (invariants m ++ grd ++ act)
                    (forall_fv xp) )
            where
                grd = M.elems $ guard evt
                act = M.elems $ action evt
                forall_fv xp = if L.null fv then xp else zforall fv ztrue xp
        po_name evt_lbl = composite_label [_name m, evt_lbl, co_lbl, pname]

inv_po m pname xp = 
        M.union 
            (mapKeys po_name $ mapWithKey po (events m))
            (M.singleton 
                (composite_label [_name m, inv_init_lbl, pname])
                (Sequent (assert_ctx m) (M.elems $ inits m) xp))
    where
        po _ evt = 
                (Sequent 
                    (step_ctx m `merge_ctx` Context M.empty ind M.empty M.empty M.empty) 
                    (invariants m ++ grd ++ act)
                    (primed (variables m) xp))
            where
                grd = M.elems $ guard evt
                act = M.elems $ action evt
                ind = indices evt `merge` params evt
        po_name evt_lbl = composite_label [_name m, evt_lbl, inv_lbl, pname]

fis_po m lbl evt = M.fromList $ flip map pos $ \(pvar, acts) ->
        ( composite_label $ [_name m, lbl, fis_lbl] ++ map (label . name) pvar,
          Sequent 
            (assert_ctx m `merge_ctx` Context M.empty ind M.empty M.empty M.empty)
            (invariants m ++ grd)
            (zexists pvar ztrue $ zall acts))
    where
        grd  = M.elems $ guard evt
--        act  = zall $ M.elems $ action evt
        pvar = map prime $ M.elems $ variables m
        ind  = indices evt `merge` params evt
        pos  = partition_expr pvar $ M.elems $ action evt

sch_po :: Machine -> Label -> Event -> Map Label Sequent
sch_po m lbl evt = M.singleton
        (composite_label [_name m, lbl, sch_lbl])
        (Sequent 
            (           assert_ctx m 
            `merge_ctx` evt_live_ctx evt
            `merge_ctx` Context M.empty ind M.empty M.empty M.empty)
            (invariants m ++ f_sch ++ c_sch)
            (exist_param $ zall grd))
    where
        grd   = M.elems $ guard evt
        c_sch = M.elems $ fst $ last_schedule evt
        f_sch = map snd $ maybeToList $ snd $ last_schedule evt
        param = params evt
        ind   = indices evt `merge` params evt
        exist_param xp = zexists (M.elems param) ztrue xp

thm_po m lbl xp = M.singleton
        (composite_label [_name m, lbl, thm_lbl])
        (Sequent
            (assert_ctx m)
            (invariants_only m)
            xp)
    where

add_suffix suf (Var n t) = Var (n ++ suf) t

new_dummy = make_unique "@param"

verify_machine :: Machine -> IO (Int, Int)
verify_machine m = do
    (s,i,j) <- str_verify_machine m
    putStrLn s
    return (i,j)

steps_po :: Theory -> Context -> Calculation -> Either [Error] [(Label, Sequent)]
steps_po th ctx (Calc d _ e0 es _) = f e0 es
    where
        f _ [] = return []
        f e0 ((r0, e1, a0,li):es) = do
            expr <- with_li li $ mk_expr r0 e0 e1
            tail <- f e1 es
            return (
                ( label ("step " ++ show li)
                , Sequent 
                    (ctx `merge_ctx` d `merge_ctx` theory_ctx th) 
                    (a0 ++ M.elems (theory_facts th)) 
                    expr
                ) : tail)

entails_goal_po th ctx (Calc d g e0 es li) = do
            a <- with_li li assume
            return $ Sequent 
                (ctx `merge_ctx` d `merge_ctx` theory_ctx th) 
                (a ++ M.elems (theory_facts th)) 
                g
    where
        assume = 
                fmap reverse $ foldM f [] (map (\(x,y,z) -> (mk_expr x y z)) $ zip3 rs xs ys)
        f xs mx = do 
            x <- mx
            return (x:xs)
        ys = map (\(_,x,_,_) -> x) es
        xs = take (length es) (e0:ys)
        rs = map (\(x,_,_,_) -> x) es

goal_po c = Sequent (context c) xs (goal c)
    where
        xs = concatMap (\(_,_,x,_) -> x) $ following c

obligations :: Theory -> Context -> Calculation -> Either [Error] [Sequent]
obligations th ctx c = do
        fmap (map snd) $ obligations' th ctx c

obligations' :: Theory -> Context -> Calculation -> Either [Error] [(Label, Sequent)]
obligations' th ctx c = do
        x  <- entails_goal_po th ctx c
        ys <- steps_po th ctx c
        return ((label ("relation " ++ show (l_info c)),x):ys)


pretty_print :: StrList -> [String]
pretty_print (Str xs) = [xs]
pretty_print (List []) = ["()"]
pretty_print (List ys@(x:xs)) = 
        case x of
            Str y    -> 
                if length one_line <= 50
                then ["(" ++ y ++ one_line ++ ")"]
                else map (uncurry (++)) $ zip
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
                _        -> xs
        one_line = concatMap (uncurry (++)) $ zip (repeat " ") $ concatMap pretty_print xs

proof_po th p@(ByCalc c) lbl po@(Sequent ctx _ _) = do
        let (y0,y1) = entailment (goal_po c) po
        ys   <- obligations' th ctx c
        return $ map f ((g "goal ",y0) : (g "hypotheses ",y1) : ys)
    where 
        f (x,y) = (composite_label [lbl, x],y)
        g x = label (x ++ show li)
        li  = line_info p
proof_po th (ByCases xs li) lbl (Sequent ctx asm goal) = do
        dis <- mzsome (map (\(_,x,_) -> Right x) xs)
        let c  = completeness dis
        cs <- mapM case_a $ zip [1..] xs
        return (c : concat cs)
    where
        completeness dis = 
                ( (f ("completeness " ++ show li)) 
                , Sequent ctx asm dis )
        case_a (n,(_,x,p)) = proof_po th p (f ("case " ++ show n))
                $ Sequent ctx (x:asm) goal
        f x     = composite_label [lbl,label x]
proof_po th (ByParts xs li) lbl (Sequent ctx asm goal) = do
        let conj = map (\(x,_) -> x) xs
        let c  = completeness conj
        cs <- mapM part $ zip [1..] xs
        return (c : concat cs)
    where
        completeness conj = 
                ( (f ("completeness " ++ show li)) 
                , Sequent ctx conj goal )
        part (n,(x,p)) = proof_po th p (f ("part " ++ show n))
                $ Sequent ctx asm x
        f x     = composite_label [lbl,label x]
proof_po    th  (FreeGoal v u p li) 
            lbl po@(Sequent ctx asm goal) = do
        new_goal <- free_vars goal
        proof_po th p lbl $ Sequent ctx asm new_goal
    where
        free_vars (Binder Forall ds r expr) 
                | are_fresh [u] po = return (zforall (L.filter ((v /=) . name) ds) 
                                            (rename v u r)
                                            $ rename v u expr)
                | otherwise          = Left $ [Error (format "variable can't be freed: {0}" u) li]
            where
        free_vars expr = return expr
--        step_lbls = map (("case "++) . show) [1..]
--        lbls      = map f ("completeness" : step_lbls)
--        f x       = composite_label [lbl,label x]
--        g x       = name x /= v
proof_po    _  (Easy (LI _ i j)) 
            lbl po = 
        return [(composite_label [lbl, label ("easy " ++ show (i,j))],po)]
proof_po    th  (Assume new_asm new_goal p (LI _ i j))
            lbl (Sequent ctx asm goal) = do
        pos <- proof_po th p lbl $ Sequent ctx (M.elems new_asm ++ asm) new_goal
        return ( ( composite_label [lbl, label ("new assumption " ++ show (i,j))]
                 , Sequent ctx [] (zimplies (zall $ M.elems new_asm) new_goal `zimplies` goal) )
               : pos)
proof_po    th  (Assertion lemma p _)
            lbl (Sequent ctx asm goal) = do
        pos1 <- proof_po th p ( composite_label [lbl,label "main goal"] )
            $ Sequent ctx (asm ++ map fst (M.elems lemma)) goal
        pos2 <- forM (M.toList lemma) (\(lbl2,(g,p)) ->
            proof_po th p (composite_label [lbl,label "assertion",lbl2]) 
                $ Sequent ctx asm g )
        return (pos1 ++ concat pos2)

are_fresh :: [String] -> Sequent -> Bool
are_fresh vs (Sequent _ asm goal) = 
            S.fromList vs `S.intersection` (S.map name $ S.unions $ map used_var (goal:asm))
         == S.empty 


rename :: String -> String -> Expr -> Expr
rename x y e@(Word (Var vn t))
        | vn == x   = Word (Var y t)
        | otherwise = e
rename x y e@(Binder q vs r xp)
        | x `elem` map name vs  = e
        | otherwise             = Binder q vs (rename x y r) $ rename x y xp
rename x y e = rewrite (rename x y) e 

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
        f x = unlines $ pretty_print (as_tree x)

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