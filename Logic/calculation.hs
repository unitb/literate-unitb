{-# LANGUAGE ExistentialQuantification, DeriveDataTypeable #-}
module Logic.Calculation where

    -- Modules
import Logic.Classes
import Logic.Const
import Logic.Expr
import Logic.Genericity
import Logic.Operator
import Logic.Label
import Logic.Sequent

import Theories.Theory

    -- Libraries
import Control.Monad

import Data.List as L
import Data.Map as M (Map, lookup, fromList, elems, toList, empty, singleton, mapKeys)
import Data.Maybe
import Data.Set as S 
import Data.String.Utils as SU
import Data.Typeable

import Utilities.Format
import Utilities.Syntactic
import Utilities.HeterogenousEquality

embed :: Either a b -> (b -> IO c) -> IO (Either a c)
embed em f = do
        case em of
            Right x -> do
                y <- f x
                return (Right y)
            Left x  -> 
                return (Left x)

data Calculation = Calc 
        {  context    :: Context
        ,  goal       :: Expr
        ,  first_step :: Expr
        ,  following  :: [(BinOperator, Expr, [Expr], LineInfo)]
        ,  l_info     :: LineInfo }
    deriving (Eq, Typeable)

data Proof = forall a. ProofRule a => Proof a
    deriving Typeable

instance Eq Proof where
    Proof x == Proof y = x `h_equal` y

data Ignore = Ignore LineInfo
    deriving (Eq,Typeable)

data Prune = Prune Int Proof
    deriving (Eq,Typeable)

data FreeGoal   = FreeGoal String String Type Proof LineInfo
    deriving (Eq,Typeable)

data ByCases    = ByCases   [(Label, Expr, Proof)] LineInfo
    deriving (Eq,Typeable)

data Easy       = Easy                             LineInfo
    deriving (Eq,Typeable)
data Assume     = Assume (Map Label Expr) Expr Proof LineInfo
    deriving (Eq,Typeable)
data ByParts    = ByParts [(Expr,Proof)]           LineInfo
    deriving (Eq,Typeable)
data Assertion  = Assertion (Map Label (Expr,Proof)) Proof LineInfo
    deriving (Eq,Typeable)

class (Syntactic a, Typeable a, Eq a) => ProofRule a where
    proof_po :: Theory -> a -> Label -> Sequent -> Either [Error] [(Label,Sequent)]

instance ProofRule Proof where
    proof_po y (Proof x) z a = proof_po y x z a

instance Syntactic Calculation where
    line_info c = l_info c

instance Syntactic Proof where
    line_info (Proof x) = line_info x

instance Syntactic ByCases where
    line_info (ByCases _ li)        = li

instance Syntactic Assume where
    line_info (Assume _ _ _ li)     = li

instance Syntactic ByParts where
    line_info (ByParts _ li)        = li

instance Syntactic Assertion where
    line_info (Assertion _ _ li)    = li

instance Syntactic Easy where
    line_info (Easy li)             = li

instance Syntactic FreeGoal where
    line_info (FreeGoal _ _ _ _ li)   = li

instance Syntactic Prune where
    line_info (Prune _ p) = line_info p

instance Syntactic Ignore where
    line_info (Ignore li) = li

instance ProofRule Calculation where
    proof_po th c lbl po@(Sequent ctx _ _) = do
            let (y0,y1) = entailment (goal_po c) po
            ys   <- obligations' th ctx c
            return $ L.map f ((g "goal ",y0) : (g "hypotheses ",y1) : ys)
        where 
            f (x,y) = (composite_label [lbl, x],y)
            g x = label (x ++ show li)
            li  = line_info c

instance ProofRule ByCases where
    proof_po th (ByCases xs li) lbl (Sequent ctx asm goal) = do
            dis <- toErrors li $ mzsome (L.map (\(_,x,_) -> Right x) xs)
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

instance ProofRule ByParts where
    proof_po th (ByParts xs li) lbl (Sequent ctx asm goal) = do
            let conj = L.map (\(x,_) -> x) xs
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

instance ProofRule FreeGoal where
    proof_po    th  (FreeGoal v u t p li) 
                lbl po@(Sequent ctx asm goal) = do
            new_goal <- free_vars goal
            proof_po th p lbl $ Sequent new_ctx asm new_goal
        where
            new_ctx = merge_ctx (Context M.empty (M.singleton u (Var u t)) M.empty M.empty M.empty)
                                ctx
            free_vars (Binder Forall ds r expr) 
                    | are_fresh [u] po = return $ zforall (L.filter ((v /=) . name) ds) 
                                                (rename v u r)
                                                (rename v u expr)
                    | otherwise        = Left $ [Error (format "variable can't be freed: {0}" u) li]
                where
            free_vars expr = return expr
    --        step_lbls = map (("case "++) . show) [1..]
    --        lbls      = map f ("completeness" : step_lbls)
    --        f x       = composite_label [lbl,label x]
    --        g x       = name x /= v

instance ProofRule Easy where
    proof_po    _  (Easy (LI _ i j)) 
                lbl po = 
            return [(composite_label [lbl, label ("easy " ++ show (i,j))],po)]

instance ProofRule Assume where
    proof_po    th  (Assume new_asm new_goal p (LI _ i j))
                lbl (Sequent ctx asm goal) = do
            pos <- proof_po th p lbl $ Sequent ctx (M.elems new_asm ++ asm) new_goal
            return ( ( composite_label [lbl, label ("new assumption " ++ show (i,j))]
                     , Sequent ctx [] (zimplies (zall $ M.elems new_asm) new_goal `zimplies` goal) )
                   : pos)

instance ProofRule Assertion where
    proof_po    th  (Assertion lemma p _)
                lbl (Sequent ctx asm goal) = do
            pos1 <- proof_po th p ( composite_label [lbl,label "main goal"] )
                $ Sequent ctx (asm ++ L.map fst (M.elems lemma)) goal
            pos2 <- forM (M.toList lemma) (\(lbl2,(g,p)) ->
                proof_po th p (composite_label [lbl,label "assertion",lbl2]) 
                    $ Sequent ctx asm g )
            return (pos1 ++ concat pos2)

instance ProofRule Prune where
    proof_po th (Prune n p) lbl (Sequent ctx asm goal) = 
            proof_po th p lbl (Sequent ctx (drop (length asm - n) asm) goal)

instance ProofRule Ignore where
    proof_po _ _ _ _ = Right []

chain :: Notation -> BinOperator -> BinOperator -> Either String BinOperator
chain n x y 
    | x == equal = Right y
    | y == equal = Right x
    | otherwise  = case M.lookup (x,y) $ M.fromList (chaining n) of
                    Just z -> Right z
                    Nothing -> Left $ format "chain: operators {0} and {1} don't chain" x y


infer_goal :: Calculation -> Notation -> Either String Expr
infer_goal (Calc _ _ s0 xs _) n = do
        op <- mk_expr `fmap` foldM (chain n) equal (L.map g xs)
        case reverse $ L.map f xs of
            x:_ -> either 
                        (\x -> Left (x)) --,i,j)) 
                        Right 
                        (s0 `op` x)
            []   -> Left ("a calculation must include at least one reasoning step") --,i,j)
    where
--        op = mk_expr $ foldl chain equal $ map g xs
        f (_,y,_,_) = y
        g (x,_,_,_) = x

show_proof :: Calculation -> String
show_proof (Calc _ g fs ss _) = 
        unlines ( [
                show g,
                "----",
                "    " ++ show fs ]
            ++  concatMap f ss )
    where
        f (_, s, h, _) = (
                   (L.map ("      | " ++) $ L.map show h)
                ++ [ "    " ++ show s ] )

goal_po :: Calculation -> Sequent
goal_po c = Sequent (context c) xs (goal c)
    where
        xs = concatMap (\(_,_,x,_) -> x) $ following c

obligations :: Theory -> Context -> Calculation -> Either [Error] [Sequent]
obligations th ctx c = do
        fmap (L.map snd) $ obligations' th ctx c

obligations' :: Theory -> Context -> Calculation -> Either [Error] [(Label, Sequent)]
obligations' th ctx c = do
        x  <- entails_goal_po th ctx c
        ys <- steps_po th ctx c
        return ((label ("relation " ++ show (l_info c)),x):ys)

--proof_po :: Theory -> Proof -> Label -> Sequent -> Either [Error] [(Label,Sequent)]

are_fresh :: [String] -> Sequent -> Bool
are_fresh vs (Sequent _ asm goal) = 
            S.fromList vs `S.intersection` (S.map name $ S.unions $ L.map used_var (goal:asm))
         == S.empty 


rename :: String -> String -> Expr -> Expr
rename x y e@(Word (Var vn t))
        | vn == x   = Word (Var y t)
        | otherwise = e
rename x y e@(Binder q vs r xp)
        | x `elem` L.map name vs  = e
        | otherwise             = Binder q vs (rename x y r) $ rename x y xp
rename x y e = rewrite (rename x y) e 

steps_po :: Theory -> Context -> Calculation -> Either [Error] [(Label, Sequent)]
steps_po th ctx (Calc d _ e0 es _) = f e0 es
    where
        f _ [] = return []
        f e0 ((r0, e1, a0,li):es) = do
                expr <- with_li li $ mk_expr r0 e0 e1
                let ts = S.unions $ L.map used_types $ expr : a0
                tail <- f e1 es
                return (
                    ( label ("step " ++ show li)
                    , Sequent 
                        (ctx `merge_ctx` d `merge_ctx` theory_ctx ts th) 
                        (a0 ++ M.elems (theory_facts ts th)) 
                        expr
                    ) : tail)

entails_goal_po :: Theory -> Context 
                -> Calculation -> Either [Error] Sequent
entails_goal_po th ctx (Calc d g e0 es li) = do
            a <- with_li li assume
            let ts = S.unions $ L.map used_types $ g : a
            return $ Sequent 
                (ctx `merge_ctx` d `merge_ctx` theory_ctx ts th) 
                (a ++ M.elems (theory_facts ts th)) 
                g
    where
        assume = 
                fmap reverse $ foldM f [] (L.map (\(x,y,z) -> (mk_expr x y z)) $ zip3 rs xs ys)
        f xs mx = do 
            x <- mx
            return (x:xs)
        ys = L.map(\(_,x,_,_) -> x) es
        xs = take (length es) (e0:ys)
        rs = L.map(\(x,_,_,_) -> x) es

theory_ctx :: Set Type -> Theory -> Context
theory_ctx used_ts th = 
        merge_all_ctx $
            (Context ts c new_fun M.empty dums) : L.map (theory_ctx ref_ts) (M.elems d)
    where
        d      = extends th
        tparam = gen_param th
        ts     = types th
        fun    = funs th
        c      = consts th
        dums   = dummies th
        
        new_fun = case tparam of
            Just t -> M.fromList $ do
                m' <- mapMaybe (unify t) $ S.elems used_ts
                let m = mapKeys (reverse . drop 2 . reverse) m'
                (tag,f)   <- M.toList fun
                let new_f = instantiate m f
                return (tag ++ concatMap z3_decoration (M.elems m), new_f)
            Nothing -> fun
        ref_ts = S.unions $ used_ts : L.map used_types fm
        fm = M.elems $ theory_facts used_ts th

    -- todo: prefix name of theorems of a z3_decoration
theory_facts :: Set Type -> Theory -> Map Label Expr
theory_facts ts th = 
        merge_all (new_fact : L.map (theory_facts ref_ts) (M.elems d))
    where
        d      = extends th
        tparam = gen_param th
        facts  = fact th

        new_fact = case tparam of
            Just t -> M.fromList $ do
                m' <- mapMaybe (unify t) $ S.elems ts
                let m = mapKeys (reverse . drop 2 . reverse) m'
                (tag, f) <- M.toList facts
                let (name,nb) = case SU.split "@@" $ show tag of
                                    [name,nb] -> (name,nb)
                                    xs -> error $ "theory_fact: " ++ show xs
                let new_f = substitute_type_vars m f
--                return (name, new_f)
                return (label $ name ++ concatMap z3_decoration (M.elems m) ++ nb, 
                     new_f)
            Nothing -> facts
        ref_ts = S.unions $ ts : L.map used_types fm
        fm = M.elems new_fact

used_types :: Expr -> Set Type
used_types e = visit (flip $ S.union . used_types) (
        case e of
            Binder _ vs e0 e1 -> S.fromList $ type_of e0 : type_of e1 : L.map f vs
            _ -> S.singleton $ type_of e
            ) e
    where
        f (Var _ t) = t
