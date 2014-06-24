{-# LANGUAGE ExistentialQuantification, DeriveDataTypeable #-}
module Logic.Proof.ProofTree where

    -- Modules
import Logic.Expr
import Logic.Operator
import Logic.Proof.Sequent

    -- Libraries
import Control.Monad

import Data.List as L
import Data.Map as M 
                ( Map )
import qualified Data.Map as M 
--import Data.Maybe
import Data.Set as S 
--import Data.String.Utils as SU
import Data.Typeable

import Utilities.Format
import Utilities.Syntactic

data Ignore = Ignore LineInfo
    deriving (Eq,Typeable)

data Prune = Prune Int Proof
    deriving (Eq,Typeable)

-- instance ProofRule Proof where
--     proof_po y (Proof x) z a = proof_po y x z a

data Proof =  FreeGoal String String Type Proof LineInfo
            | ByCases   [(Label, Expr, Proof)] LineInfo
            | Easy                             LineInfo
            | Assume (Map Label Expr) Expr Proof LineInfo
            | ByParts [(Expr,Proof)]           LineInfo
                -- Too complex
            | Assertion (Map Label (Expr,Proof)) [(Label,Label)] Proof LineInfo
            | InstantiateHyp Expr (Map Var Expr) Proof LineInfo
            | Keep Context [Expr] (Map Label Expr) Proof LineInfo
            | ByCalc Calculation
    deriving (Eq,Typeable)

data Calculation = Calc 
        {  context    :: Context
        ,  goal       :: Expr
        ,  first_step :: Expr
        ,  following  :: [(BinOperator, Expr, [Expr], LineInfo)]
        ,  l_info     :: LineInfo }
    deriving (Eq, Typeable)

data TheoremRef = ThmRef Label [(Var,Expr)]
    deriving (Eq,Show)

-- instance Eq Proof where
--     Proof x == Proof y = x `h_equal` y

class (Syntactic a, Typeable a, Eq a) => ProofRule a where
    proof_po :: a -> Label -> Sequent -> Either [Error] [(Label,Sequent)]

instance Show Proof where
    show _ = "[..]"

instance Syntactic Calculation where
    line_info c = l_info c

instance Syntactic Proof where
    -- line_info (Proof x) = line_info x
-- instance Syntactic ByCases where
    line_info (ByCases _ li)        = li
-- instance Syntactic Assume where
    line_info (Assume _ _ _ li)     = li
-- instance Syntactic ByParts where
    line_info (ByParts _ li)        = li
-- instance Syntactic Assertion where
    line_info (Assertion _ _ _ li)  = li
-- instance Syntactic Easy where
    line_info (Easy li)             = li
-- instance Syntactic FreeGoal where
    line_info (FreeGoal _ _ _ _ li)   = li
-- instance Syntactic Prune where
    -- line_info (Prune _ p) = line_info p
-- instance Syntactic Ignore where
    -- line_info (Ignore li) = li
-- instance Syntactic InstantiateHyp where
    line_info (InstantiateHyp _ _ _ li) = li
-- instance Syntactic Keep where
    line_info (Keep _ _ _ _ li) = li
    line_info (ByCalc c) = line_info c

instance ProofRule Proof where
    proof_po (ByCalc c) lbl po@(Sequent ctx _ _ _) = do
            let (y0,y1) = entailment (goal_po c) po
            ys   <- obligations' ctx po c
            return $ L.map f (  (with_li "goal ",y0) 
                              : (with_li "hypotheses ",y1)
                              : ys)
        where 
            f (x,y) = (composite_label [lbl, x],y)
            with_li x = label (x ++ show li)
            li  = line_info c

-- instance ProofRule ByCases where
    proof_po (ByCases xs li) lbl (Sequent ctx asm hyps goal) = do
            dis <- toErrors li $ mzsome (L.map (\(_,x,_) -> Right x) xs)
            let c  = completeness dis
            cs <- mapM case_a $ zip [1..] xs
            return (c : concat cs)
        where
            completeness dis = 
                    ( (f ("completeness " ++ show li)) 
                    , Sequent ctx asm hyps dis )
            case_a (n,(_,x,p)) = proof_po p (f ("case " ++ show n))
                    $ Sequent ctx (x:asm) hyps goal
            f x     = composite_label [lbl,label x]

-- instance ProofRule ByParts where
    proof_po (ByParts xs li) lbl (Sequent ctx asm hyps goal) = do
            let conj = L.map (\(x,_) -> x) xs
            let c  = completeness conj
            cs <- mapM part $ zip [1..] xs
            return (c : concat cs)
        where
            completeness conj = 
                    ( (f ("completeness " ++ show li)) 
                    , Sequent ctx conj hyps goal )
            part (n,(x,p)) = proof_po p (f ("part " ++ show n))
                    $ Sequent ctx asm hyps x
            f x     = composite_label [lbl,label x]

-- instance ProofRule FreeGoal where
    proof_po    (FreeGoal v u t p li) 
                lbl po@(Sequent ctx asm hyps goal) = do
            new_goal <- free_vars goal
            xs <- proof_po p lbl $ Sequent new_ctx asm hyps new_goal
            return xs
        where
            new_ctx = merge_ctx (Context M.empty (M.singleton u (Var u t)) M.empty M.empty M.empty)
                                ctx
            free_vars (Binder Forall ds r expr) 
                    | are_fresh [u] po = return $ zforall (L.filter ((v /=) . name) ds) 
                                                (rename v u r)
                                                (rename v u expr)
                    | otherwise        = Left $ [Error (format "variable '{0}' cannot be freed as '{1}'" v u) li]
            free_vars expr = return expr

-- instance ProofRule Easy where
    proof_po    (Easy (LI _ i j)) 
                lbl po = 
            return [(composite_label [lbl, label ("easy " ++ show (i,j))],po)]

-- instance ProofRule Assume where
    proof_po    (Assume new_asm new_goal p (LI _ i j))
                lbl (Sequent ctx asm hyps goal) = do
            pos <- proof_po p lbl $ Sequent ctx asm (new_asm `M.union` hyps) new_goal
            return ( ( composite_label [lbl, label ("new assumption " ++ show (i,j))]
                     , Sequent ctx [] M.empty (           zimplies (zall $ M.elems new_asm) new_goal 
                                               `zimplies` goal) )
                   : pos)

-- instance ProofRule Assertion where
    proof_po    (Assertion lemma dep p _)
                lbl (Sequent ctx asm hyps goal) = do
            let depend = M.map M.fromList $ M.fromListWith (++) $ L.map f dep
                f (x,y) = (x,[(y,())])
            pos1 <- proof_po p ( composite_label [lbl,label "main goal"] )
                $ Sequent ctx (asm ++ L.map fst (M.elems lemma)) hyps goal
            pos2 <- forM (M.toList lemma) (\(lbl2,(g,p)) -> do
                let used = maybe M.empty id $ lbl2 `M.lookup` depend
                    thm  = (M.map fst lemma) `M.intersection` used
                proof_po p (composite_label [lbl,label "assertion",lbl2]) 
                    $ Sequent ctx asm (thm `M.union` hyps) g )
            return (pos1 ++ concat pos2)

--instance ProofRule Prune where
--    proof_po th (Prune n p) lbl (Sequent ctx asm goal) = 
--            proof_po th p lbl (Sequent ctx (drop (length asm - n) asm) goal)

-- instance ProofRule Ignore where
--     proof_po _ _ _ _ = Right []

-- instance ProofRule InstantiateHyp where
    proof_po    (InstantiateHyp hyp ps proof li) 
                lbl (Sequent ctx asm hyps goal) = do
        if hyp `elem` M.elems hyps || hyp `elem` asm then do
            newh <- case hyp of
                Binder Forall vs r t 
                    | all (`elem` vs) (M.keys ps) -> do
                        let new_vs = L.foldl (flip L.delete) vs (M.keys ps)
                            ps'    = M.mapKeys name ps
                            re     = substitute ps' r
                            te     = substitute ps' t
                        if L.null new_vs
                            then return $ zimplies re te
                            else return $ zforall new_vs re te
                _ -> Left [Error ("hypothesis is not a universal quantification:\n" 
                        ++ pretty_print' hyp) li]
            proof_po proof lbl (Sequent ctx (newh:asm) hyps goal)
        else
            Left [Error ("formula is not an hypothesis:\n" 
                ++ pretty_print' hyp) li]
-- instance ProofRule Keep where
    proof_po    (Keep ctx unnamed named proof _) 
                lbl (Sequent _ _ _ goal) = do
        proof_po proof lbl (Sequent ctx unnamed named goal)

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
goal_po c = Sequent (context c) xs M.empty (goal c)
    where
        xs = concatMap (\(_,_,x,_) -> x) $ following c

obligations :: Context -> Sequent -> Calculation -> Either [Error] [Sequent]
obligations ctx s c = do
        fmap (L.map snd) $ obligations' ctx s c

obligations' :: Context -> Sequent -> Calculation -> Either [Error] [(Label, Sequent)]
obligations' ctx s c = do
        x  <- entails_goal_po ctx c
        ys <- steps_po ctx s c
        return ((label ("relation " ++ show (l_info c)),x):ys)

--proof_po :: Theory -> Proof -> Label -> Sequent -> Either [Error] [(Label,Sequent)]

are_fresh :: [String] -> Sequent -> Bool
are_fresh vs (Sequent _ asm hyps goal) = 
            S.fromList vs `S.intersection` (
                S.map name $ 
                S.unions $ 
                L.map used_var (goal : asm ++ M.elems hyps)
                )
         == S.empty 

rename_all :: [(Var,Var)] -> Expr -> Expr
rename_all [] e = e
rename_all vs e@(Word v) = maybe e Word $ L.lookup v vs
rename_all vs (Binder q ds r xp) = Binder q ds (rename_all us r) (rename_all us xp)
    where
        us = L.filter (\(x,_) -> not $ x `elem` ds) vs
rename_all vs e = rewrite (rename_all vs) e 

steps_po :: Context -> Sequent -> Calculation -> Either [Error] [(Label, Sequent)]
steps_po ctx s (Calc d _ e0 es _) = f e0 es
    where
        f _ [] = return []
        f e0 ((r0, e1, a0,li):es) = do
                expr <- with_li li $ mk_expr r0 e0 e1
                tail <- f e1 es
                let (Sequent _ asm _ _) = s
                return (
                    ( label ("step " ++ show li)
                    , Sequent 
                        (ctx `merge_ctx` d) 
                        (a0 ++ asm) 
                        M.empty
                        expr
                    ) : tail)

entails_goal_po :: Context 
                -> Calculation -> Either [Error] Sequent
entails_goal_po ctx (Calc d g e0 es li) = do
            a <- with_li li assume
            return $ Sequent 
                ( ctx   `merge_ctx` 
                  d)
                a 
--                (a ++ (M.elems $ theory_facts ts th))
                M.empty 
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
