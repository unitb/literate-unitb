{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE OverloadedStrings          #-}
module Logic.Proof.ProofTree where

    -- Modules
import Logic.Expr
import Logic.Operator
import Logic.Proof.Sequent

    -- Libraries
import Control.Arrow
import Control.DeepSeq
import Control.Monad
import Control.Lens hiding (Context,rewrite)

import Data.List as L
import Data.Maybe as M 
import qualified Data.Map.Class as M 
import Data.Serialize hiding (label)
import Data.Set as S 
import Data.Typeable

import GHC.Generics (Generic)

import Test.QuickCheck.ZoomEq

import Text.Printf.TH

import Utilities.Syntactic
import Utilities.Table

data Ignore = Ignore LineInfo
    deriving (Eq,Typeable)

data Prune = Prune Int Proof
    deriving (Eq,Typeable)

type Proof = ProofBase Expr

data ProofBase expr =  FreeGoal Name Name Type (ProofBase expr) LineInfo
            | ByCases   [(Label, expr, (ProofBase expr))] LineInfo
            | Easy                             LineInfo
            | Assume (Table Label expr) expr (ProofBase expr) LineInfo
            | ByParts [(expr,(ProofBase expr))]           LineInfo
                -- Too complex
            | Assertion (Table Label (expr,(ProofBase expr))) [(Label,Label)] (ProofBase expr) LineInfo
            | Definition (Table Var expr) (ProofBase expr) LineInfo
            | InstantiateHyp expr (Table Var expr) (ProofBase expr) LineInfo
            | Keep Context [expr] (Table Label expr) (ProofBase expr) LineInfo
            | ByCalc (CalculationBase expr)
    deriving (Eq,Typeable, Generic, Show,Functor,Foldable,Traversable)

type Calculation = CalculationBase Expr

data CalculationBase expr = Calc 
        {  _calculationBaseContext :: Context
        ,  _calculationBaseGoal    :: expr
        ,  first_step :: expr
        ,  following  :: [(BinOperator, expr, [expr], LineInfo)]
        ,  l_info     :: LineInfo }
    deriving (Eq,Typeable,Generic,Show,Functor,Foldable,Traversable)

makeFields ''CalculationBase

data TheoremRef = 
        ThmRef Label [(Var,Expr)]
    deriving (Eq,Show)

-- instance Eq Proof where
--     Proof x == Proof y = x `h_equal` y

class (Syntactic a, Typeable a, Eq a) => ProofRule a where
    proof_po :: a -> Label -> Sequent -> Either [Error] [(Label,Sequent)]

instance ZoomEq expr => ZoomEq (CalculationBase expr) where

instance Syntactic (CalculationBase expr) where
    line_info c = l_info c
    after = line_info
    traverseLineInfo f c = tr <$> f (l_info c) <*> (traverse._4) f (following c)
        where
            tr x y = c { l_info = x, following = y }

instance ZoomEq expr => ZoomEq (ProofBase expr) where

instance Syntactic (ProofBase expr) where
    line_info (ByCases _ li)        = li
    line_info (Assume _ _ _ li)     = li
    line_info (ByParts _ li)        = li
    line_info (Definition _ _ li)   = li
    line_info (Assertion _ _ _ li)  = li
    line_info (Easy li)             = li
    line_info (FreeGoal _ _ _ _ li) = li
    line_info (InstantiateHyp _ _ _ li) = li
    line_info (Keep _ _ _ _ li) = li
    line_info (ByCalc c) = line_info c
    after = line_info
    traverseLineInfo f (ByCalc c) = ByCalc <$> traverseLineInfo f c
    traverseLineInfo f (Easy li)  = Easy <$> f li
    traverseLineInfo f (ByCases xs li)  = ByCases <$> (traverse._3.traverseLineInfo) f xs 
                                                  <*> f li
    traverseLineInfo f (ByParts xs li)  = ByParts <$> (traverse._2.traverseLineInfo) f xs 
                                                  <*> f li
    traverseLineInfo f (Definition xs p li) = Definition xs <$> traverseLineInfo f p
                                                            <*> f li
    traverseLineInfo f (Assume xs x p li)   = Assume xs x <$> traverseLineInfo f p 
                                                          <*> f li
    traverseLineInfo f (Assertion xs x p li) = Assertion xs x <$> traverseLineInfo f p 
                                                              <*> f li
    traverseLineInfo f (FreeGoal x y t p li) = FreeGoal x y t <$> traverseLineInfo f p
                                                              <*> f li
    traverseLineInfo f (InstantiateHyp c xs p li) = InstantiateHyp c xs <$> traverseLineInfo f p
                                                                        <*> f li
    traverseLineInfo f (Keep c xs m p li) = Keep c xs m <$> traverseLineInfo f p 
                                                        <*> f li

instance (Eq expr,IsExpr expr) => ProofRule (ProofBase expr) where
    proof_po (ByCalc c) lbl po = do
            let ctx = po^.context
                (y0,y1) = entailment (goal_po c) po
            ys   <- obligations' ctx po c
            return $ L.map f (  ("goal",y0) 
                              : ("hypotheses",y1)
                              : ys)
        where 
            f (x,y) = (composite_label [lbl, x],y)

    proof_po (ByCases xs li) lbl po = do
            dis <- toErrors li $ mzsome (L.map (\(_,x,_) -> Right x) xs)
            let c  = completeness dis
            cs <- zipWithM case_a [1..] xs
            return (c : concat cs)
        where
            completeness dis = 
                    ( (f "completeness") 
                    , po & goal .~ dis )
            case_a n (_,x,p) = proof_po p (f ("case " ++ show n))
                    $ po & nameless %~ (x:)
            f x     = composite_label [lbl,label x]

    proof_po (ByParts xs _) lbl po = do
            let conj = L.map (\(x,_) -> x) xs
                c  = completeness conj
            cs <- zipWithM part [1..] xs
            return (c : concat cs)
        where
            completeness conj = 
                    ( (f "completeness") 
                    , po & nameless .~ conj )
            part n (x,p) = proof_po p (f ("part " ++ show n))
                    $ po & goal .~ x
            f x     = composite_label [lbl,label x]

    proof_po (FreeGoal v u t p li) lbl po = do
            new_goal <- free_vars $ po^.goal
            xs <- proof_po p lbl $ po & constants %~ M.insert u (Var u t)
                                      & goal .~ new_goal
            return xs
        where
            free_vars (Binder Forall ds r expr _) 
                    | are_fresh [u] po = return $ zforall (L.filter ((v /=) . view name) ds) 
                                                (rename v u r)
                                                (rename v u expr)
                    | otherwise        = Left $ [Error ([printf|variable '%s' cannot be freed as '%s'|] 
                                                    (render v) (render u)) li]
            free_vars expr = return expr

    proof_po (Easy _) lbl po = 
            return [(composite_label [lbl, label "easy"],po)]

    proof_po (Assume new_asm new_goal p _) lbl po = do
            pos <- proof_po p lbl $ po & named %~ (new_asm `M.union`) 
                                       & goal .~ new_goal
            return ( ( composite_label [lbl, label "new assumption"]
                     , empty_sequent 
                            & context .~ (po^.context)
                            & goal .~ (           zimplies (zall new_asm) new_goal 
                                       `zimplies` (po^.goal)) )
                   : pos)

    proof_po (Definition defs p li) lbl s = do
            let decl = symbols $ s^.absContext
                clashes = decl `M.intersection` M.mapKeys (view name) defs
                defs' = L.map (uncurry zeq . first Word) $ M.toList defs
            unless (M.null clashes) $
                Left [Error ([printf|Symbols %s are already defined|] $ intercalate "," $ L.map render $ M.keys clashes) li]
            proof_po p lbl $ 
                s & constants %~ (M.union $ symbol_table $ M.keys defs)
                  & nameless  %~ (defs' ++)
    proof_po (Assertion lemma dep p _) lbl po = do
            let depend = M.map M.fromList $ M.fromListWith (++) $ L.map f dep
                depend :: Table Label (Table Label ())
                f (x,y) = (x,[(y,())])
            pos1 <- proof_po p ( composite_label [lbl,label "main goal"] )
                $ po & nameless %~ (++ L.map fst (M.ascElems lemma))
            pos2 <- forM (M.toList lemma) (\(lbl2,(g,p)) -> do
                let used = fromMaybe M.empty $ lbl2 `M.lookup` depend
                    thm  = (M.map fst lemma) `M.intersection` used
                proof_po p (composite_label [lbl,label "assertion",lbl2]) 
                    $ po & named %~ (thm `M.union`)
                         & goal  .~ g )
            return (pos1 ++ concat pos2)

    proof_po    (InstantiateHyp hyp ps proof li) 
                lbl po = do -- (Sequent ctx asm hyps goal) = do
        if hyp `elem` M.ascElems (po^.named) 
                || hyp `elem` (po^.nameless) then do
            newh <- case hyp of
                Binder Forall vs r t _
                    | all (`elem` vs) (M.keys ps) -> do
                        let new_vs = L.foldl (flip L.delete) vs (M.keys ps)
                            ps'    = M.mapKeys (view name) ps
                            re     = substitute ps' r
                            te     = substitute ps' t
                        if L.null new_vs
                            then return $ zimplies re te
                            else return $ zforall new_vs re te
                _ -> Left [Error ("hypothesis is not a universal quantification:\n" 
                        ++ pretty_print' hyp) li]
            proof_po proof lbl $
                po & nameless %~ (newh:)
        else
            Left [Error ("formula is not an hypothesis:\n" 
                ++ pretty_print' hyp) li]

    proof_po (Keep ctx unnamed' named' proof _) lbl po = do
        proof_po proof lbl
            $ po & context  .~ ctx
                 & nameless .~ unnamed'
                 & named    .~ named'

chain :: Notation -> BinOperator -> BinOperator -> Either [String] BinOperator
chain n x y 
    | x == equal = Right y
    | y == equal = Right x
    | otherwise  = case (x,y) `L.lookup` (n^.chaining) of
                    Just z -> Right z
                    Nothing -> Left [[printf|chain: operators %s and %s don't chain|] 
                                    (pretty x) (pretty y)]


infer_goal :: Calculation -> Notation -> Either [String] Expr
infer_goal (Calc _ _ s0 xs _) n = do
        op <- mk_expr <$> foldM (chain n) equal (L.map g xs)
        case reverse $ L.map f xs of
            x:_ -> either 
                        (\x -> Left x) --,i,j)) 
                        Right 
                        (s0 `op` x)
            []   -> Left ["a calculation must include at least one reasoning step"] --,i,j)
    where
--        op = mk_expr $ foldl chain equal $ map g xs
        f (_,y,_,_) = y
        g (x,_,_,_) = x

instance PrettyPrintable Calculation where
    pretty (Calc _ g fs ss _) = 
            unlines ( [
                    pretty g,
                    "----",
                    "    " ++ pretty fs ]
                ++  concatMap f ss )
        where
            f (_, s, h, _) = (
                       (L.map ("      | " ++) $ L.map pretty h)
                    ++ [ "    " ++ pretty s ] )

show_proof :: Calculation -> String
show_proof = pretty

goal_po :: (HasGenExpr expr) 
        => CalculationBase expr 
        -> HOSequent expr
goal_po c = empty_sequent & context .~ (c^.context)
                          & nameless .~ xs
                          & goal .~ (c^.goal)
    where
        xs = concatMap (\(_,_,x,_) -> x) $ following c

obligations :: Context -> Sequent -> Calculation -> Either [Error] [Sequent]
obligations ctx s c = do
        L.map snd <$> obligations' ctx s c

obligations' :: Context -> Sequent -> Calculation -> Either [Error] [(Label, Sequent)]
obligations' ctx s c = do
        x  <- entails_goal_po ctx c
        ys <- steps_po ctx s c
        return (("relation",x):ys)

--proof_po :: Theory -> Proof -> Label -> Sequent -> Either [Error] [(Label,Sequent)]

are_fresh :: [Name] -> Sequent -> Bool
are_fresh vs po = 
        S.null $ S.fromList vs `S.intersection` (
                S.map (view name) $ 
                S.unions $ 
                L.map used_var es)
    where
        es = (po^.goal) : (po^.nameless) ++ (M.ascElems $ po^.named)

rename_all :: [(Var,Var)] -> Expr -> Expr
rename_all [] e = e
rename_all vs e@(Word v) = maybe e Word $ L.lookup v vs
rename_all vs (Binder q ds r xp t) = Binder q ds (rename_all us r) (rename_all us xp) t
    where
        us = L.filter (\(x,_) -> not $ x `elem` ds) vs
rename_all vs e = rewrite (rename_all vs) e 

steps_po :: Context -> Sequent -> Calculation -> Either [Error] [(Label, Sequent)]
steps_po ctx s (Calc d _ e0 es _) = f e0 es [1..]
    where
        f _ [] _ = return []
        f e0 ((r0, e1, a0,li):es) ns = do
                expr <- with_li li $ mk_expr r0 e0 e1
                let step = ( label ("step " ++ show (head ns))
                           , s & context  .~ (ctx `merge_ctx` d)
                               & nameless %~ (a0++)
                               & named .~ M.empty
                               & goal  .~ expr )
                (step:) <$> f e1 es (tail ns)

entails_goal_po :: Context 
                -> Calculation -> Either [Error] Sequent
entails_goal_po ctx (Calc d g e0 es li) = do
            a <- with_li li assume
            return $ empty_sequent
                & context .~ (ctx `merge_ctx` d)
                & nameless .~ a 
                & goal .~ g
    where
        assume = reverse <$> foldM f [] (L.map (\(x,y,z) -> (mk_expr x y z)) $ zip3 rs xs ys)
        f xs mx = do 
            x <- mx
            return (x:xs)
        ys = L.map(\(_,x,_,_) -> x) es
        xs = take (length es) (e0:ys)
        rs = L.map(\(x,_,_,_) -> x) es

instance NFData expr => NFData (ProofBase expr)
instance NFData expr => NFData (CalculationBase expr)

instance Serialize expr => Serialize (ProofBase expr) where
instance Serialize expr => Serialize (CalculationBase expr) where
