{-# LANGUAGE TypeOperators, MultiParamTypeClasses, FlexibleInstances, UndecidableInstances #-}
module Logic.Tactics where

import Logic.Calculation
import Logic.Classes
import Logic.Const
import Logic.Expr
import Logic.Label
import Logic.Sequent

    -- Libraries
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Trans.Either

import Data.List as L
import Data.Map  as M hiding (map)

import Utilities.Format
import Utilities.Syntactic

data Tactic a = Tactic { unTactic :: EitherT [Error] (Reader (Sequent, LineInfo)) a }

with_goal :: Expr -> Tactic a -> Tactic a
with_goal e (Tactic cmd) = Tactic $ do
    (Sequent ctx hyps _, li) <- lift ask 
    EitherT $ local (const (Sequent ctx hyps e, li)) $ runEitherT cmd

with_hypotheses :: [Expr] -> Tactic Proof -> Tactic Proof
with_hypotheses es (Tactic cmd) = Tactic $ do
    (Sequent ctx hyps g, li) <- lift ask 
    EitherT $ local (const (Sequent ctx (hyps ++ es) g, li)) $ runEitherT cmd

with_variables :: [Var] -> Tactic Proof -> Tactic Proof
with_variables vs (Tactic cmd) = Tactic $ do
    (Sequent (Context sorts vars funs defs dums) hyps g, li) <- lift ask 
    let new_ctx = Context sorts (symbol_table vs `M.union` vars) funs defs dums
    EitherT $ local (const (Sequent new_ctx hyps g, li)) $ runEitherT cmd

get_line_info :: Tactic LineInfo
get_line_info = Tactic $ liftM snd $ lift ask

get_goal :: Tactic Expr
get_goal = Tactic $ do
        Sequent _ _ goal <- liftM fst $ lift ask
        return goal

get_hypothesis :: Tactic [Expr]
get_hypothesis = Tactic $ do
        Sequent _ hyps _ <- liftM fst $ lift ask
        return hyps

is_fresh :: Var -> Tactic Bool
is_fresh v = Tactic $ do
        s <- liftM fst $ lift ask
        return $ are_fresh [name v] s

assert :: [(Label,Expr,Tactic Proof)] 
       -> Tactic Proof 
       -> Tactic Proof
assert xs proof = do
        li <- get_line_info
        ys <- forM xs $ \(lbl,x,m) -> do
            y <- with_goal x m
            return (lbl,(x,y))
        p  <- with_hypotheses (map (fst . snd) ys) proof
        return $ Proof $ Assertion (fromList ys) p li

assume :: [(Label,Expr)]
       -> Expr
       -> Tactic Proof        
       -> Tactic Proof
assume xs new_g proof = do
        li <- get_line_info
        p  <- with_hypotheses (map snd xs) 
            $ with_goal new_g proof
        return $ Proof $ Assume (fromList xs) new_g p li

by_cases :: [(Label, Expr, Tactic Proof)]
         -> Tactic Proof
by_cases cs = do
        li <- get_line_info
        ps <- forM cs $ \(lbl,e,m) -> do
            p <- with_hypotheses [e] m 
            return (lbl,e,p)
        return $ Proof $ ByCases ps li

easy :: Tactic Proof
easy = do
        li <- get_line_info
        return $ Proof $ Easy li

new_fresh :: String -> Type 
          -> Tactic Var
new_fresh name t = do
        fix (\rec n suf -> do
            let v = Var (name ++ suf) t
            b <- is_fresh v
            if b then return v
            else do
                rec (n+1) (show n)
            ) 0 ""

free_goal :: Var -> Var 
          -> Tactic Proof 
          -> Tactic Proof
free_goal v0 v1 m = do
        li   <- get_line_info
        goal <- get_goal 
        b    <- is_fresh v1
        new  <- rename (name v0) (name v1) `liftM` case goal of 
            Binder Forall bv r t
                | not b         -> fail $ format "'{0}' is not a fresh variable" v1
                | [v0] == bv    -> return $ r `zimplies` t
                |  v0 `elem` bv -> return $ Binder Forall (L.delete v0 bv) r t
                | otherwise     -> fail $ format "'{0}' is not a bound variable in:\n{1}"
                                    v0 $ pretty_print' goal
            _ -> fail $ "goal is not a universal quantification:\n" ++ pretty_print' goal
        p <- with_variables [v1] $ with_goal new m
        let t = type_of (Word v1)
        return $ Proof $ FreeGoal (name v0) (name v1) t p li

instantiate_hyp :: Expr -> [(Var,Expr)] 
                -> Tactic Proof
                -> Tactic Proof
instantiate_hyp hyp ps proof = do
        hyps <- get_hypothesis
        li   <- get_line_info
        if hyp `elem` hyps then do
            newh <- case hyp of
                Binder Forall vs r t 
                    | all (`elem` vs) (map fst ps) -> do
                        let new_vs = L.foldl (flip L.delete) vs (map fst ps)
                            re     = substitute (fromList ps) r
                            te     = substitute (fromList ps) t
                        if L.null new_vs
                            then return $ zimplies re te
                            else return $ zforall new_vs re te
                _ -> fail $ "hypothesis is not a universal quantification:\n" 
                        ++ pretty_print' hyp
            p <- with_hypotheses [newh] proof
            return $ Proof $ InstantiateHyp hyp (fromList ps) p li
        else
            fail $ "formula is not an hypothesis:\n" 
                ++ pretty_print' hyp


make_expr :: Either String a
          -> Tactic a
make_expr e = do
        li <- get_line_info
        let f xs = Left [Error xs li]
        Tactic $ hoistEither (either f Right e)

runTactic :: LineInfo -> Sequent
          -> Tactic a -> Either [Error] a
runTactic li s (Tactic tac) = runReader (runEitherT tac) (s,li)
          
instance Monad Tactic where
    Tactic m >>= f = Tactic $ m >>= (unTactic . f)
    return x       = Tactic $ return x
    fail msg       = do
            li <- get_line_info
            Tactic $ left [Error msg li]
