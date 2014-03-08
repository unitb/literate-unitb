{-# LANGUAGE TypeOperators, MultiParamTypeClasses, FlexibleInstances, UndecidableInstances #-}
module Logic.Tactics 
    ( Tactic, TacticT, get_line_info, get_context
    , get_goal, by_parts
    , is_fresh, get_hypotheses, assert, assume
    , by_cases, easy, new_fresh, free_goal
    , instantiate_hyp, with_line_info
    , runTactic, runTacticT, make_expr
    )
where

import Logic.Calculation
import Logic.Classes
import Logic.Const
import Logic.Expr
import Logic.Label
import Logic.Sequent
import Logic.Theory

--import Latex.Parser

    -- Libraries
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State.Class
import Control.Monad.Trans.Either

import Control.Monad.Identity
import Data.List as L
import Data.Map  as M hiding (map)

import Utilities.Error
import Utilities.Format
import Utilities.Syntactic ( Error (..), LineInfo )

data TacticParam = TacticParam 
    { sequent :: Sequent
    , line_info :: LineInfo
    }

data TacticT m a = TacticT { unTactic :: ErrorT (ReaderT TacticParam m) a }

type Tactic = TacticT Identity

with_line_info :: Monad m => LineInfo -> TacticT m a -> TacticT m a
with_line_info li (TacticT cmd) = 
        TacticT $ ErrorT $ local (\p -> p { line_info = li }) $ runErrorT cmd

with_goal :: Monad m => Expr -> TacticT m a -> TacticT m a
with_goal e (TacticT cmd) = TacticT $ do
    Sequent ctx hyps _ <- lift $ asks sequent
    param              <- lift ask
    ErrorT $ local (const (param { sequent = Sequent ctx hyps e })) 
        $ runErrorT cmd

with_hypotheses :: Monad m
                => [Expr] -> TacticT m Proof 
                -> TacticT m Proof
with_hypotheses es (TacticT cmd) = TacticT $ do
    Sequent ctx hyps g <- lift $ asks sequent 
    param              <- lift ask
    ErrorT $ local (const (param { sequent = Sequent ctx (hyps ++ es) g })) 
        $ runErrorT cmd

with_variables :: Monad m
               => [Var] -> TacticT m Proof -> TacticT m Proof
with_variables vs (TacticT cmd) = TacticT $ do
    (Sequent ctx hyps g) <- lift $ asks sequent
    param              <- lift ask
    let (Context sorts vars funs defs dums) = ctx
        new_ctx = Context sorts (symbol_table vs `M.union` vars) funs defs dums
    ErrorT $ local (const (param { sequent = Sequent new_ctx hyps g })) $ 
        runErrorT cmd

get_line_info :: Monad m
              => TacticT m LineInfo
get_line_info = TacticT $ lift $ asks line_info

get_goal :: Monad m
         => TacticT m Expr
get_goal = TacticT $ do
        Sequent _ _ goal <- lift $ asks sequent
        return goal

get_hypotheses :: Monad m
               => TacticT m [Expr]
get_hypotheses = TacticT $ do
        Sequent _ hyps _ <- lift $ asks sequent
        return hyps

get_context :: Monad m
            => TacticT m Context
get_context = TacticT $ do
        Sequent ctx _ _ <- lift $ asks sequent
        return ctx

is_fresh :: Monad m
         => Var -> TacticT m Bool
is_fresh v = TacticT $ do
        s <- lift $ asks sequent
        return $ are_fresh [name v] s

assert :: Monad m
       => [(Label,Expr,TacticT m Proof)] 
       -> TacticT m Proof 
       -> TacticT m Proof
assert xs proof = do
        li <- get_line_info
        ys <- forM xs $ \(lbl,x,m) -> do
            y <- with_goal x m
            return (lbl,(x,y))
        p  <- with_hypotheses (map (fst . snd) ys) proof
        return $ Proof $ Assertion (fromList ys) p li

assume :: Monad m
       => [(Label,Expr)]
       -> Expr
       -> TacticT m Proof        
       -> TacticT m Proof
assume xs new_g proof = do
        li <- get_line_info
        p  <- with_hypotheses (map snd xs) 
            $ with_goal new_g proof
        return $ Proof $ Assume (fromList xs) new_g p li

by_cases :: Monad m
         => [(Label, Expr, TacticT m Proof)]
         -> TacticT m Proof
by_cases cs = do
        li <- get_line_info
        ps <- forM cs $ \(lbl,e,m) -> do
            p <- with_hypotheses [e] m 
            return (lbl,e,p)
        return $ Proof $ ByCases ps li

by_parts :: Monad m
         => [(Expr, TacticT m Proof)]
         -> TacticT m Proof
by_parts cs = do
        li <- get_line_info
        ps <- forM cs $ \(e,m) -> do
            p <- with_goal e m 
            return (e,p)
        return $ Proof $ ByParts ps li

easy :: Monad m
     => TacticT m Proof
easy = do
        li <- get_line_info
        return $ Proof $ Easy li

new_fresh :: Monad m
          => String -> Type 
          -> TacticT m Var
new_fresh name t = do
        fix (\rec n suf -> do
            let v = Var (name ++ suf) t
            b <- is_fresh v
            if b then return v
            else do
                rec (n+1) (show n)
            ) 0 ""

free_goal :: Monad m
          => Var -> Var 
          -> TacticT m Proof 
          -> TacticT m Proof
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

instantiate_hyp :: Monad m
                => Expr -> [(Var,Expr)] 
                -> TacticT m Proof
                -> TacticT m Proof
instantiate_hyp hyp ps proof = do
        hyps <- get_hypotheses
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

make_expr :: Monad m
          => Either String a
          -> TacticT m a
make_expr e = do
        li <- get_line_info
        let f xs = Left [Error xs li]
        TacticT $ fromEitherT $ hoistEither (either f Right e)

runTacticT :: Monad m
           => LineInfo -> Sequent
           -> TacticT m a -> m (Either [Error] a)
runTacticT li s (TacticT tac) = do
        x <- runReaderT (runErrorT tac) (TacticParam s li)
        case x of
            Right (x,[])  -> return $ Right x
            Right (_,err) -> return $ Left err
            Left err -> return $ Left err

runTactic li s tac = runIdentity (runTacticT li s tac)
          
instance Monad m => Monad (TacticT m) where
    TacticT m >>= f = TacticT $ m >>= (unTactic . f)
    return x       = TacticT $ return x
    fail msg       = do
            li <- get_line_info
            TacticT $ hard_error [Error msg li]

instance MonadState s m => MonadState s (TacticT m) where
    get = lift get
    put x = lift $ put x

instance MonadReader r m => MonadReader r (TacticT m) where
    ask = lift $ ask
    local f (TacticT (ErrorT (ReaderT cmd))) = TacticT $ 
            ErrorT $ 
            ReaderT $ \r ->
            local f $ cmd r

instance MonadTrans TacticT where
    lift cmd = TacticT $ lift $ lift cmd

instance Monad m => MonadError (TacticT m) where
    soft_error e = TacticT $ soft_error e
    hard_error e = TacticT $ hard_error e
    make_hard (TacticT cmd) = TacticT $ make_hard cmd
    make_soft x (TacticT cmd) = TacticT $ make_soft x cmd

