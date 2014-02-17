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
import Control.Monad.Trans
import Control.Monad.Trans.Either
import Control.Monad.Trans.Reader

import Data.Function
import Data.List as L
import Data.Map  as M hiding (map)

import Utilities.Format
import Utilities.Syntactic

infixr 6 :+
--infixr 5 >>>=

data Null = Null
data (:+) a b = (:+) a b 

data Tactic m a = Tactic { unTactic :: EitherT [Error] (ReaderT (Sequent, LineInfo) m) a }

with_goal :: Monad m => Expr -> Tactic m a -> Tactic m a
with_goal e (Tactic cmd) = Tactic $ do
    (Sequent ctx hyps _, li) <- lift ask 
    EitherT $ local (const (Sequent ctx hyps e, li)) $ runEitherT cmd

with_hypotheses :: Monad m => [Expr] -> Tactic m Proof -> Tactic m Proof
with_hypotheses es (Tactic cmd) = Tactic $ do
    (Sequent ctx hyps g, li) <- lift ask 
    EitherT $ local (const (Sequent ctx (hyps ++ es) g, li)) $ runEitherT cmd

with_variables :: Monad m => [Var] -> Tactic m Proof -> Tactic m Proof
with_variables vs (Tactic cmd) = Tactic $ do
    (Sequent (Context sorts vars funs defs dums) hyps g, li) <- lift ask 
    let new_ctx = Context sorts (symbol_table vs `M.union` vars) funs defs dums
    EitherT $ local (const (Sequent new_ctx hyps g, li)) $ runEitherT cmd

get_line_info :: Monad m => Tactic m LineInfo
get_line_info = Tactic $ liftM snd $ lift ask

get_goal :: Monad m => Tactic m Expr
get_goal = Tactic $ do
        Sequent _ _ goal <- liftM fst $ lift ask
        return goal

is_fresh :: Monad m => Var -> Tactic m Bool
is_fresh v = Tactic $ do
        s <- liftM fst $ lift ask
        return $ are_fresh [name v] s

assert :: Monad m 
       => [(Label,Expr,Tactic m Proof)] 
       -> Tactic m Proof 
       -> Tactic m Proof
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
       -> Tactic m Proof        
       -> Tactic m Proof
assume xs new_g proof = do
        li <- get_line_info
        p  <- with_hypotheses (map snd xs) 
            $ with_goal new_g proof
        return $ Proof $ Assume (fromList xs) new_g p li

by_cases :: Monad m
         => [(Label, Expr, Tactic m Proof)]
         -> Tactic m Proof
by_cases cs = do
        li <- get_line_info
        ps <- forM cs $ \(lbl,e,m) -> do
            p <- with_hypotheses [e] m 
            return (lbl,e,p)
        return $ Proof $ ByCases ps li

easy :: Monad m
     => Tactic m Proof
easy = do
        li <- get_line_info
        return $ Proof $ Easy li

new_fresh :: Monad m 
          => String -> Type 
          -> Tactic m Var
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
          -> Tactic m Proof 
          -> Tactic m Proof
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

make_expr :: Monad m
          => Either String a
          -> Tactic m a
make_expr e = do
        li <- get_line_info
        let f xs = Left [Error xs li]
        Tactic $ hoistEither (either f Right e)

runTactic :: Monad m 
          => LineInfo -> Sequent
          -> Tactic m a -> m (Either [Error] a)
runTactic li s (Tactic tac) = runReaderT (runEitherT tac) (s,li)
          
instance Monad m => Monad (Tactic m) where
    Tactic m >>= f = Tactic $ m >>= (unTactic . f)
    return x       = Tactic $ return x
    fail msg       = do
            li <- get_line_info
            Tactic $ left [Error msg li]

instance MonadTrans Tactic where
    lift m = Tactic $ lift $ lift m

--fork_ :: [(Sequent, Tactic ())] -> Tactic ()
--fork_ xs = mapM_ f xs
--    where
--        f (x,Tactic y) = Tactic $ local (const x) y
--
--class Append a b c where
--    append :: a -> b -> c
--
--instance Append (a :+ b) Null (a :+ b) where
--    append x _ = x
--
--instance Append Null (a :+ b) (a :+ b) where
--    append _ x = x
--
--instance Append Null Null Null where
--    append _ _ = Null
--
--instance Append as bs cs => Append (a :+ as) bs (a :+ cs) where
--    append (x :+ xs) ys = x :+ append xs ys
--
--class Zip as bs cs where
--    zip_tuple :: as -> bs -> cs
--
--instance Zip Null Null Null where
--    zip_tuple _ _ = Null
--
--instance Zip as bs cs => Zip (a :+ as) (b :+ bs) ((a,b) :+ cs) where
--    zip_tuple (x :+ xs) (y :+ ys) = (x,y) :+ zip_tuple xs ys
--
--class Apply as bs cs where
--
--
--instance Apply Null Null Null where
--
--instance Apply as bs cs => 
--    Apply (Sequent :+ as) ( Tactic b :+ bs ) (c :+ cs) where
--
--class StringList xs where
--    string_list :: xs -> [String]
--
--instance StringList (Null,()) where
--    string_list _ = []
--
--instance (Show a, StringList (as,())) => StringList (a :+ as,()) where
--    string_list (x :+ xs, ()) = show x : string_list (xs,())
--
--instance StringList (as,()) => Show as where
--    show xs = "[ " ++ intercalate ", " (string_list (xs,())) ++ " ]"
--
--test0 = zip_tuple (a1 :+ a2 :+ Null) (b1 :+ b2 :+ Null) :: (Int,Int) :+ (Int,Int) :+ Null
--    where
--        (a1,a2,b1,b2) = (1,2,3,4) :: (Int,Int,Int,Int)
--
----class Concat as bs where
----    append_all :: as -> bs
----
----instance Concat Null Null where
----    append_all _ = Null
----
----instance (Append a bs cs, Concat as bs) => Concat (a :+ as) cs where
----    append_all (x :+ xs) = append x (append_all xs :: bs)