{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE UndecidableInstances   #-}
module Logic.Tactics 
    ( Tactic, TacticT, get_line_info, get_context
    , get_goal, by_parts
    , is_fresh, get_hypotheses, assert, assume
    , by_cases, easy, new_fresh, free_goal
    , instantiate_hyp, with_line_info
    , runTactic, runTacticT
    , runTacticWithTheorems, runTacticTWithTheorems
    , make_expr, fresh_label
    , last_step, add_step, TheoremRef ( .. )
    , get_dummy, lookup_hypothesis, clear_vars
    , free_vars_goal, instantiate_hyp_with
    , get_named_hyps, get_nameless_hyps
    , get_used_vars, get_allocated_vars
    , use_theorems
    )
where

import Logic.Operator
import Logic.Calculation
import Logic.Classes
import Logic.Const
import Logic.Expr
import Logic.Label
import Logic.Sequent
import Logic.Theory hiding ( theorems )

    -- Libraries
import Control.Monad
import Control.Monad.RWS
import Control.Monad.Trans.Either

import Control.Monad.Identity

import           Data.Graph
import           Data.List as L
import qualified Data.List.Ordered as OL
import           Data.Map  as M hiding (map)
import qualified Data.Set  as S

import Utilities.Error
import Utilities.Format
import Utilities.Graph hiding ( map )
import Utilities.Syntactic ( Error (..), LineInfo )

data TacticParam = TacticParam 
    { sequent :: Sequent
    , line_info :: LineInfo
    , theorems  :: Map Label Expr
    }

data TacticT m a = TacticT 
        { unTactic :: ErrorT 
                (RWST 
                    TacticParam 
                    [Label] 
                    (S.Set Label,S.Set String) m) a }

type Tactic = TacticT Identity

tac_local :: Monad m
          => TacticParam
          -> TacticT m a
          -> TacticT m a
tac_local x (TacticT (ErrorT cmd)) = TacticT $ ErrorT $ local (const x) cmd

tac_listen :: Monad m
           => TacticT m a
           -> TacticT m (a, [Label])
tac_listen (TacticT (ErrorT cmd)) = TacticT $ ErrorT $ do
        (x,w) <- listen cmd
        case x of
            Right (x,y) -> return $ Right ((x,w),y)
            Left x -> return $ Left x

tac_censor :: Monad m
           => ([Label] -> [Label])
           -> TacticT m a
           -> TacticT m a
tac_censor f (TacticT (ErrorT cmd)) = TacticT $ ErrorT $ censor f cmd

with_line_info :: Monad m => LineInfo -> TacticT m a -> TacticT m a
with_line_info li (TacticT cmd) = 
        TacticT $ ErrorT $ local (\p -> p { line_info = li }) $ runErrorT cmd

with_goal :: Monad m => Expr -> TacticT m a -> TacticT m a
with_goal e (TacticT cmd) = TacticT $ do
    Sequent ctx asm hyps _ <- lift $ asks sequent
    param              <- lift ask
    ErrorT $ local (const (param { sequent = Sequent ctx asm hyps e })) 
        $ runErrorT cmd

with_hypotheses :: Monad m
                => [(Label, Expr)] 
                -> TacticT m a 
                -> TacticT m a
with_hypotheses es cmd = do
    param              <- TacticT $ lift ask
    let Sequent ctx asm hyps g = sequent param
    let new_hyp = (M.fromList es `M.union` hyps)
    tac_local (param { sequent = Sequent ctx asm new_hyp g }) cmd

with_variables :: Monad m
               => [Var] -> TacticT m Proof -> TacticT m Proof
with_variables vs (TacticT cmd) = TacticT $ do
    (Sequent ctx asm hyps g) <- lift $ asks sequent
    param              <- lift ask
    let (Context sorts vars funs defs dums) = ctx
        new_ctx = Context sorts (symbol_table vs `M.union` vars) funs defs dums
    ErrorT $ local (const (param { sequent = Sequent new_ctx asm hyps g })) $ 
        runErrorT cmd

get_dummy :: Monad m
          => String -> TacticT m Var
get_dummy var = do
        ctx <- get_context
        li  <- get_line_info
        let Context _ _ _ _ vars = ctx
        maybe 
            (hard_error [Error ("invalid dummy: " ++ var) li])
            return
            $ M.lookup var vars


get_line_info :: Monad m
              => TacticT m LineInfo
get_line_info = TacticT $ lift $ asks line_info

get_goal :: Monad m
         => TacticT m Expr
get_goal = TacticT $ do
        Sequent _ _ _ goal <- lift $ asks sequent
        return goal

get_named_hyps :: Monad m
               => TacticT m (Map Label Expr)
get_named_hyps = TacticT $ do 
        Sequent _ _ hyps _ <- lift $ asks sequent
        return hyps

get_nameless_hyps :: Monad m
                  => TacticT m [Expr]
get_nameless_hyps = TacticT $ do 
        Sequent _ asm _ _ <- lift $ asks sequent
        return asm

get_hypotheses :: Monad m
               => TacticT m [Expr]
get_hypotheses = TacticT $ do
        Sequent _ asm hyps _ <- lift $ asks sequent
        return $ asm ++ elems hyps

lookup_hypothesis :: Monad m
                  => TheoremRef
                  -> TacticT m Expr
lookup_hypothesis (ThmRef hyp inst) = do
        li <- get_line_info
        let err_msg = Error (format "predicate is undefined: '{0}'" hyp) li
        Sequent _ _ hyps _ <- TacticT $ lift $ asks sequent
        x <- maybe 
            (hard_error [err_msg])
            return
            $ M.lookup hyp hyps
        instantiate x inst

get_context :: Monad m
            => TacticT m Context
get_context = TacticT $ do
        Sequent ctx _ _ _ <- lift $ asks sequent
        return ctx

add_theorems :: Monad m
             => [(Label,Expr)] 
             -> TacticT m Proof 
             -> TacticT m (Proof, [Label])
add_theorems thms proof = do
        param <- TacticT $ lift ask
        let new_thm = fromList thms
            f xs = sort xs `OL.minus` keys new_thm
        tac_censor f $ tac_listen $ tac_local 
            (param { theorems = new_thm `M.union` theorems param })
            proof
        

assert :: Monad m
       => [(Label,Expr,TacticT m Proof)] 
       -> TacticT m Proof 
       -> TacticT m Proof
assert xs proof = make_hard $ do
        li <- get_line_info
        let thm       = map f xs
            f (x,y,_) = (x,y)
        ps <- forM xs $ \(lbl,x,m) -> do
            p     <- easy
            (p,r) <- add_theorems thm 
                $ make_soft p 
                $ with_goal x m
            return ((lbl,x),(lbl,(x,p)),(map (\x -> (lbl,x)) r))
        let (xs,ys,zs) = unzip3 ps
            -- (xs,ys,zs) =
            -- (new hypotheses
            -- , assertions with proof objects
            -- , dependencies between assertions)
        make_hard $ forM_ (cycles $ concat zs) $ \x ->
            let msg = "a cycle exists between the proofs of the assertions {0}" in
            case x of
                AcyclicSCC _ -> return ()
                CyclicSCC cs -> soft_error [Error (format msg $ intercalate "," $ map show cs) li]
        p  <- with_hypotheses xs proof
        return $ Proof $ Assertion (fromList ys) (concat zs) p li

assume :: Monad m
       => [(Label,Expr)]
       -> Expr
       -> TacticT m Proof        
       -> TacticT m Proof
assume xs new_g proof = do
        li <- get_line_info
        p  <- with_hypotheses xs
            $ with_goal new_g proof
        return $ Proof $ Assume (fromList xs) new_g p li

clear_vars :: Monad m
           => [Var]
           -> TacticT m Proof
           -> TacticT m Proof
clear_vars vars proof = do
        param <- TacticT $ lift $ ask
        let Sequent ctx asm hyp g = sequent param
            new_asm = L.filter f asm
            new_hyp = M.filter f hyp
            f x     = not $ any (`S.member` used_var x) vars
            Context a old_vars b c d = ctx
            new_vars = L.foldl (flip M.delete) old_vars (map name vars)
            new_ctx  = Context a new_vars b c d
        li    <- get_line_info
        (p,w) <- tac_listen $ tac_local 
            (param { sequent = Sequent new_ctx new_asm new_hyp g }) $
            do  (lbls,ids)  <- TacticT $ lift $ get
                let new_ids = ids `S.difference` S.fromList (map name vars)
                TacticT $ lift $ put (lbls,new_ids)
                p           <- proof
                TacticT $ lift $ put (lbls,ids)
                return p
        let thm = M.filter f $ theorems param `intersection` fromList (zip w $ repeat ())
        return $ Proof $ Keep new_ctx new_asm (thm `M.union` new_hyp) p li
        

by_cases :: Monad m
         => [(Label, Expr, TacticT m Proof)]
         -> TacticT m Proof
by_cases cs = make_hard $ do
        li <- get_line_info
        ps <- forM cs $ \(lbl,e,m) -> do
            p <- easy
            p <- make_soft p $ with_hypotheses [(lbl,e)] m 
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

data TheoremRef = ThmRef Label [(Var,Expr)]

use_theorems :: Monad m
             => [(TheoremRef,LineInfo)]
             -> TacticT m a
             -> TacticT m a
use_theorems hint cmd = do
        thms     <- TacticT $ lift $ asks theorems
        thms     <- liftM concat $ forM hint $ \(ThmRef lbl _, _) -> do
            hyps <- get_named_hyps
            case lbl `M.lookup` thms of
                Just e 
                    | not $ lbl `M.member` hyps -> do
                        TacticT $ lift $ tell [lbl]
                        return [(lbl,e)]
                _ -> return []
        with_hypotheses thms cmd

add_step :: Monad m
         => Expr
         -> BinOperator
         -> [(TheoremRef,LineInfo)]
         -> TacticT m Calculation
         -> TacticT m Calculation
add_step step op hint calc = make_hard $ do
        use_theorems hint $ do
            hyp     <- forM hint $ \(ref,li) -> 
                with_line_info li $ make_soft ztrue $ lookup_hypothesis ref
            trivial <- last_step ztrue
            r       <- make_soft trivial calc
            li      <- get_line_info
            return r { 
                first_step = step,
                following  = (op,first_step r,hyp,li):following r }

last_step :: Monad m => Expr -> TacticT m Calculation
last_step xp = do
        li  <- get_line_info
        ctx <- get_context
        return $ Calc ctx ztrue xp [] li

get_used_vars :: Monad m
              => TacticT m [Var]
get_used_vars = do
        Sequent _ asm hyp g <- TacticT $ lift $ asks sequent
        return $ S.toList $ S.unions $ 
               used_var g
             : map used_var asm 
            ++ map used_var (M.elems hyp)

get_allocated_vars :: Monad m
                   => TacticT m [String]
get_allocated_vars = do
        (_,ids) <- TacticT $ lift $ get
        return $ S.toList ids

is_fresh :: Monad m
         => Var -> TacticT m Bool
is_fresh v = TacticT $ do
        s       <- lift $ asks sequent
        return $    are_fresh [name v] s

new_fresh :: Monad m
          => String -> Type 
          -> TacticT m Var
new_fresh name t = do
        fix (\rec n suf -> do
            let v = Var (name ++ suf) t
            b <- is_fresh v
            (lbls,ids) <- TacticT $ lift $ get
            if b && not ((name ++ suf) `S.member` ids)
            then TacticT $ do
                lift $ put (lbls,S.insert (name ++ suf) ids)
                return v
            else do
                rec (n+1) (show n)
            ) 0 ""

is_label_fresh :: Monad m => Label -> TacticT m Bool
is_label_fresh lbl = do
        Sequent _ _ hyps _ <- TacticT $ asks sequent
        thm                <- TacticT $ asks theorems
        return $   (not $ lbl `member` hyps) 
                && (not $ lbl `member` thm)

fresh_label :: Monad m
            => String -> TacticT m Label
fresh_label name = do
        fix (\rec n suf -> do
            let v = label (name ++ suf)
            b           <- is_label_fresh v
            (lbls, ids) <- TacticT $ get
            if b && not (v `S.member` lbls) 
            then TacticT $ do
                lift $ put (S.insert v lbls,ids)
                return v
            else do
                rec (n+1) (show n)
            ) 0 ""

free_vars_goal :: Monad m
               => [(Var,Var)]
               -> TacticT m Proof
               -> TacticT m Proof
free_vars_goal [] proof = proof
free_vars_goal ((v0,v1):vs) proof = do
        free_goal v0 v1 $
            free_vars_goal vs proof

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

instantiate :: Monad m
            => Expr -> [(Var,Expr)] 
            -> TacticT m Expr
instantiate hyp ps = do
        case hyp of
            Binder Forall vs r t 
                | all (`elem` vs) (map fst ps) -> do
                    let new_vs = L.foldl (flip L.delete) vs (map fst ps)
                        re     = substitute (fromList ps) r
                        te     = substitute (fromList ps) t
                        newh   = if L.null new_vs
                                    then zimplies re te
                                    else zforall new_vs re te
                    return newh
            _ 
                | not $ L.null ps -> fail $ "predicate is not a universal quantification:\n" 
                    ++ pretty_print' hyp
            _  -> return hyp

instantiate_hyp_with :: Monad m
                     => Expr 
                     -> [[(Var,Expr)]] 
                     -> TacticT m Proof
                     -> TacticT m Proof    
instantiate_hyp_with _ [] proof = proof
instantiate_hyp_with hyp (p:ps) proof = do
        lbl <- fresh_label "H"
        instantiate_hyp hyp lbl p $
            instantiate_hyp_with hyp ps proof

instantiate_hyp :: Monad m
                => Expr -> Label 
                -> [(Var,Expr)] 
                -> TacticT m Proof
                -> TacticT m Proof
instantiate_hyp hyp lbl ps proof = do
        hyps <- get_hypotheses
        li   <- get_line_info
        if hyp `elem` hyps then do
            newh <- instantiate hyp ps
            p    <- with_hypotheses [(lbl,newh)] proof
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
        (x,_,_) <- runRWST (runErrorT tac) (TacticParam s li M.empty) (S.empty,S.empty)
        case x of
            Right (x,[])  -> return $ Right x
            Right (_,err) -> return $ Left err
            Left err -> return $ Left err

runTacticTWithTheorems :: Monad m
                       => LineInfo -> Sequent
                       -> Map Label Expr
                       -> TacticT m a -> m (Either [Error] (a,[Label]))
runTacticTWithTheorems li s thms (TacticT tac) = do
        (x,_,thms) <- runRWST (runErrorT tac) (TacticParam s li thms) (S.empty,S.empty)
        case x of
            Right (x,[])  -> return $ Right (x,thms)
            Right (_,err) -> return $ Left err
            Left err -> return $ Left err

runTactic :: LineInfo -> Sequent -> Tactic a -> Either [Error] a
runTactic li s tac = runIdentity (runTacticT li s tac)

runTacticWithTheorems :: LineInfo -> Sequent 
                      -> Map Label Expr
                      -> Tactic a -> Either [Error] (a, [Label])
runTacticWithTheorems li s thms tac = runIdentity (runTacticTWithTheorems li s thms tac)
          
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
    local f (TacticT (ErrorT (RWST cmd))) = TacticT $ 
            ErrorT $ 
            RWST $ \r s ->
            local f $ cmd r s

instance MonadTrans TacticT where
    lift cmd = TacticT $ lift $ lift cmd

instance Monad m => MonadError (TacticT m) where
    soft_error e = TacticT $ soft_error e
    hard_error e = TacticT $ hard_error e
    make_hard (TacticT cmd) = TacticT $ make_hard cmd
    make_soft x (TacticT cmd) = TacticT $ make_soft x cmd

