{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
module UnitB.POGenerator 
    ( POGen, POGenT, context, emit_goal
    , eval_generator, eval_generatorT
    , with, prefix_label, prefix, named_hyps
    , nameless_hyps, variables, emit_exist_goal
    , definitions, existential, functions )
where

import Logic.Expr
import Logic.Proof

import UnitB.Feasibility

import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Reader.Class
import Control.Monad.RWS
import Control.Monad.State

import Data.List as L
import Data.Map as M hiding ( map )

data POParam = POP 
    { ctx :: Context
    , tag :: [Label]
    , nameless :: [Expr]
    , named :: Map Label Expr
    }

empty_param :: POParam
empty_param = POP empty_ctx [] [] M.empty

type POGen = POGenT Identity

newtype POGenT m a = POGen { runPOGen :: RWST POParam [(Label,Sequent)] () m a }

instance Monad m => Applicative (POGenT m) where
    (<*>) = ap
    pure = return

instance Monad m => Functor (POGenT m) where
    fmap = liftM

instance Monad m => Monad (POGenT m) where
    POGen m >>= f = POGen $ m >>= runPOGen . f
    return = POGen . return

instance MonadTrans POGenT where
    lift = POGen . lift

emit_exist_goal :: Monad m => [Label] -> [Var] -> [Expr] -> POGenT m ()
emit_exist_goal lbl vars es = with
        (mapM_ prefix_label lbl)
        $ forM_ clauses $ \(vs,es) -> 
            unless (L.null es) $
                emit_goal (map (label . name) vs) (zexists vs ztrue $ zall es)
    where
        clauses = partition_expr vars es

existential :: Monad m => [Var] -> POGenT m () -> POGenT m ()
existential [] cmd = cmd
existential vs (POGen cmd) = do
        let g (_, Sequent ctx h0 h1 goal) = do
                    vs <- f ctx
                    return $ zforall vs ztrue $ zall (h0 ++ M.elems h1) `zimplies` goal
            f (Context s vs fs def _) 
                | not $ M.null s = error "existential: cannot add sorts in existentials"
                -- |    not (M.null fs) 
                --   || not (M.null def) = error "existential: cannot introduce new function symbols in existentials"
                | otherwise = do
                    modify (`merge_ctx` Context M.empty M.empty fs def M.empty)
                    return $ M.elems vs
            -- f xs = [(tag, zexists vs ztrue $ zall $ map snd xs)]
        ss <- POGen 
            $ censor (const []) $ listen 
            $ local (const empty_param) cmd
        let (ss',st) = runState (mapM g $ snd ss) empty_ctx
        with (context st) 
            $ emit_exist_goal [] vs ss'

emit_goal :: Monad m => [Label] -> Expr -> POGenT m ()
emit_goal lbl g = POGen $ do
    ctx  <- asks ctx
    tag  <- asks tag
    asm  <- asks nameless
    hyps <- asks named
    tell [(composite_label $ tag ++ lbl, Sequent ctx asm hyps g)]

context :: Context -> State POParam ()
context new_ctx = do
    ctx <- gets ctx
    modify $ \p -> p { ctx = new_ctx `merge_ctx` ctx }

functions :: Map String Fun -> State POParam ()
functions new_funs = do
    context $ Context M.empty M.empty new_funs M.empty M.empty

definitions :: Map String Def -> State POParam ()
definitions new_defs = do
    let new_ctx = Context M.empty M.empty M.empty new_defs M.empty
    context new_ctx

with :: Monad m => State POParam () -> POGenT m a -> POGenT m a
with f cmd = POGen $ local (execState f) $ runPOGen cmd

prefix_label :: Label -> State POParam ()
prefix_label lbl = do
        tag <- gets tag
        modify $ \p -> p { tag = tag ++ [lbl] }

prefix :: String -> State POParam ()
prefix lbl = prefix_label $ label lbl

named_hyps :: Map Label Expr -> State POParam ()
named_hyps hyps = do
        h <- gets named
        modify $ \p -> p { named = hyps `M.union` h }

nameless_hyps :: [Expr] -> State POParam ()
nameless_hyps hyps = do
        h <- gets nameless
        modify $ \p -> p { nameless = h ++ hyps }

variables :: Map String Var -> State POParam ()
variables vars = do
        ctx <- gets ctx
        let new_ctx = Context M.empty vars M.empty M.empty M.empty
        modify $ \p -> p 
            { ctx = new_ctx `merge_ctx` ctx }

eval_generator :: POGen () -> Map Label Sequent
eval_generator cmd = runIdentity $ eval_generatorT cmd
        -- fromList $ snd $ evalRWS (runPOGen cmd) empty_param ()

eval_generatorT :: Monad m => POGenT m () -> m (Map Label Sequent)
eval_generatorT cmd = liftM (fromList . snd) $ evalRWST (runPOGen cmd) empty_param ()
