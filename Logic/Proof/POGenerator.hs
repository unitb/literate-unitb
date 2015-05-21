{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TemplateHaskell        #-}
module Logic.Proof.POGenerator 
    ( POGen, POGenT, Logic.Proof.POGenerator.context
    , emit_goal
    , eval_generator, eval_generatorT
    , with, prefix_label, prefix, named_hyps
    , nameless_hyps, variables, emit_exist_goal
    , Logic.Proof.POGenerator.definitions
    , Logic.Proof.POGenerator.functions 
    , existential, tracePOG )
where

    -- Modules
import Logic.Expr as E hiding ((.=))
import Logic.Proof.Sequent as S

import UnitB.Feasibility

    -- Libraries
import Control.Arrow
import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Reader.Class
import Control.Monad.RWS
import Control.Monad.State
import Control.Lens hiding (Context)

import Data.List as L
import Data.Map as M hiding ( map )

import Utilities.Error
import Utilities.Trace

import Text.Printf

data POParam = POP 
    { _pOParamContext :: Context
    , tag :: [Label]
    , _pOParamNameless :: [Expr]
    , _pOParamNamed :: Map Label Expr
    }

makeFields ''POParam

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
        $ forM_ clauses' $ \(vs,es) -> 
            unless (L.null es) $
                emit_goal (map (label . name) vs) (zexists vs ztrue $ zall es)
    where
        clauses = partition_expr vars es
        clauses' = M.toList $ M.fromListWith (++) clauses

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
        with (_context st) 
            $ emit_exist_goal [] vs ss'

emit_goal :: Monad m => [Label] -> Expr -> POGenT m ()
emit_goal lbl g = POGen $ do
    ctx  <- asks $ view S.context
    tag  <- asks tag
    asm  <- asks $ view nameless
    hyps <- asks $ view named
    tell [(composite_label $ tag ++ lbl, Sequent ctx asm hyps g)]

context :: Context -> State POParam ()
context = _context

_context :: Context -> State POParam ()
_context new_ctx = do
    S.context %= (new_ctx `merge_ctx`)

functions :: Map String Fun -> State POParam ()
functions new_funs = do
    _context $ Context M.empty M.empty new_funs M.empty M.empty

definitions :: Map String Def -> State POParam ()
definitions new_defs = do
    S.context.E.definitions .= new_defs

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
        named %= M.union hyps

nameless_hyps :: [Expr] -> State POParam ()
nameless_hyps hyps = do
        nameless %= (++hyps)

variables :: Map String Var -> State POParam ()
variables vars = do
        S.context.constants %= (vars `merge`)

eval_generator :: POGen () -> Map Label Sequent
eval_generator cmd = runIdentity $ eval_generatorT cmd
        -- fromList $ snd $ evalRWS (runPOGen cmd) empty_param ()

tracePOG :: Monad m => POGenT m () -> POGenT m ()
tracePOG (POGen cmd) = POGen $ do
    xs <- snd `liftM` listen cmd
    let goal (Sequent _ _ _ g) = g
    traceM $ unlines $ map (show . second goal) xs

eval_generatorT :: Monad m => POGenT m () -> m (Map Label Sequent)
eval_generatorT cmd = liftM (fromListWithKey (\k _ _ -> ($myError) $ printf "%s\n" $ show k) . snd) $ evalRWST (runPOGen cmd) empty_param ()
