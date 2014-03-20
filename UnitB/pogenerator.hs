module UnitB.POGenerator 
    ( POGen, context, emit_goal, eval_generator
    , with, prefix_label, prefix, named_hyps
    , nameless_hyps, variables, emit_exist_goal )
where

import Logic.Label
import Logic.Expr
import Logic.Sequent
import Logic.Const
import Logic.Classes

import UnitB.Feasibility

import Control.Monad.RWS
import Control.Monad.State

import Data.Map hiding ( map )

data POParam = POP 
    { ctx :: Context
    , tag :: [Label]
    , nameless :: [Expr]
    , named :: Map Label Expr
    }

empty_param :: POParam
empty_param = POP empty_ctx [] [] empty

type POGen = RWS POParam [(Label,Sequent)] ()

emit_exist_goal :: [Label] -> [Var] -> [Expr] -> POGen ()
emit_exist_goal lbl vars es = with
        (mapM_ prefix_label lbl)
        $ forM_ clauses $ \(vs,es) -> 
            emit_goal (map (label . name) vs) (zexists vs ztrue $ zall es)
    where
        clauses = partition_expr vars es
    

emit_goal :: [Label] -> Expr -> POGen ()
emit_goal lbl g = do
    ctx  <- asks ctx
    tag  <- asks tag
    asm  <- asks nameless
    hyps <- asks named
    tell [(composite_label $ tag ++ lbl, Sequent ctx asm hyps g)]

context :: Context -> State POParam ()
context new_ctx = do
    ctx <- gets ctx
    modify $ \p -> p { ctx = new_ctx `merge_ctx` ctx }

with :: State POParam () -> POGen a -> POGen a
with f cmd = local (execState f) cmd

prefix_label lbl = do
        tag <- gets tag
        modify $ \p -> p { tag = tag ++ [lbl] }

prefix :: String -> State POParam ()
prefix lbl = prefix_label $ label lbl

named_hyps :: Map Label Expr -> State POParam ()
named_hyps hyps = do
        h <- gets named
        modify $ \p -> p { named = hyps `union` h }

nameless_hyps :: [Expr] -> State POParam ()
nameless_hyps hyps = do
        h <- gets nameless
        modify $ \p -> p { nameless = h ++ hyps }

variables :: Map String Var -> State POParam ()
variables vars = do
        ctx <- gets ctx
        let new_ctx = Context empty vars empty empty empty
        modify $ \p -> p 
            { ctx = new_ctx `merge_ctx` ctx }

eval_generator :: POGen () -> Map Label Sequent
eval_generator cmd = fromList $ snd $ evalRWS cmd empty_param ()
