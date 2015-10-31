module Logic.Proof.POGenerator 
    ( POGen, POGenT -- Logic.Proof.POGenerator.context
    , emit_goal
    , _context
    , POCtx
    , eval_generator, eval_generatorT
    , with, prefix_label, prefix, named_hyps
    , nameless_hyps, variables, emit_exist_goal
    , Logic.Proof.POGenerator.definitions
    , Logic.Proof.POGenerator.functions 
    , set_syntactic_props
    , existential, tracePOG )
where

    -- Modules
import Logic.Expr as E hiding ((.=))
import Logic.Expr.Existential
import Logic.Proof.Sequent as S

    -- Libraries
import Control.Arrow
import Control.Monad.Identity
import Control.Monad.Reader.Class
import Control.Monad.RWS
import Control.Monad.State
import Control.Lens hiding (Context)

import Data.List as L
import Data.Map as M hiding ( map )
import qualified Data.Map as M

import Utilities.Error
import Utilities.TH (mkCons)
import Utilities.Trace

import Text.Printf

data POParam = POP 
    { _pOParamContext :: Context
    , tag :: [Label]
    , _pOParamNameless :: [Expr]
    , _pOParamNamed :: Map Label Expr
    , _pOParamSynProp :: SyntacticProp
    }

makeFields ''POParam
mkCons ''POParam

empty_param :: POParam
empty_param = makePOParam empty_ctx

type POGen = POGenT Identity

newtype POGenT m a = POGen { runPOGen :: RWST POParam [(Label,Sequent)] () m a }

newtype POCtx a = POCtx { runPOCxt :: State POParam a }

instance Applicative POCtx where
    (<*>) = ap
    pure  = return

instance Functor POCtx where
    fmap = liftM

instance Monad POCtx where
    m >>= f = POCtx $ runPOCxt m >>= runPOCxt . f
    return  = POCtx . return

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

emit_exist_goal :: (HasExpr expr Expr, Monad m,Functor m) 
                => [Label] -> [Var] -> [expr] -> POGenT m ()
emit_exist_goal lbl vars es = with
        (mapM_ prefix_label lbl)
        $ forM_ clauses' $ \(vs,es) -> 
            unless (L.null es) $
                emit_goal (map (label . view name) vs) (zexists vs ztrue $ zall es)
    where
        clauses = partition_expr vars $ map getExpr es
        clauses' = M.toList $ M.fromListWith (++) clauses

existential :: (Monad m,Functor m) => [Var] -> POGenT m () -> POGenT m ()
existential [] cmd = cmd
existential vs (POGen cmd) = do
        let g (_, Sequent ctx _ h0 h1 goal) = do
                    vs <- f ctx
                    return $ zforall vs ztrue $ zall (h0 ++ M.elems h1) `zimplies` goal
            f (Context s vs fs def _) 
                | not $ M.null s = error "existential: cannot add sorts in existentials"
                -- |    not (M.null fs) 
                --   || not (M.null def) = error "existential: cannot introduce new function symbols in existentials"
                | otherwise = do
                    E.definitions %= merge def
                    E.functions %= merge fs
                    return $ M.elems vs
            -- f xs = [(tag, zexists vs ztrue $ zall $ map snd xs)]
        ss <- POGen 
            $ censor (const []) $ listen 
            $ local (const empty_param) cmd
        let (ss',st) = runState (mapM g $ snd ss) empty_ctx
        with (_context st) 
            $ emit_exist_goal [] vs ss'

emit_goal :: (Functor m, Monad m, HasExpr expr Expr) 
          => [Label] -> expr -> POGenT m ()
emit_goal lbl g = POGen $ do
    tag <- asks tag 
    po <- Sequent <$> view S.context 
                  <*> view synProp
                  <*> view nameless
                  <*> view named
                  <*> pure (getExpr g)
    tell [(composite_label $ tag ++ lbl, po)]

set_syntactic_props :: SyntacticProp -> POCtx ()
set_syntactic_props s = POCtx $ synProp .= s


_context :: Context -> POCtx ()
_context new_ctx = POCtx $ do
    S.context %= (new_ctx `merge_ctx`)

functions :: Map String Fun -> POCtx ()
functions new_funs = do
    _context $ Context M.empty M.empty new_funs M.empty M.empty

definitions :: Map String Def -> POCtx ()
definitions new_defs = POCtx $ do
    S.context.E.definitions .= new_defs

with :: Monad m => POCtx () -> POGenT m a -> POGenT m a
with f cmd = POGen $ local (execState $ runPOCxt f) $ runPOGen cmd

prefix_label :: Label -> POCtx ()
prefix_label lbl = POCtx $ do
        tag <- gets tag
        modify $ \p -> p { tag = tag ++ [lbl] }

prefix :: String -> POCtx ()
prefix lbl = prefix_label $ label lbl

named_hyps :: HasExpr expr Expr => Map Label expr -> POCtx ()
named_hyps hyps = POCtx $ do
        named %= M.union (M.map getExpr hyps)

nameless_hyps :: HasExpr expr Expr => [expr] -> POCtx ()
nameless_hyps hyps = POCtx $ do
        nameless %= (++ map getExpr hyps)

variables :: Map String Var -> POCtx ()
variables vars = POCtx $ do
        S.context.constants %= (vars `merge`)

eval_generator :: POGen () -> Map Label Sequent
eval_generator cmd = runIdentity $ eval_generatorT cmd
        -- fromList $ snd $ evalRWS (runPOGen cmd) empty_param ()

tracePOG :: Monad m => POGenT m () -> POGenT m ()
tracePOG (POGen cmd) = POGen $ do
    xs <- snd `liftM` listen cmd
    traceM $ unlines $ map (show . second (view goal)) xs

eval_generatorT :: Monad m => POGenT m () -> m (Map Label Sequent)
eval_generatorT cmd = liftM (fromListWithKey (\k _ _ -> ($myError) $ printf "%s\n" $ show k) . snd) $ evalRWST (runPOGen cmd) empty_param ()
