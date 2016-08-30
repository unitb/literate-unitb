{-# LANGUAGE DataKinds, ViewPatterns #-}
module Logic.Proof.Lambda 
    ( delambdify
    , CanonicalLambda ( .. )
    , canonical
    , Role(..) )
where

    -- Modules
import Logic.Expr   hiding ( rename, free_vars )
import Logic.Expr.Prism
import Logic.Proof.Sequent

    -- Libraries
import Control.DeepSeq
import Control.Lens hiding (Context,Context',rewriteM)
import Control.Monad.State

import Data.Default
import Data.List as L hiding (union)
import Data.Map.Class  as M hiding (filter)
import qualified Data.Set as S
import Data.Tuple
import qualified Data.Traversable as T
import Data.Typeable

import GHC.Generics

import Utilities.Table

data CanonicalLambda = CL 
        [Var'] [Var'] -- free vars, bound vars
        Expr'         -- range or term
        (Maybe Type)  -- return type, nothing if the type is boolean because of range
    deriving (Eq, Ord, Typeable, Show, Generic)

arg_type :: CanonicalLambda -> [Type]
arg_type (CL vs _ _ _) = L.map var_type vs

return_type :: CanonicalLambda -> Type
return_type (CL _ bv _ rt) = 
        case rt of
            Just rt ->
                (array tuple rt)
            Nothing -> set_type tuple
    where
        tuple = ztuple_type $ L.map var_type bv

can_bound_vars :: () -> [InternalName]
can_bound_vars _ = L.map (reserved "bv") [0..]

can_free_vars :: () -> [InternalName]
can_free_vars _ = L.map (reserved "fv") [0..]

can_local_vars :: () -> [InternalName]
can_local_vars _ = L.map (reserved "lv") [0..]

data CanonicalRewriter = CR 
        {  local_gen :: [InternalName]            -- locals
        ,  free_gen  :: [InternalName]            -- bound var names
        ,  renaming :: Table InternalName InternalName      -- rewrites
        ,  exprs  :: [(Expr', Var')]
        }

free_vars :: Monad m => StateT CanonicalRewriter m ([Var'],[Expr'])
free_vars = gets g
    where
        g s = (L.map fst (f s), L.map snd (f s))
        f s = sort $ L.map swap $ exprs s

rename :: MonadState CanonicalRewriter m
       => (AbsVar InternalName Type)
       -> m (AbsVar InternalName Type)
rename v@(Var n t) = do
        m <- gets renaming
        case M.lookup n m of
            Just new_name -> return (Var new_name t)
            Nothing       -> return $ translate v

expr_name :: Monad m => Expr' -> StateT CanonicalRewriter m Var'
expr_name e = do
            n:ns <- gets free_gen
            modify (\m -> m { free_gen = ns }) 
            let v = Var n $ type_of e
            es <- gets exprs
            modify (\m -> m { exprs = (e, v):es } )
            return v

data Role = Range | Term

canonical :: Role -> [Var'] -> Expr' -> (CanonicalLambda, [Expr'])
canonical role vs e = do
        let { state = CR
                { local_gen = can_local_vars ()
                , free_gen  = can_free_vars ()
                , renaming  = fromList $ zip (L.map (view name) vs) (can_bound_vars ())
                , exprs     = [] 
                } }
        evalState (do
                e'      <- findFreeVars (S.fromList vs) e
                us      <- forM vs rename
                (fv,es) <- free_vars
                let t' = case role of
                            Term ->  Just $ type_of e'
                            Range -> Nothing
                return (CL fv us e' t', es)) 
            state

findFreeVars :: S.Set Var' -> Expr' -> State CanonicalRewriter Expr'
findFreeVars ls e
    | S.null (used_var e `S.intersection` ls) 
                = Word <$> expr_name e
    | otherwise = do
        case e of
            Binder q vs r t et -> do
                let dums = S.fromList vs `S.union` ls
                ls  <- gets local_gen
                ren <- gets renaming
                modify (\m -> m 
                    { local_gen = take (length vs) ls
                    , renaming  = union 
                        (fromList $ zip (L.map (view name) vs) ls) 
                        ren } )
                r'  <- findFreeVars dums r
                t'  <- findFreeVars dums t
                us  <- forM vs rename
                modify (\m -> m 
                    { local_gen = ls
                    , renaming  = ren } )
                return (binder q us r' t' et)
            Word v          -> 
                Word <$> rename v
            _               ->
                rewriteM (findFreeVars ls) e

type TermStore = Map CanonicalLambda (AbsFun InternalName Type)

get_lambda_term :: Monad m => CanonicalLambda -> StateT TermStore m InternalFun
get_lambda_term t@(CL vs us e t') = do
        m <- get
        case M.lookup t m of
            Just s -> return s
            Nothing -> do
                case t' of
                  Just _
                    | L.map Word vs == [e] -> return const_fun
                    | L.null vs && 
                        ztuple (L.map Word us) == e -> return ident_fun
                  _ -> do
                    let n = size m
                        term = mk_fun [] 
                                (reserved "lambda" n :: InternalName) 
                                (arg_type t) (return_type t)
                    put (M.insert t term m)
                    return term 

lambda_decl :: Monad m => StateT TermStore m Context'
lambda_decl = do
            xs <- gets toList 
            return $ def & functions .~ M.mapKeys asInternal (symbol_table $ L.map snd xs)

lambda_def :: Monad m => StateT TermStore m [Expr']
lambda_def = do
            xs <- gets toList
            forM xs $ \(CL vs us e t,fun) -> do
                let sel :: ExprPG InternalName Type FOQuantifier
                    sel = check_type fun $ L.map (Right . Word) vs
                    tuple = Right $ ztuple $ L.map Word us
                    app = case t of
                            Just _ -> zselect sel tuple
                            Nothing -> tuple `zelem` sel
                    eq :: ExprPG InternalName Type FOQuantifier
                    eq  = mzeq app (Right e)
                    res :: Expr'
                    res = ($typeCheck) $ mzforall (vs ++ us) mztrue eq
                return $ res

delambdify :: Sequent -> Sequent'
delambdify po = -- (Sequent ctx asm hyps goal) = 
        evalState (do
            asm'  <- forM (po^.nameless) lambdas
            hyps' <- T.forM (po^.named) lambdas
            goal' <- lambdas $ po^.goal
            let Context ss vs fs _ dd = po^.context
            ds' <- T.forM (po^.definitions) $ \(Def tp fn arg rt e) -> do
                    makeDef tp (asInternal fn) 
                               (L.map translate arg) rt
                        <$> lambdas e
            defs  <- lambda_def
            decl  <- lambda_decl
            let ctx' = Context ss 
                            (symbol_table $ M.map translate vs) 
                            (M.mapKeys asInternal $ fs & traverse.namesOf %~ asInternal)
                            (M.mapKeys asInternal ds')
                            (symbol_table $ M.map translate dd) 
                ctx' :: Context'
            return $ Sequent 
                (po^.timeout) 
                (po^.resource) 
                (            ctx' 
                 `merge_ctx` decl :: Context') 
                (po^.syntacticThm)
                (asm' ++ defs :: [Expr'])
                (hyps' :: Table Label Expr')
                (goal' :: Expr')
            ) empty

make_canonical :: Role -> [Var'] -> Expr' 
               -> State TermStore ExprP'
make_canonical Range vs [fun| (elem $var $set) |]
       |   L.map Word vs == [var]
        && not (any (`S.member` used_var set) vs) = 
            return $ Right set
make_canonical role vars e = do
        let (can,param) = canonical role vars e
        fun <- get_lambda_term can
        return $ check_type fun $ L.map Right param

lambdas :: Expr -> State TermStore Expr'
lambdas (Binder (UDQuant fn _ _ _) vs r t _) = do
    r' <- lambdas r
    t' <- lambdas t
    let vs' = L.map translate vs
    select_r <- make_canonical Range vs' r'
    select_t <- make_canonical Term vs' t'
    let select = ($typeCheck) $ check_type (fn & namesOf %~ asInternal) [select_r,select_t]
        -- careful here! we expect this expression to be type checked already 
    return select
lambdas (Binder Forall vs r t et) = do
    r' <- lambdas r
    t' <- lambdas t
    return $ binder FOForall (L.map translate vs) r' t' et
lambdas (Binder Exists vs r t et) = do
    r' <- lambdas r
    t' <- lambdas t
    return $ binder FOExists (L.map translate vs) r' t' et
lambdas (Word v) = return (Word $ translate v)
lambdas (Lit v t) = return (Lit v t)
lambdas (FunApp fun args) = do
    args' <- mapM lambdas args
    return $ funApp (fun & namesOf %~ asInternal) args'
lambdas (Cast e t) = (`Cast` t) <$> lambdas e
lambdas (Lift e t) = (`Lift` t) <$> lambdas e
lambdas (Record e) = Record <$> traverseRecExpr lambdas e

instance NFData CanonicalLambda where
