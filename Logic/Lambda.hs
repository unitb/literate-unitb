{-# LANGUAGE DeriveDataTypeable, FlexibleContexts #-}
module Logic.Lambda 
    ( delambdify
    , CanonicalLambda ( .. )
    , canonical )
where

    -- Modules
import Logic.Expr   hiding ( rename, free_vars )
import Logic.Proof

    -- Libraries
import Control.Applicative ((<$>))
import Control.Monad.State

import Data.List hiding (union)
import Data.Map as M hiding (map,filter,foldl)
import qualified Data.Set as S
import Data.Traversable (traverse)
import Data.Tuple
import Data.Typeable

data CanonicalLambda = CL 
        [Var] [Var]   -- free vars, bound vars
        Expr'  Expr'  -- range, term
        Type          -- return type
    deriving (Eq, Ord, Typeable, Show)

arg_type :: CanonicalLambda -> [Type]
arg_type (CL vs _ _ _ _) = map var_type vs

return_type :: CanonicalLambda -> Type
return_type (CL _ bv _ _ rt) = 
        (fun_type (ztuple_type $ map var_type bv) rt)

can_bound_vars :: [String]
can_bound_vars = map ( ("@@bv@@_" ++) . show ) [0..]

can_free_vars :: [String]
can_free_vars  = map ( ("@@fv@@_" ++) . show ) [0..]

can_local_vars :: [String]
can_local_vars = map ( ("@@lv@@_" ++) . show ) [0..]

data CanonicalRewriter = CR 
        {  local_gen :: [String]            -- locals
        ,  free_gen  :: [String]            -- bound var names
        ,  renaming :: Map String String    -- rewrites
        ,  exprs  :: [(Expr', Var)]
        }

free_vars :: Monad m => StateT CanonicalRewriter m ([Var],[Expr'])
free_vars = gets g
    where
        g s = (map fst (f s), map snd (f s))
        f s = sort $ map swap $ exprs s

rename :: MonadState CanonicalRewriter m
       => Var -> m Var
rename v@(Var n t) = do
        m <- gets renaming
        case M.lookup n m of
            Just new_name -> return (Var new_name t)
            Nothing       -> return v

expr_name :: Monad m => Expr' -> StateT CanonicalRewriter m Var
expr_name e = do
            n:ns <- gets free_gen
            modify (\m -> m { free_gen = ns }) 
            let v = Var n $ type_of e
            es <- gets exprs
            modify (\m -> m { exprs = (e, v):es } )
            return v

canonical :: [Var] -> Expr' -> Expr' -> (CanonicalLambda, [Expr'])
canonical vs r t = do
        let { state = CR
            { local_gen = can_local_vars
            , free_gen  = can_free_vars
            , renaming  = fromList $ zip (map name vs) can_bound_vars 
            , exprs     = [] 
            } }
        evalState (do
            r'      <- findFreeVars (S.fromList vs) r
            t'      <- findFreeVars (S.fromList vs) t
            us      <- forM vs rename
            (fv,es) <- free_vars
            return (CL fv us r' t' $ type_of t', es)) 
            state

findFreeVars :: S.Set Var -> Expr' -> State CanonicalRewriter Expr'
findFreeVars ls e
    | S.null (used_var e `S.intersection` ls) 
                = do
            v <- expr_name e
            return (Word v)
    | otherwise = do
        case e of
            Binder q vs r t -> do
                let dums = S.fromList vs `S.union` ls
                ls  <- gets local_gen
                ren <- gets renaming
                modify (\m -> m 
                    { local_gen = take (length vs) ls
                    , renaming  = union 
                        (fromList $ zip (map name vs) ls) 
                        ren } )
                r'  <- findFreeVars dums r
                t'  <- findFreeVars dums t
                us  <- forM vs rename
                modify (\m -> m 
                    { local_gen = ls
                    , renaming  = ren } )
                return (Binder q us r' t')
            Word v          -> 
                Word <$> rename v
            _               ->
                rewriteM (findFreeVars ls) e

type TermStore = Map CanonicalLambda Fun

get_lambda_term :: Monad m => CanonicalLambda -> StateT TermStore m Fun
get_lambda_term t = do
        m <- get
        case M.lookup t m of
            Just s -> return s
            Nothing -> do
                let n = size m
                let term = Fun [] ("@@lambda@@_" ++ show n) (arg_type t) (return_type t)
                put (M.insert t term m)
                return term 

lambda_decl :: Monad m => StateT TermStore m (AbsContext Type FOQuantifier)
lambda_decl = do
            xs <- gets toList 
            return $ Context empty empty (symbol_table $ map snd xs) empty empty

lambda_def :: Monad m => StateT TermStore m [Expr']
lambda_def = do
            xs <- gets toList
            forM xs $ \(CL vs us r t _,fun) -> do
                let sel :: ExprPG Type FOQuantifier
                    sel = check_type fun $ map (Right . Word) vs
                    app = zselect sel (Right $ ztuple $ map Word us)
                    eq :: ExprPG Type FOQuantifier
                    eq  = mzeq app $ zite (Right r) (zjust $ Right t) znothing
                    res :: Expr'
                    res = fromJust $ mzforall (vs ++ us) mztrue eq
                return $ res

delambdify :: Sequent -> AbsSequent Type FOQuantifier
delambdify (Sequent ctx asm hyps goal) = 
        evalState (do
            asm'   <- forM asm lambdas
            hyps'  <- fromList `liftM` forM (toList hyps) (
                \(lbl,xp) -> do
                    xp <- lambdas xp
                    return (lbl,xp)
                )
            goal' <- lambdas goal
            defs  <- lambda_def
            decl  <- lambda_decl
            let Context ss vs fs ds dd = ctx
            ds' <- traverse (\(Def tp fn arg rt e) -> do
                    e' <- lambdas e
                    return $ Def tp fn arg rt e'
                ) ds
            let ctx' = Context ss vs fs ds' dd
            return $ Sequent
                (            ctx' 
                 `merge_ctx` decl) 
                (asm' ++ defs)
                hyps'
                goal'
            ) empty

lambdas :: Expr -> State TermStore Expr'
lambdas (Binder Lambda vs r t) = do
    r' <- lambdas r
    t' <- lambdas t
    let (can, param) = canonical vs r' t'
    fun <- get_lambda_term can
    let select = fromJust (check_type fun $ map Right param)
        -- careful here! we expect this expression to be type checked already 
    return select
lambdas (Binder Forall vs r t) = do
    r' <- lambdas r
    t' <- lambdas t
    return $ Binder FOForall vs r' t'
lambdas (Binder Exists vs r t) = do
    r' <- lambdas r
    t' <- lambdas t
    return $ Binder FOExists vs r' t'
lambdas (Word v) = return (Word v)
lambdas (Const v t) = return (Const v t)
lambdas (FunApp fun args) = do
    args' <- mapM lambdas args
    return $ FunApp fun args'
lambdas (Cast e t) = (`Cast` t) <$> lambdas e
lambdas (Lift e t) = (`Lift` t) <$> lambdas e
