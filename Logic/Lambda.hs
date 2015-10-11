{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, TemplateHaskell #-}
module Logic.Lambda 
    ( delambdify
    , CanonicalLambda ( .. )
    , canonical
    , Role(..) )
where

    -- Modules
import Logic.Expr   hiding ( rename, free_vars )
import Logic.Proof

import Theories.SetTheory

    -- Libraries
import Control.Applicative ((<$>))
import Control.Lens hiding (Context,Context',rewriteM,Const)
import Control.Monad.State

import Data.List as L hiding (union)
import Data.Map  as M hiding (map,filter,foldl)
import qualified Data.Set as S
import Data.Tuple
import Data.Typeable

data CanonicalLambda = CL 
        [Var] [Var]   -- free vars, bound vars
        Expr'         -- range or term
        (Maybe Type)  -- return type, nothing if the type is boolean because of range
    deriving (Eq, Ord, Typeable, Show)

arg_type :: CanonicalLambda -> [Type]
arg_type (CL vs _ _ _) = map var_type vs

return_type :: CanonicalLambda -> Type
return_type (CL _ bv _ rt) = 
        case rt of
            Just rt ->
                (array tuple rt)
            Nothing -> set_type tuple
    where
        tuple = ztuple_type $ map var_type bv

can_bound_vars :: () -> [String]
can_bound_vars _ = map ( ("@@bv@@_" ++) . show ) [0..]

can_free_vars :: () -> [String]
can_free_vars _ = map ( ("@@fv@@_" ++) . show ) [0..]

can_local_vars :: () -> [String]
can_local_vars _ = map ( ("@@lv@@_" ++) . show ) [0..]

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

data Role = Range | Term

canonical :: Role -> [Var] -> Expr' -> (CanonicalLambda, [Expr'])
canonical role vs e = do
        let { state = CR
            { local_gen = can_local_vars ()
            , free_gen  = can_free_vars ()
            , renaming  = fromList $ zip (map (view name) vs) (can_bound_vars ())
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

findFreeVars :: S.Set Var -> Expr' -> State CanonicalRewriter Expr'
findFreeVars ls e
    | S.null (used_var e `S.intersection` ls) 
                = do
            v <- expr_name e
            return (Word v)
    | otherwise = do
        case e of
            Binder q vs r t et -> do
                let dums = S.fromList vs `S.union` ls
                ls  <- gets local_gen
                ren <- gets renaming
                modify (\m -> m 
                    { local_gen = take (length vs) ls
                    , renaming  = union 
                        (fromList $ zip (map (view name) vs) ls) 
                        ren } )
                r'  <- findFreeVars dums r
                t'  <- findFreeVars dums t
                us  <- forM vs rename
                modify (\m -> m 
                    { local_gen = ls
                    , renaming  = ren } )
                return (Binder q us r' t' et)
            Word v          -> 
                Word <$> rename v
            _               ->
                rewriteM (findFreeVars ls) e

type TermStore = Map CanonicalLambda Fun

get_lambda_term :: Monad m => CanonicalLambda -> StateT TermStore m Fun
get_lambda_term t@(CL vs us e t') = do
        m <- get
        case M.lookup t m of
            Just s -> return s
            Nothing -> do
                case t' of
                  Just _
                    | map Word vs == [e] -> return const_fun
                    | L.null vs && 
                        ztuple (map Word us) == e -> return ident_fun
                  _ -> do
                    let n = size m
                        term = mk_fun [] ("@@lambda@@_" ++ show n) (arg_type t) (return_type t)
                    put (M.insert t term m)
                    return term 

lambda_decl :: Monad m => StateT TermStore m Context'
lambda_decl = do
            xs <- gets toList 
            return $ Context empty empty (symbol_table $ map snd xs) empty empty

lambda_def :: Monad m => StateT TermStore m [Expr']
lambda_def = do
            xs <- gets toList
            forM xs $ \(CL vs us e t,fun) -> do
                let sel :: ExprPG Type FOQuantifier
                    sel = check_type fun $ map (Right . Word) vs
                    tuple = Right $ ztuple $ map Word us
                    app = case t of
                            Just _ -> zselect sel tuple
                            Nothing -> tuple `zelem` sel
                    eq :: ExprPG Type FOQuantifier
                    eq  = mzeq app (Right e)
                    res :: Expr'
                    res = ($typeCheck) $ mzforall (vs ++ us) mztrue eq
                return $ res

delambdify :: Sequent -> Sequent'
delambdify po = -- (Sequent ctx asm hyps goal) = 
        evalState (do
            asm'   <- forM (po^.nameless) lambdas
            hyps'  <- fromList `liftM` forM (toList $ po^.named) (
                \(lbl,xp) -> do
                    xp <- lambdas xp
                    return (lbl,xp)
                )
            goal' <- lambdas $ po^.goal
            defs  <- lambda_def
            decl  <- lambda_decl
            let Context ss vs fs _ dd = po^.context
            ds' <- traverse (\(Def tp fn arg rt e) -> do
                    e' <- lambdas e
                    return $ Def tp fn arg rt e'
                ) (po^.definitions)
            let ctx' = Context ss vs fs ds' dd
            return $ Sequent
                (            ctx' 
                 `merge_ctx` decl) 
                (po^.syntacticThm)
                (asm' ++ defs)
                hyps'
                goal'
            ) empty

lambdas :: Expr -> State TermStore Expr'
lambdas (Binder (UDQuant fun _ _ _) vs r t _) = do
    r' <- lambdas r
    t' <- lambdas t
    let (can_r, param_r) = canonical Range vs r'
        (can_t, param_t) = canonical Term vs t'
    fun_r <- get_lambda_term can_r
    fun_t <- get_lambda_term can_t
    let select_r = check_type fun_r $ map Right param_r
        select_t = check_type fun_t $ map Right param_t
        select = ($typeCheck) $ check_type fun [select_r,select_t]
        -- careful here! we expect this expression to be type checked already 
    return select
lambdas (Binder Forall vs r t et) = do
    r' <- lambdas r
    t' <- lambdas t
    return $ Binder FOForall vs r' t' et
lambdas (Binder Exists vs r t et) = do
    r' <- lambdas r
    t' <- lambdas t
    return $ Binder FOExists vs r' t' et
lambdas (Word v) = return (Word v)
lambdas (Const v t) = return (Const v t)
lambdas (FunApp fun args) = do
    args' <- mapM lambdas args
    return $ FunApp fun args'
lambdas (Cast e t) = (`Cast` t) <$> lambdas e
lambdas (Lift e t) = (`Lift` t) <$> lambdas e
