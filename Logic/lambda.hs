{-# LANGUAGE DeriveDataTypeable, FlexibleContexts #-}
module Logic.Lambda 
    ( delambdify
    , CanonicalLambda ( .. )
    , canonical )
where

    -- Modules
import Logic.Classes
import Logic.Const
import Logic.Expr
import Logic.Genericity
import Logic.Label
import Logic.Sequent
import Logic.Type

    -- Libraries
import Control.Monad.State

import Data.List hiding (union)
import Data.Map as M hiding (map,filter,foldl)
import qualified Data.Set as S
import Data.Tuple
import Data.Typeable

data CanonicalLambda = CL 
        [Var] [Var] -- free vars, bound vars
        Expr  Expr  -- range, term
        Type        -- return type
    deriving (Eq, Ord, Typeable, Show)

arg_type :: CanonicalLambda -> [Type]
arg_type (CL vs _ _ _ _) = map (type_of . Word) vs

return_type :: CanonicalLambda -> Type
return_type (CL _ bv _ _ rt) = 
        (array (type_of $ ztuple $ map Word bv) $ maybe_type rt)

can_bound_vars :: [String]
can_bound_vars = map ( ("@@bv@@_" ++) . show ) [0..]

can_free_vars :: [String]
can_free_vars  = map ( ("@@fv@@_" ++) . show ) [0..]

can_local_vars :: [String]
can_local_vars = map ( ("@@lv@@_" ++) . show ) [0..]

data CanonicalRewriter = CR 
        {  local_gen :: [String]            -- locals
        ,  free_gen  :: [String]            -- bound var names
        ,  renaming :: Map String String -- rewrites
        ,  exprs  :: [(Expr, Var)]
        }

free_vars :: Monad m => StateT CanonicalRewriter m ([Var],[Expr])
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

expr_name :: Monad m => Expr -> StateT CanonicalRewriter m Var
expr_name e = do
            n:ns <- gets free_gen
            modify (\m -> m { free_gen = ns }) 
            let v = Var n $ type_of e
            es <- gets exprs
            modify (\m -> m { exprs = (e, v):es } )
            return v

canonical :: [Var] -> Expr -> Expr -> (CanonicalLambda, [Expr])
canonical vs r t = do
        let { state = CR
            { local_gen = can_local_vars
            , free_gen  = can_free_vars
            , renaming  = fromList $ zip (map name vs) can_bound_vars 
            , exprs     = [] 
            } }
        evalState (do
            r'      <- f (S.fromList vs) r
            t'      <- f (S.fromList vs) t
            us      <- forM vs rename
            (fv,es) <- free_vars
            return (CL fv us r' t' $ type_of t', es)) 
            state
    where
--        ls = 
--        f = error ""
        f ls e
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
                        r'  <- f dums r
                        t'  <- f dums t
                        us  <- forM vs rename
                        modify (\m -> m 
                            { local_gen = ls
                            , renaming  = ren } )
                        return (Binder q us r' t')
                    Word v          -> 
                        Word `liftM` rename v
                    _               ->
                        rewriteM (f ls) e

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

lambda_decl :: Monad m => StateT TermStore m Context
lambda_decl = do
            xs <- gets toList 
            return $ Context empty empty (symbol_table $ map snd xs) empty empty

lambda_def :: Monad m => StateT TermStore m [Expr]
lambda_def = do
            xs <- gets toList
            forM xs $ \(CL vs us r t _,fun) -> do
                let sel = check_type fun $ map (Right . Word) vs
                let app = zselect sel (Right $ ztuple $ map Word us)
                let eq  = mzeq app $ zite (Right r) (zjust $ Right t) znothing
                let res = fromJust $ mzforall (vs ++ us) mztrue eq
                return $ res

delambdify :: Sequent -> Sequent
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
            return $ Sequent
                (            ctx 
                 `merge_ctx` decl) 
                (defs ++ asm')
                hyps'
                goal'
            ) empty

lambdas :: Monad m => Expr -> StateT TermStore m Expr
lambdas expr = f expr
    where
        f (Binder Lambda vs r t) = do
            r' <- f r
            t' <- f t
            let (can, param) = canonical vs r' t'
            fun <- get_lambda_term can
--            let array = Const [] name (array_type can)
            let select = fromJust (check_type fun $ map Right param)
--                FunApp fun (Right $ ztuple param)
                -- careful here! we expect this expression to be type checked already 
            return select
        f e = rewriteM f e