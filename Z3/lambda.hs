{-# LANGUAGE DeriveDataTypeable #-}
module Z3.Lambda where

    -- Modules
import UnitB.Theory

import Z3.Def
import Z3.Const

    -- Libraries
import Control.Applicative hiding ( empty, Const )
    -- for the operator <|>
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

can_bound_vars = map ( ("@@bound_var@@_" ++) . show ) [0..]

can_free_vars  = map ( ("@@free_var@@_" ++) . show ) [0..]

can_local_vars = map ( ("@@local_var@@_" ++) . show ) [0..]

data CanonicalRewriter = CR 
        {  local_gen :: [String]            -- locals
        ,  free_gen  :: [String]            -- bound var names
        ,  renaming :: Map String String -- rewrites
        ,  exprs  :: Map Expr Var
        }

free_vars :: Monad m => StateT CanonicalRewriter m ([Var],[Expr])
free_vars = gets g
    where
        g s = (map fst (f s), map snd (f s))
        f s = sort $ map swap $ toList $ exprs s

--        [String]            -- free_vars names
--        (Map Expr Var)      -- expressions containing no bound variables

--with_locals ls act = do
--        s@(CR lv ns) <- get
--        put (CR 
--            (drop (length ls) lv) 
----            bv
--            (union (fromList $ zip ls vs) ns))
--        e <- act
--        put (CR lb ns) 
--        return e

rename v@(Var n t) = do
        m <- gets renaming
        case M.lookup n m of
            Just new_name -> return (Var new_name t)
            Nothing       -> return v

expr_name :: Monad m => Expr -> StateT CanonicalRewriter m Var
expr_name e = do
        es <- gets exprs
        case M.lookup e es of
            Just v  -> return v
            Nothing -> do
                n:ns <- gets free_gen
                modify (\m -> m { free_gen = ns }) 
                let v = Var n $ type_of e
                modify (\m -> m { exprs = M.insert e v es } )
                return v

canonical :: [Var] -> Expr -> Expr -> (CanonicalLambda, [Expr])
canonical vs r t = do
        let { state = CR
            { local_gen = can_local_vars
            , free_gen  = can_free_vars
            , renaming  = fromList $ zip (map name vs) can_bound_vars 
            , exprs     = empty 
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
--        f (Word v)  = rename v
--        f e@(Binder _ vs r t) 
--                    = with_locals vs (rewriteM f e)
--        f e         = do
--                e' <- rewriteM f e
--                return e'
--error "not implemented"

type TermStore = Map CanonicalLambda String

get_lambda_term :: CanonicalLambda -> State TermStore String
get_lambda_term t = do
        m <- get
        case M.lookup t m of
            Just s -> return s
            Nothing -> do
                let n = size m
                let term = "@@lambda@@_" ++ show n
                put (M.insert t term m)
                return term 

type_ :: CanonicalLambda -> Type
type_ = error ""

--lambdas :: Expr -> State TermStore Expr
--lambdas expr = f expr
--    where
--        f (Binder Lambda vs r t) = do
--            r' <- f r
--            t' <- f t
--            let (can, param) = canonical vs r' t'
--            name <- get_lambda_term can
--            let array = Const [] name (ARRAY (type_of $ ztuple param) d
--            let select = zselect array (ztuple param)
--                -- careful here! we expect this expression to be type checked already 
--            return select
--        f e = rewriteM f e