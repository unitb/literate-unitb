{-# LANGUAGE FlexibleContexts, BangPatterns, ScopedTypeVariables #-}
module Document.Proof where

    -- Modules
import Document.Expression
import Document.Visitor

import Latex.Parser
import Latex.Scanner

import UnitB.AST
import UnitB.Calculation hiding ( context )
import UnitB.Genericity
import UnitB.PO
import UnitB.Operator

import Z3.Z3

    -- Libraries
import Control.Monad hiding ( guard )
import Control.Monad.Reader.Class
import Control.Monad.Trans
import Control.Monad.Trans.Either
import 
    Control.Monad.Trans.RWS hiding ( ask, tell, asks )
import qualified
    Control.Monad.Trans.RWS as RWS

import Data.Map hiding ( map, foldl )
import Data.List as L hiding ( union, insert, inits )
import qualified Data.Map as M

import Utilities.Format
import Utilities.Syntactic

context m = step_ctx m

data ProofStep = Step 
        (Map Label Expr)    -- assertions
        (Map Label Proof)   -- proofs of assertions
        (Map Label Expr)    -- assumptions
        (Maybe Expr)        -- new_goal
        (Maybe Proof)       -- main proof        

set_proof :: Monad m => Proof -> ProofStep -> EitherT [Error] m ProofStep
set_proof p (Step a b c d Nothing)      = return $ Step a b c d $ Just p
set_proof p (Step a b c d (Just _))     = left [("too many proofs",i,j)]
    where
        (i,j) = line_info p

set_goal :: (Monad m, MonadReader (Int,Int) m)
         => Expr -> ProofStep
         -> EitherT [Error] m ProofStep
set_goal g (Step a b c Nothing d)       = return $ Step a b c (Just g) d
set_goal g (Step a b c (Just _) d)  = do
        (i,j) <- ask
        left [("too many goals",i,j)]

add_assumption :: (Monad m, MonadReader (Int,Int) m)
               => Label -> Expr -> ProofStep
               -> EitherT [Error] m ProofStep
add_assumption lbl asm (Step a b c d e) 
    | lbl `member` c    = do
            (i,j) <- ask
            left [(format "an assumption {0} already exists" lbl,i,j)]
    | otherwise         = return $ Step a b (insert lbl asm c) d e

add_assert :: (Monad m, MonadReader (Int,Int) m)
           => Label -> Expr -> ProofStep
           -> EitherT [Error] m ProofStep
add_assert lbl asrt (Step a b c d e)    
    | lbl `member` a    = do
            (i,j) <- ask
            left [(format "an assertion {0} already exists" lbl,i,j)]
    | otherwise         = return $ Step (insert lbl asrt a) b c d e

add_proof :: (Monad m, MonadReader (Int,Int) m)
          => Label -> Proof -> ProofStep
          -> EitherT [Error] m ProofStep
add_proof lbl prf (Step a b c d e)      
    | lbl `member` b    = do
            (i,j) <- ask
            left [(format "a proof for assertion {0} already exists" lbl,i,j)]
    | otherwise         = return $ Step a (insert lbl prf b) c d e

empty_step = Step empty empty empty Nothing Nothing

find_assumptions :: Monad m
                 => Machine
                 -> [LatexDoc] 
                 -> ProofStep
                 -> RWST (Int,Int) [Error] s m ProofStep
find_assumptions m = visit_doc
        [   (   "calculation"
            ,   EnvBlock (\() xs proofs -> return proofs)
            )
        ,   (   "free:var"
            ,   EnvBlock (\(from :: Label,to :: Label,()) xs proofs -> return proofs)
            )
        ,   (   "by:cases"
            ,   EnvBlock (\() xs proofs -> return proofs)
            )
        ,   (   "by:parts"
            ,   EnvBlock (\() xs proofs -> return proofs)
            )
        ,   (   "subproof"
            ,   EnvBlock (\(lbl :: Label,()) xs proofs -> return proofs)
            )
        ] [ (   "\\assume"
            ,   CmdBlock $ \(lbl,formula,()) proofs -> do
                    expr <- get_assert m formula
                    add_assumption lbl expr proofs
            )
        ,   (   "\\assert"
            ,   CmdBlock $ \(lbl,formula,()) proofs -> do
                    expr <- get_assert m formula
                    add_assert lbl expr proofs
            )
        ,   (   "\\goal"
            ,   CmdBlock $ \(formula,()) proofs -> do
                    expr <- get_assert m formula
                    set_goal expr proofs
            )
        ]

find_proof_step :: Monad m
                => Map Label Expr 
                -> Machine
                -> [LatexDoc] 
                -> ProofStep
                -> RWST (Int,Int) [Error] s m ProofStep
find_proof_step hyps m = visit_doc
        [   (   "calculation"
            ,   EnvBlock $ \() xs proofs -> do
                    (i,j) <- lift $ ask
                    cc <- toEither $ parse_calc hyps m xs
                    case infer_goal cc of
                        Right cc_goal -> set_proof (ByCalc cc { goal = cc_goal }) proofs
                        Left msg      -> left [(format "type error: {0}" msg,i,j)]
            )
                -- TODO: make into a command
        ,   (   "free:var"
            ,   EnvBlock $ \(String from,String to,()) xs proofs -> do
                    (i,j) <- lift $ ask
                    p     <- collect_proof_step hyps m xs
                    set_proof (FreeGoal from to p (i,j)) proofs
            )
        ,   (   "by:cases"
            ,   EnvBlock (\() xs proofs -> do
                    (i,j) <- lift $ ask
                    cases <- toEither $ find_cases hyps m xs []
                    set_proof (ByCases (reverse cases) (i,j)) proofs )
            )
        ,   (   "by:parts"
            ,   EnvBlock (\() xs proofs -> do
                    (i,j) <- lift $ ask
                    cases <- toEither $ find_parts hyps m xs []
                    set_proof (ByParts (reverse cases) (i,j)) proofs )
            )
        ,   (   "subproof"
            ,   EnvBlock $ \(lbl,()) xs proofs -> do
                    p <- collect_proof_step hyps m xs
                    add_proof lbl p proofs
            )
        ] [ (   "\\easy"
            ,   CmdBlock $ \() proofs -> do
                    (i,j) <- lift $ ask        
                    set_proof (Easy (i,j)) proofs
            )
        ]

find_cases :: Monad m
           => Map Label Expr 
           -> Machine
           -> [LatexDoc] 
           -> [(Label,Expr,Proof)]
           -> RWST (Int,Int) [Error] s m [(Label,Expr,Proof)]
find_cases hyps m = visit_doc 
        [   (   "case"
            ,   EnvBlock $ \(lbl,formula,()) xs cases -> do
                    expr      <- get_assert m formula
                    p         <- collect_proof_step 
                            (insert lbl expr hyps) 
                            m xs
                    return ((lbl, expr, p):cases) 
            )
        ] []

find_parts :: Monad m
           => Map Label Expr 
           -> Machine
           -> [LatexDoc] 
           -> [(Expr,Proof)]
           -> RWST (Int,Int) [Error] s m [(Expr,Proof)]
find_parts hyps m = visit_doc 
        [   (   "part:a"
            ,   EnvBlock (\(formula,()) xs cases -> do
                    expr      <- get_assert m formula
                    p         <- collect_proof_step hyps m xs
                    return ((expr, p):cases))
            )
        ] []

collect_proof_step :: Monad m 
                   => Map Label Expr 
                   -> Machine 
                   -> [LatexDoc] 
                   -> EitherT [Error] (RWST (Int,Int) [Error] s m) Proof
collect_proof_step hyps m xs = do
        step@(Step asrt _ asm _ _) <- toEither $ find_assumptions m xs empty_step
        let hyps2 = asrt `union` asm `union` hyps
        step  <- toEither $ find_proof_step hyps2 m xs step
        (i,j) <- lift $ ask
        case step of
            Step assrt prfs asm ng (Just p) -> do
                let f k x = (x, prfs ! k)
                p <- if M.null assrt && M.null prfs
                    then return p
                    else if keysSet assrt == keysSet prfs
                    then return $ Assertion (M.mapWithKey f assrt) p (i,j)
                    else left [("assertion labels and proofs mismatch",i,j)]
                case ng of
                    Just g  -> return $ Assume asm g p (i,j)
                    Nothing -> 
                        if M.null asm 
                        then return p
                        else left [("assumptions must be accompanied by a new goal",i,j)]
            _   -> left [("expecting a single proof step",i,j)]         

parse_calc :: Monad m
           => Map Label Expr -> Machine 
           -> [LatexDoc]
           -> RWST (Int,Int) [Error] s m Calculation
parse_calc hyps m xs = 
    case find_cmd_arg 2 ["\\hint"] xs of
        Just (a,t,[b,c],d)    -> do
            xp <- fromEither ztrue $ get_expr m a
            li <- RWS.ask
            op <- fromEither Equal $ hoistEither $ read_tokens 
                    (do eat_space ; x <- oper ; eat_space ; return x) 
                    (concatMap flatten_li b) li
            hyp <- fromEither [] (do
                hs <- fmap (map (\(x,y) -> (label x,y))) $ hint c
                mapM (hoistEither . find hyps m) hs)
            r   <- parse_calc hyps m d
            return r { 
                first_step = xp,
                following  = (op,first_step r,hyp,line_info t):following r }
        Nothing         -> do
            li <- ask
            xp <- fromEither ztrue $ get_expr m xs
            return $ Calc (context m) ztrue xp [] li
    where
        f x = composite_label [_name m,label x]
        hint xs =
            case find_cmd_arg 1 ["\\ref","\\eqref"] xs of
                Just (a,_,[[Text [TextBlock b li]]],c)  -> do
                    xs <- hint c
                    return ((b,li):xs)
                Nothing         -> return []
        find :: Map Label Expr -> Machine -> (Label,(Int,Int)) -> Either [Error] Expr
        find hyps m (xs,(i,j)) = either Right Left (do
                err $ M.lookup xs $ hyps
                err $ M.lookup xs $ inv p
                err $ M.lookup xs $ inv_thm p
                err $ M.lookup xs $ inits m
                foldM f [err_msg] $ elems $ events m
                )
            where
                p = props m
                err (Just x) = Left x
                err Nothing  = Right [err_msg]
                err_msg      = ("reference to unknown predicate",i,j)
                f :: [Error] -> Event -> Either Expr [Error]
                f _ ev = do
                    err (do
                        x <- c_sched ev
                        M.lookup xs x)
                    err $ M.lookup xs $ guard ev
                    err $ M.lookup xs $ action ev
                                
get_expr :: (Monad m, MonadReader (Int,Int) m)
         => Machine -> [LatexDoc] 
         -> EitherT [Error] m Expr
get_expr m ys = do
        x  <- fmap normalize_generics $ parse_expr (context m) (concatMap flatten_li xs)
        li <- ask
        let (i,j) = if L.null xs
                    then li
                    else line_info xs
        unless (L.null $ ambiguities x) $ left 
            $ map (\x -> (format "type of {0} is ill-defined: {1}" x (type_of x),i,j))
                $ ambiguities x
        return x
    where
        xs    = drop_blank_text ys
        

get_assert :: (Monad m, MonadReader (Int,Int) m)
           => Machine -> [LatexDoc] 
           -> EitherT [Error] m Expr
get_assert m ys = do
        x <- parse_expr (context m) (concatMap flatten_li xs)
        li <- ask
        let (i,j) = if L.null xs
                    then li
                    else line_info xs
        x <- either (\x -> left [(x,i,j)]) (right . normalize_generics) $ zcast BOOL $ Right x
        unless (L.null $ ambiguities x) $ left 
            $ map (\x -> (format "type of {0} is ill-defined: {1}" x (type_of x),i,j))
                $ ambiguities x
        return x
    where
        xs    = drop_blank_text ys

get_evt_part :: (Monad m, MonadReader (Int,Int) m)
             => Machine -> Event
             -> [LatexDoc]
             -> EitherT [Error] m Expr
get_evt_part m e ys = do
        x <- parse_expr (            step_ctx m 
                         `merge_ctx` evt_live_ctx e
                         `merge_ctx` evt_saf_ctx  e)
                        (concatMap flatten_li xs)
        li <- ask
        let (i,j) = if L.null xs
                    then li
                    else line_info xs
        x <- either (\x -> left [(x,i,j)]) (right . normalize_generics) $ zcast BOOL $ Right x
        unless (L.null $ ambiguities x) $ left 
            $ map (\x -> (format "type of {0} is ill-defined: {1}" x (type_of x),i,j))
                $ ambiguities x
        return x
    where
        xs    = drop_blank_text ys
