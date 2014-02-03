{-# LANGUAGE FlexibleContexts, BangPatterns, ScopedTypeVariables #-}
module Document.Proof where

    -- Modules
import Document.Expression
import Document.Visitor

import Latex.Parser

import UnitB.AST
import UnitB.PO

import Logic.Calculation hiding ( context )
import Logic.Expr
import Logic.Const
import Logic.Genericity
import Logic.Operator

    -- Libraries
import           Control.Monad hiding ( guard )
import           Control.Monad.Reader.Class
import           Control.Monad.Trans
import           Control.Monad.Trans.Either
import           Control.Monad.Trans.RWS hiding ( ask, tell, asks )
import qualified Control.Monad.Trans.RWS as RWS

import           Data.Map hiding ( map, foldl )
import qualified Data.Map as M
import           Data.Monoid (Monoid)
import           Data.List as L hiding ( union, insert, inits )
import qualified Data.Set as S

import Utilities.Format
import Utilities.Syntactic
import Utilities.Trace

context m = step_ctx m `merge_ctx` theory_ctx S.empty (theory m)

data ProofStep = Step 
        (Map Label Expr)    -- assertions
        (Map Label Proof)   -- proofs of assertions
        (Map Label Expr)    -- assumptions
        (Maybe Expr)        -- new_goal
        (Maybe Proof)       -- main proof        

set_proof :: Monad m => Proof -> ProofStep -> EitherT [Error] m ProofStep
set_proof p (Step a b c d Nothing)      = return $ Step a b c d $ Just p
set_proof p (Step _ _ _ _ (Just _))     = left [Error "too many proofs" li]
    where
        li = line_info p

set_goal :: (Monad m, MonadReader LineInfo m)
         => Expr -> ProofStep
         -> EitherT [Error] m ProofStep
set_goal g (Step a b c Nothing d)       = return $ Step a b c (Just g) d
set_goal _ (Step _ _ _ (Just _) _)  = do
        li    <- lift $ ask
        left [Error ("too many goals") li]

add_assumption :: (Monad m, MonadReader LineInfo m)
               => Label -> Expr -> ProofStep
               -> EitherT [Error] m ProofStep
add_assumption lbl asm (Step a b c d e) 
    | lbl `member` c    = do
            li    <- lift $ ask
            left [Error (format "an assumption {0} already exists" lbl) li]
    | otherwise         = return $ Step a b (insert lbl asm c) d e

add_assert :: (Monad m, MonadReader LineInfo m)
           => Label -> Expr -> ProofStep
           -> EitherT [Error] m ProofStep
add_assert lbl asrt (Step a b c d e)    
    | lbl `member` a    = do
            li    <- lift $ ask
            left [Error (format "an assertion {0} already exists" lbl) li]
    | otherwise         = return $ Step (insert lbl asrt a) b c d e

add_proof :: (Monad m, MonadReader LineInfo m)
          => Label -> Proof -> ProofStep
          -> EitherT [Error] m ProofStep
add_proof lbl prf (Step a b c d e)      
    | lbl `member` b    = do
            li    <- lift $ ask
            left [Error (format "a proof for assertion {0} already exists" lbl) li]
    | otherwise         = return $ Step a (insert lbl prf b) c d e

empty_step = Step empty empty empty Nothing Nothing

find_assumptions :: Monad m
                 => Machine
                 -> [LatexDoc] 
                 -> ProofStep
                 -> RWST LineInfo [Error] System m ProofStep
find_assumptions m = visit_doc
        [   (   "calculation"
            ,   EnvBlock $ \() _ proofs -> return proofs
            )
        ,   (   "free:var"
            ,   EnvBlock $ \(_ :: Label,_ :: Label,()) _ proofs -> return proofs
            )
        ,   (   "by:cases"
            ,   EnvBlock $ \() _ proofs -> return proofs
            )
        ,   (   "by:parts"
            ,   EnvBlock $ \() _ proofs -> return proofs
            )
        ,   (   "subproof"
            ,   EnvBlock $ \(_ :: Label,()) _ proofs -> return proofs
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
                -> RWST LineInfo [Error] System m ProofStep
find_proof_step hyps m = visit_doc
        [   (   "calculation"
            ,   EnvBlock $ \() xs proofs -> do
                    li <- lift $ ask
                    cc <- toEither $ parse_calc hyps m xs
                    case infer_goal cc (all_notation m) of
                        Right cc_goal -> set_proof (ByCalc cc { goal = cc_goal }) proofs
                        Left msg      -> left [Error (format "type error: {0}" msg) li]
            )
                -- TODO: make into a command
        ,   (   "free:var"
            ,   EnvBlock $ \(String from,String to,()) xs proofs -> do
                    li    <- lift $ ask
                    p     <- collect_proof_step hyps m xs
                    set_proof (FreeGoal from to p li) proofs
            )
        ,   (   "by:cases"
            ,   EnvBlock (\() xs proofs -> do
                    li    <- lift $ ask
                    cases <- toEither $ find_cases hyps m xs []
                    set_proof (ByCases (reverse cases) li) proofs )
            )
        ,   (   "by:parts"
            ,   EnvBlock (\() xs proofs -> do
                    li    <- lift $ ask
                    cases <- toEither $ find_parts hyps m xs []
                    set_proof (ByParts (reverse cases) li) proofs )
            )
        ,   (   "subproof"
            ,   EnvBlock $ \(lbl,()) xs proofs -> do
                    p <- collect_proof_step hyps m xs
                    add_proof lbl p proofs
            )
        ] [ (   "\\easy"
            ,   CmdBlock $ \() proofs -> do
                    li <- lift $ ask        
                    set_proof (Easy li) proofs
            )
        ]

find_cases :: Monad m
           => Map Label Expr 
           -> Machine
           -> [LatexDoc] 
           -> [(Label,Expr,Proof)]
           -> RWST LineInfo [Error] System m [(Label,Expr,Proof)]
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
           -> RWST LineInfo [Error] System m [(Expr,Proof)]
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
                   -> EitherT [Error] (RWST LineInfo [Error] System m) Proof
collect_proof_step hyps m xs = do
        step@(Step asrt _ asm _ _) <- toEither $ find_assumptions m xs empty_step
        let hyps2 = asrt `union` asm `union` hyps
        step <- toEither $ find_proof_step hyps2 m xs step
        li   <- lift $ ask
        case step of
            Step assrt prfs asm ng (Just p) -> do
                let f k x = (x, prfs ! k)
                p <- if M.null assrt && M.null prfs
                    then return p
                    else if keysSet assrt == keysSet prfs
                    then return $ Assertion (M.mapWithKey f assrt) p li
                    else left [Error "assertion labels and proofs mismatch" li]
                case ng of
                    Just g  -> return $ Assume asm g p li
                    Nothing -> 
                        if M.null asm 
                        then return p
                        else left [Error "assumptions must be accompanied by a new goal" li]
            _   -> left [Error "expecting a single proof step" li]         

hint :: Monad m
     => [LatexDoc] 
     -> [(Label, LineInfo)]
     -> RWST LineInfo [Error] s m [(Label, LineInfo)] 
hint = visit_doc []
        [ ( "\\ref", CmdBlock f ), ( "\\eqref", CmdBlock f ) ]
    where
        f (b,()) xs = do
            li <- lift $ ask 
            return $ (b,li):xs

parse_calc :: Monad m
           => Map Label Expr 
           -> Machine 
           -> [LatexDoc]
           -> RWST LineInfo [Error] System m Calculation
parse_calc hyps m xs = 
    case find_cmd_arg 2 ["\\hint"] xs of
        Just (a,t,[b,c],d)    -> do
            xp <- fromEither ztrue $ get_expr m a
            op <- fromEither equal $ parse_oper 
                    (context m)
                    (all_notation m)
                    (concatMap flatten_li b) 
            hs <- hint c []
            hyp <- fromEither [] (do
                hoistEither $ mapM (find hyps m) hs)
            r   <- parse_calc hyps m d
            return r { 
                first_step = xp,
                following  = (op,first_step r,hyp,line_info t):following r }
        Nothing         -> do
            li <- ask
            xp <- fromEither ztrue $ get_expr m xs
            return $ Calc (context m) ztrue xp [] li
        _               -> do
                    li <- ask
                    RWS.tell [Error "invalid hint" li]
                    return $ Calc (context m) ztrue ztrue [] li
    where
        find :: Map Label Expr -> Machine -> (Label,LineInfo) -> Either [Error] Expr
        find hyps m (xs,li) = either Right Left (do
                err $ M.lookup xs $ hyps
                err $ M.lookup xs $ inv p0
                err $ M.lookup xs $ inv_thm p0
                err $ M.lookup xs $ inv p1
                err $ M.lookup xs $ inv_thm p1
                err $ M.lookup xs $ inits m
                err $ M.lookup xs $ fact $ theory m
                foldM f [err_msg] $ elems $ events m
                )
            where
                p0 = props m
                p1 = inh_props m
                err (Just x) = Left x
                err Nothing  = Right [err_msg]
                err_msg      = Error "reference to unknown predicate" li
                f :: [Error] -> Event -> Either Expr [Error]
                f _ ev = do
                    err (M.lookup xs $ scheds  ev)
                    err $ M.lookup xs $ guard  ev
                    err $ M.lookup xs $ action ev

    -- assoc' n
get_table m = with_tracingM $ do
        let key = sort $ M.keys $ extends $ theory m
--        traceM $ "KEY: " ++ show key
        tb <- lift $ RWS.gets parse_table
        case M.lookup key tb of
            Just x -> return x
            Nothing -> do
                let x   = assoc' $ all_notation m
                    new = insert key x tb
                lift $ RWS.modify $ \s -> s { parse_table = new }
                return x
                                
get_expr :: ( Monad m, Monoid b ) 
         => Machine -> [LatexDoc] 
         -> EitherT [Error] (RWST LineInfo b System m)  Expr
get_expr m ys = do
        tb <- get_table m
        y  <- focus_es $ parse_expr 
            (context m) 
            (all_notation m) tb
            (concatMap flatten_li xs)
        let x = normalize_generics y
        li <- if L.null xs
            then ask
            else return $ line_info xs
        unless (L.null $ ambiguities x) $ left 
            $ map (\x -> Error (format msg x (type_of x)) li)
                $ ambiguities x
        return x
    where
        xs    = drop_blank_text ys
        msg   = "type of {0} is ill-defined: {1}"

get_assert :: ( Monad m, Monoid b ) 
           => Machine -> [LatexDoc] 
           -> EitherT [Error] (RWST LineInfo b System m) Expr
get_assert m ys = do
        tb <- get_table m
        x  <- focus_es $ parse_expr 
            (context m) 
            (all_notation m) tb
            (concatMap flatten_li xs)
        li <- if L.null xs
            then ask
            else return $ line_info xs
        x <- either 
            (\x -> left [Error x li]) 
            (right . normalize_generics) $ zcast bool $ Right x
        unless (L.null $ ambiguities x) $ left 
            $ map (\x -> Error (format msg x (type_of x)) li)
                $ ambiguities x
        return x
    where
        xs    = drop_blank_text ys
        msg   = "type of {0} is ill-defined: {1}"

get_evt_part :: ( Monad m, Monoid b ) 
             => Machine -> Event
             -> [LatexDoc] 
             -> EitherT [Error] (RWST LineInfo b System m)  Expr
get_evt_part m e ys = do
        tb <- get_table m
        x  <- focus_es $ parse_expr (
                                     step_ctx m 
                         `merge_ctx` theory_ctx S.empty (theory m)
                         `merge_ctx` evt_live_ctx e
                         `merge_ctx` evt_saf_ctx  e)
                        (all_notation m) tb
                        (concatMap flatten_li xs)
        li <- if L.null xs
            then ask
            else return $ line_info xs
--        li <- ask
--        let (i,j) = if L.null xs
--                    then li
--                    else line_info xs
        x <- either 
            (\x -> left [Error x li]) 
            (right . normalize_generics) $ zcast bool $ Right x
        unless (L.null $ ambiguities x) $ left 
            $ map (\x -> Error (format msg x (type_of x)) li)
                $ ambiguities x
        return x
    where
        msg   = "type of {0} is ill-defined: {1}"
        xs    = drop_blank_text ys
