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

set_proof p (Step a b c d Nothing)      = return $ Step a b c d $ Just p
set_proof p (Step a b c d (Just _)) = Left [("too many proofs",i,j)]
    where
        (i,j) = line_info p

set_goal g _ (Step a b c Nothing d)       = return $ Step a b c (Just g) d
set_goal g (i,j) (Step a b c (Just _) d)  = Left [("too many goals",i,j)]

add_assumption lbl asm (i,j) (Step a b c d e) 
    | lbl `member` c    = Left [(format "an assumption {0} already exists" lbl,i,j)]
    | otherwise         = return $ Step a b (insert lbl asm c) d e

add_assert lbl asrt (i,j) (Step a b c d e)    
    | lbl `member` a    = Left [(format "an assertion {0} already exists" lbl,i,j)]
    | otherwise         = return $ Step (insert lbl asrt a) b c d e

add_proof lbl prf (i,j) (Step a b c d e)      
    | lbl `member` b    = Left [(format "a proof for assertion {0} already exists" lbl,i,j)]
    | otherwise         = return $ Step a (insert lbl prf b) c d e

empty_step = Step empty empty empty Nothing Nothing

find_assumptions :: Machine
                 -> [LatexDoc] 
                 -> ProofStep
                 -> MEither Error ProofStep
find_assumptions m = visit_doc
        [   (   "calculation"
            ,   Env0Args (\() xs proofs (i,j) -> return proofs)
            )
        ,   (   "free:var"
            ,   Env2Args (\(from,to) xs proofs (i,j) -> return proofs)
            )
        ,   (   "by:cases"
            ,   Env0Args (\() xs proofs (i,j) -> return proofs)
            )
        ,   (   "by:parts"
            ,   Env0Args (\() xs proofs (i,j) -> return proofs)
            )
        ,   (   "subproof"
            ,   Env1Args (\(lbl,()) xs proofs (i,j) -> return proofs)
            )
        ] [ (   "\\assume"
            ,   Cmd1Args1Blocks (\(lbl,formula) proofs (i,j) -> do
                    expr <- get_assert m formula (i,j)
                    add_assumption (label lbl) expr (i,j) proofs)
            )
        ,   (   "\\assert"
            ,   Cmd1Args1Blocks (\(lbl,formula) proofs (i,j) -> do
                    expr <- get_assert m formula (i,j)
                    add_assert (label lbl) expr (i,j) proofs)
            )
        ,   (   "\\goal"
            ,   Cmd0Args1Blocks (\(formula,()) proofs (i,j) -> do
                    expr <- get_assert m formula (i,j)
                    set_goal expr (i,j) proofs)
            )
        ]

find_proof_step :: Map Label Expr 
                -> Machine
                -> [LatexDoc] 
                -> ProofStep
                -> MEither Error ProofStep
find_proof_step hyps m = visit_doc
        [   (   "calculation"
            ,   Env0Args (\() xs proofs (i,j) -> do
                    cc <- toEither $ parse_calc hyps m xs (i,j)
                    case infer_goal cc of
                        Right cc_goal -> set_proof (ByCalc cc { goal = cc_goal }) proofs
                        Left msg      -> Left [(format "type error: {0}" msg,i,j)]) 
            )
                -- TODO: make into a command
        ,   (   "free:var"
            ,   Env2Args (\(from,to) xs proofs (i,j) -> do
                    p     <- collect_proof_step hyps m xs (i,j)
                    set_proof (FreeGoal from to p (i,j)) proofs)
            )
        ,   (   "by:cases"
            ,   Env0Args (\() xs proofs (i,j) -> do
                    cases <- toEither $ find_cases hyps m xs []
                    set_proof (ByCases (reverse cases) (i,j)) proofs )
            )
        ,   (   "by:parts"
            ,   Env0Args (\() xs proofs (i,j) -> do
                    cases <- toEither $ find_parts hyps m xs []
                    set_proof (ByParts (reverse cases) (i,j)) proofs )
            )
        ,   (   "subproof"
            ,   Env1Args (\(lbl,()) xs proofs (i,j) -> do
                    p <- collect_proof_step hyps m xs (i,j)
                    add_proof (label lbl) p (i,j) proofs)
            )
        ] [ (   "\\easy"
            ,   Cmd0Args (\() proofs (i,j) -> 
                    set_proof (Easy (i,j)) proofs)
            )
        ]

find_cases :: Map Label Expr 
           -> Machine
           -> [LatexDoc] 
           -> [(Label,Expr,Proof)]
           -> MEither Error [(Label,Expr,Proof)]
find_cases hyps m = visit_doc 
        [   (   "case"
            ,   Env1Args1Blocks (\(lbl,formula) xs cases (i,j) -> do
                    expr      <- get_assert m formula (i,j)
                    p         <- collect_proof_step 
                            (insert (label lbl) expr hyps) 
                            m xs (i,j)
                    return ((label lbl, expr, p):cases) ) 
            )
        ] []

find_parts :: Map Label Expr 
           -> Machine
           -> [LatexDoc] 
           -> [(Expr,Proof)]
           -> MEither Error [(Expr,Proof)]
find_parts hyps m = visit_doc 
        [   (   "part:a"
            ,   Env0Args1Blocks (\(formula,()) xs cases (i,j) -> do
                    expr      <- get_assert m formula (i,j)
                    p         <- collect_proof_step hyps m xs (i,j)
                    return ((expr, p):cases))
            )
        ] []

collect_proof_step hyps m xs (i,j) = do
        step@(Step asrt _ asm _ _) <- toEither $ find_assumptions m xs empty_step
        let hyps2 = asrt `union` asm `union` hyps
        step <- toEither $ find_proof_step hyps2 m xs step
        case step of
            Step assrt prfs asm ng (Just p) -> do
                let f k x = (x, prfs ! k)
                p <- if M.null assrt && M.null prfs
                    then return p
                    else if keysSet assrt == keysSet prfs
                    then return $ Assertion (M.mapWithKey f assrt) p (i,j)
                    else Left [("assertion labels and proofs mismatch",i,j)]
                case ng of
                    Just g  -> return $ Assume asm g p (i,j)
                    Nothing -> 
                        if M.null asm 
                        then return p
                        else Left [("assumptions must be accompanied by a new goal",i,j)]
            _   -> Left [("expecting a single proof step",i,j)]         

parse_calc hyps m xs li = 
    case find_cmd_arg 2 ["\\hint"] xs of
        Just (a,t,[b,c],d)    -> do
            xp <- fromEither ztrue $ get_expr m a li
            op <- fromEither Equal $ read_tokens 
                    (do eat_space ; x <- oper ; eat_space ; return x) 
                    (concatMap flatten_li b)
            hyp <- fromEither [] (do
                hs <- fmap (map (\(x,y) -> (label x,y))) $ hint c
                mapM (find hyps m) hs)
            r   <- parse_calc hyps m d li
            return r { 
                first_step = xp,
                following  = (op,first_step r,hyp,line_info t):following r }
        Nothing         -> do
            xp <- fromEither ztrue $ get_expr m xs li
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

collect_proofs :: [LatexDoc] -> Machine -> MEither Error Machine
collect_proofs = visit_doc
        [   (   "proof"
            ,   Env1Args (\(po,()) xs m (i,j) -> do
                    let lbl = composite_label [ _name m, label po ]
                    toEither $ error_list (i,j) 
                        [   ( lbl `member` proofs (props m)
                            , format "a proof for {0} already exists" lbl )
                        ] 
                    p <- collect_proof_step empty m xs (i,j)
                    return m { 
                        props = (props m) { 
                            proofs = insert lbl p $ 
                                    proofs $ props m } } )
            )
        ] []
                                
get_expr :: Machine -> [LatexDoc] -> (Int,Int) -> Either [Error] Expr
get_expr m ys li = do
        x <- fmap normalize_generics $ parse_expr (context m) (concatMap flatten_li xs)
        unless (L.null $ ambiguities x) $ Left 
            $ map (\x -> (format "type of {0} is ill-defined: {1}" x (type_of x),i,j))
                $ ambiguities x
        return x
    where
        xs    = drop_blank_text ys
        (i,j) = if L.null xs
                then li
                else line_info xs

get_assert :: Machine -> [LatexDoc] -> (Int,Int) -> Either [Error] Expr
get_assert m ys li = do
        x <- parse_expr (context m) (concatMap flatten_li xs)
        x <- either (\x -> Left [(x,i,j)]) (Right . normalize_generics) $ zcast BOOL $ Right x
        unless (L.null $ ambiguities x) $ Left 
            $ map (\x -> (format "type of {0} is ill-defined: {1}" x (type_of x),i,j))
                $ ambiguities x
        return x
    where
        xs    = drop_blank_text ys
        (i,j) = if L.null xs
                then li
                else line_info xs

get_evt_part :: Machine -> Event -> [LatexDoc] -> (Int,Int) -> Either [Error] Expr
get_evt_part m e ys li = do
        x <- parse_expr (            step_ctx m 
                         `merge_ctx` evt_live_ctx e
                         `merge_ctx` evt_saf_ctx  e)
                        (concatMap flatten_li xs)
        x <- either (\x -> Left [(x,i,j)]) (Right . normalize_generics) $ zcast BOOL $ Right x
        unless (L.null $ ambiguities x) $ Left 
            $ map (\x -> (format "type of {0} is ill-defined: {1}" x (type_of x),i,j))
                $ ambiguities x
        return x
    where
        xs    = drop_blank_text ys
        (i,j) = if L.null xs
                then li
                else line_info xs