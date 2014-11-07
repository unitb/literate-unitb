{-# LANGUAGE FlexibleContexts #-}
module Documentation.SummaryGen where

import Logic.Expr
import Logic.ExpressionStore

import UnitB.AST

    -- Libraries
import Control.Monad.Reader
import Control.Monad.Trans.Writer

import Data.List (intercalate)
import Data.Map as M (null,elems,toList,fromList,Map)
import Data.Maybe

import Utilities.Format

type M = WriterT [String] (Reader ExprStore)

machine_summary :: Machine -> ExprStore -> String
machine_summary m = runReader $ do
    let prop = props m
    xs <- execWriterT $ do
        invariant_sum prop
        liveness_sum prop
        safety_sum prop
    --     [ 
    --     ]
    return $ unlines xs

event_summary :: Label -> Event -> ExprStore -> String
event_summary lbl e = runReader $ do
    xs <- execWriterT $ do
        index_sum lbl e
        block $ do
            csched_sum lbl e
            fsched_sum lbl e
            param_sum e
            guard_sum lbl e
            act_sum lbl e
            tell ["\\item \\textbf{end} \\\\"]
        -- ]
    return $ unlines xs

block :: M () -> M ()
block cmd = do
    tell ["\\begin{block}"]
    cmd
    tell ["\\end{block}"]

invariant_sum :: PropertySet -> M ()
invariant_sum prop = do
        section kw_inv (label "") (inv prop) 
        section kw_thm (label "") (inv_thm prop)
    where
        kw_inv = "\\textbf{invariants}"
        kw_thm = "\\textbf{invariants} (theorems)"
    -- forM_ (M.toList $ invariants prop) $ \(lbl,inv) -> do

liveness_sum :: PropertySet -> M ()
liveness_sum prop = do
        section' kw (label "") (progress prop) toString
    where
        kw = "\\textbf{progress}"
        toString (LeadsTo _ p q) = do
            p' <- get_string' p
            q' <- get_string' q
            return $ format "{0} \\quad \\mapsto\\quad {1}" p' q'

safety_sum :: PropertySet -> M ()
safety_sum prop = do
        section' kw (label "") (safety prop) toString
    where
        kw = "\\textbf{safety}"
        toString (Unless _ p q exc) = do
            p' <- get_string' p
            q' <- get_string' q
            let exc' = case exc of
                        Nothing -> ""
                        Just exc -> format "\\qquad  \\text{(except {0})}" exc
            return $ format "{0} \\textbf{\\quad unless \\quad} {1}{2}" p' q' exc'

add_comments :: String -> String
add_comments str = intercalate "\n" $ map (++ " %") $ lines $ "$" ++ f str ++ "$"
    where
        f xs = concatMap g xs
        g '&' = ""
        g x = [x]

get_string' :: Expr -> M String
get_string' e = do
    es <- lift $ ask
    return $ get_string es e

put_expr :: (a -> M String) -> Label -> (Label,a) -> M ()
put_expr toString pre (s,e) = do
        str <- toString e
        tell [format "\\item[ \\eqref{{0}} ]{1}" 
                    (show pre ++ show s)
                    (add_comments str)]

put_all_expr :: (a -> M String) -> Label -> Map Label a -> M ()
put_all_expr toString pre xs = do
        block $ forM_ (toList xs) $ put_expr toString pre

section' :: String -> Label -> Map Label a -> (a -> M String) -> M ()
section' kw pre xs toString = do
    if M.null xs 
        then return ()
        else do
            tell [kw]
            put_all_expr toString pre xs

section :: String -> Label -> Map Label Expr -> M ()
section kw pre xs = section' kw pre xs get_string'

index_sum :: Label -> Event -> M ()
index_sum lbl e = tell ["\\noindent \\ref{" ++ show lbl ++ "} " ++ ind ++ " \\textbf{event}"]
    where
        ind 
            | M.null $ indices e = ""
            | otherwise          = "[" ++ intercalate "," (map name $ M.elems $ indices e) ++ "]"

csched_sum :: Label -> Event -> M ()
csched_sum lbl e = section kw lbl $ coarse $ new_sched e
    where
        kw = "\\item \\textbf{during}"    

fsched_sum :: Label -> Event -> M ()
fsched_sum lbl e = section kw lbl $ fromList xs
    where
        kw = "\\item \\textbf{upon}"
        xs = maybeToList (fine $ new_sched e)
            
            
--                begin = "\\begin{block}"
--                end   = "\\end{block}"
--            str <- get_string $ sch
--            return [kw,begin,"\\item" ++ add_comments str,end]

param_sum :: Event -> M ()
param_sum e
    | M.null $ params e  = return ()
    | otherwise          = do
        tell ["\\item \\textbf{any} " 
            ++ intercalate "," (map name $ M.elems $ params e)]

guard_sum :: Label -> Event -> M ()
guard_sum lbl e = section kw lbl $ new_guard e
    where
        kw = "\\item \\textbf{when}"

act_sum :: Label -> Event -> M ()
act_sum lbl e = section kw lbl $ action e
    where 
        kw = "\\item \\textbf{begin}"

