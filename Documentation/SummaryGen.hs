{-# LANGUAGE FlexibleContexts #-}
module Documentation.SummaryGen 
    ( produce_summaries )
where

import Logic.Expr
import Logic.ExpressionStore

import UnitB.AST

    -- Libraries
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Writer

import Data.List (intercalate)
import Data.Map as M (null,elems,toList,keys
                     ,fromList,singleton, Map
                     ,lookup)
import Data.Maybe

import System.FilePath

import Utilities.Format

type Doc = ReaderT (ExprStore,FilePath) IO
type M = WriterT [String] Doc

produce_summaries :: FilePath -> System -> IO ()
produce_summaries path sys = runReaderT (do
            forM_ (M.elems ms) $ \m -> do
                machine_summary m
                properties_summary m
                forM_ (toList $ events m) $ \(lbl,evt) -> do
                    event_summary m lbl evt
            ) (st,path)
    where
        ms = machines sys
        st = expr_store sys

make_file :: FilePath -> M () -> Doc ()
make_file fn cmd = do
    path <- asks snd
    xs   <- execWriterT cmd
    liftIO $ writeFile (path </> fn) $ unlines xs

keyword :: String -> String
keyword kw = format "\\textbf{{0}}" kw

machine_summary :: Machine -> Doc ()
machine_summary m = make_file fn $ 
        block $ do
            item $ tell [keyword "machine" ++ " " ++ show (_name m)]
            item $ variable_sum m
            unless (M.null $ inv $ props m) 
                $ item $ input $ inv_file m
            unless (M.null $ inv_thm $ props m) 
                $ item $ input $ inv_thm_file m
            unless (M.null $ progress $ props m) 
                $ item $ input $ live_file m
            unless (M.null $ safety $ props m) 
                $ item $ input $ saf_file m
            item $ do
                tell [keyword "events"]
                block $ forM_ (keys $ events m) $ \k -> do
                    item $ input $ event_file_name m k
            item $ kw_end
    where
        fn = "machine_" ++ show (_name m) <.> "tex"

prop_file_name :: Machine -> String
prop_file_name m = "machine_" ++ show (_name m) ++ "_props" <.> "tex"

indent :: Int -> String -> String
indent n xs = intercalate "\n" $ map (margin ++) $ lines xs
    where
        margin = replicate n ' '

item :: M () -> M ()
item cmd = do
    let f [] = []
        f xs = ["  \\item " ++ intercalate "\n" (map (indent 2) xs)]
    censor f cmd

properties_summary :: Machine -> Doc ()
properties_summary m = do
        let prop = props m
        make_file (inv_file m) $ invariant_sum m
        make_file (inv_thm_file m) $ invariant_thm_sum prop
        make_file (live_file m) $ liveness_sum m
        make_file (saf_file m) $ safety_sum prop
        make_file fn $ block $ do
            item $ input $ inv_file m
            item $ input $ inv_thm_file m
            item $ input $ live_file m
            item $ input $ saf_file m
    where
        fn = prop_file_name m

inv_file :: Machine -> String
inv_file m  = "machine_" ++ show (_name m) ++ "_inv" <.> "tex"

inv_thm_file :: Machine -> String
inv_thm_file m  = "machine_" ++ show (_name m) ++ "_thm" <.> "tex"

live_file :: Machine -> String
live_file m = "machine_" ++ show (_name m) ++ "_prog" <.> "tex"

saf_file :: Machine -> String
saf_file m  = "machine_" ++ show (_name m) ++ "_saf" <.> "tex"

input :: String -> M ()
input fn = tell [format "\\input{{0}}" $ dropExtension fn]

kw_end :: M ()
kw_end = tell ["\\textbf{end} \\\\"]

event_file_name :: Machine -> Label -> FilePath
event_file_name m lbl = (show (_name m) ++ "_" ++ rename lbl) <.> "tex"
    where
        rename lbl = map f $ show lbl
        f ':' = '-'
        f x   = x

comment_of :: Machine -> DocItem -> M ()
comment_of m key = do
    item $ do
        case key `M.lookup` comments m of
            Just cmt -> block $ item $ tell [format "\\commentbox{{0}}" cmt]
            Nothing -> return ()

event_summary :: Machine -> Label -> Event -> Doc ()
event_summary m lbl e = make_file fn $ do
        index_sum lbl e
        comment_of m (DocEvent lbl)
        block $ do
            item $ csched_sum lbl e
            item $ fsched_sum lbl e
            item $ param_sum e
            item $ guard_sum lbl e
            item $ act_sum lbl e
            item $ kw_end
    where
        fn = event_file_name m lbl

block :: M () -> M ()
block cmd = do
    tell ["\\begin{block}"]
    cmd
    tell ["\\end{block}"]

variable_sum :: Machine -> M ()
variable_sum m = section (keyword "variables") $ 
    block $ 
        forM_ (keys $ variables m) $ \v -> do
            item $ tell [v]
            comment_of m (DocVar v)

invariant_sum :: Machine -> M ()
invariant_sum m = do
        let prop = props m
        section kw_inv $ put_all_expr_with_doc (comment_of m . DocInv) (label "") (inv prop) 
    where
        kw_inv = "\\textbf{invariants}"
        
invariant_thm_sum :: PropertySet -> M ()
invariant_thm_sum prop = 
        section kw_thm $ put_all_expr (label "") (inv_thm prop)
    where
        kw_thm = "\\textbf{invariants} (theorems)"

liveness_sum :: Machine -> M ()
liveness_sum m = do
        let prop = props m
        section kw $ put_all_expr_with_doc' (comment_of m . DocInv) toString (label "") (progress prop) 
    where
        kw = "\\textbf{progress}"
        toString (LeadsTo _ p q) = do
            p' <- get_string' p
            q' <- get_string' q
            return $ format "{0} \\quad \\mapsto\\quad {1}" p' q'

safety_sum :: PropertySet -> M ()
safety_sum prop = do
        section kw $ put_all_expr' toString (label "") (safety prop)
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
    es <- lift $ asks fst
    return $ get_string es e

put_expr :: (Label -> M ()) -> (a -> M String) -> Label -> (Label,a) -> M ()
put_expr doc toString pre (lbl,e) = do
        str <- toString e
        tell [format "\\item[ \\eqref{{0}} ]{1}" 
                    (show pre ++ show lbl)
                    (add_comments str)]
        doc lbl

put_all_expr' :: (a -> M String) -> Label -> Map Label a -> M ()
put_all_expr' = put_all_expr_with_doc' (const $ return ())

put_all_expr_with_doc' :: (Label -> M ()) -> (a -> M String) -> Label -> Map Label a -> M ()
put_all_expr_with_doc' doc toString pre xs
    | M.null xs = return ()
    | otherwise = 
        block $ forM_ (toList xs) $ put_expr doc toString pre

put_all_expr :: Label -> Map Label Expr -> M ()
put_all_expr = put_all_expr' get_string'

put_all_expr_with_doc :: (Label -> M ()) -> Label -> Map Label Expr -> M ()
put_all_expr_with_doc doc = put_all_expr_with_doc' doc get_string'

section :: String -> M () -> M ()
section kw cmd = do
    let f [] = []
        f xs = kw:xs
    censor f cmd

index_sum :: Label -> Event -> M ()
index_sum lbl e = tell ["\\noindent \\ref{" ++ show lbl ++ "} " ++ ind ++ " \\textbf{event}"]
    where
        ind 
            | M.null $ indices e = ""
            | otherwise          = "[" ++ intercalate "," (map name $ M.elems $ indices e) ++ "]"

csched_sum :: Label -> Event -> M ()
csched_sum lbl e =
        unless (sch == def) $ 
            section kw $ put_all_expr lbl sch
    where
        kw = "\\textbf{during}"    
        sch = coarse $ new_sched e
        def = M.singleton (label "default") zfalse

fsched_sum :: Label -> Event -> M ()
fsched_sum lbl e = section kw $ put_all_expr lbl $ fromList xs
    where
        kw = "\\textbf{upon}"
        xs = maybeToList (fine $ new_sched e)
            
            
--                begin = "\\begin{block}"
--                end   = "\\end{block}"
--            str <- get_string $ sch
--            return [kw,begin,"\\item" ++ add_comments str,end]

param_sum :: Event -> M ()
param_sum e
    | M.null $ params e  = return ()
    | otherwise          = do
        tell ["\\textbf{any} " 
            ++ intercalate "," (map name $ M.elems $ params e)]

guard_sum :: Label -> Event -> M ()
guard_sum lbl e = section kw $ put_all_expr lbl $ new_guard e
    where
        kw = "\\textbf{when}"

act_sum :: Label -> Event -> M ()
act_sum lbl e = section kw $ put_all_expr lbl $ action e
    where 
        kw = "\\textbf{begin}"

