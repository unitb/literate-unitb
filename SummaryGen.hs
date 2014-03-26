{-# LANGUAGE FlexibleContexts #-}
module SummaryGen where

import Logic.Classes
import Logic.ExpressionStore
import Logic.Label
import Logic.Expr

import UnitB.AST

    -- Libraries
import Control.Monad ( forM )
import Control.Monad.State.Class

import Data.List (intercalate)
import Data.Map as M (null,elems,toList,fromList,Map)

summary :: MonadState ExprStore m
        => Label -> Event -> m String
summary lbl e = do
    xs <- sequence
        [ index_sum lbl e
        , return ["\\begin{block}"]
        , csched_sum e
        , fsched_sum e
        , param_sum e
        , guard_sum e
        , act_sum e
        , return ["\\item \\textbf{end} \\\\"]
        , return ["\\end{block}"]
        ]
    return $ unlines $ concat xs

add_comments :: String -> String
add_comments str = intercalate "\n" $ map (++ " %") $ lines $ "$" ++ f str ++ "$"
    where
        f xs = concatMap g xs
        g '&' = ""
        g x = [x]

put_expr :: MonadState ExprStore m => (Label,Expr) -> m String
put_expr (s,e) = do
        str <- get_string e
        return $ "\\item[ \\eqref{" ++ show s ++ "} ]" ++ add_comments str

put_all_expr :: MonadState ExprStore m
             => Map Label Expr -> m [String]
put_all_expr xs = do
        let begin = "\\begin{block}"
            end   = "\\end{block}"
        xs <- forM (toList xs) put_expr
        return $ [begin] ++ xs ++ [end] 

index_sum :: MonadState ExprStore m
          => Label -> Event -> m [String]
index_sum lbl e = return ["\\noindent \\ref{" ++ show lbl ++ "} " ++ ind ++ " \\textbf{event}"]
    where
        ind 
            | M.null $ indices e = ""
            | otherwise          = "[" ++ intercalate "," (map name $ M.elems $ indices e) ++ "]"

csched_sum :: MonadState ExprStore m
           => Event -> m [String]
csched_sum e
        | M.null $ coarse $ new_sched e = return []
        | otherwise                = do
            xs <- put_all_expr $ coarse $ new_sched e
            return $ kw:xs
    where
        kw = "\\item \\textbf{during}"    

fsched_sum :: MonadState ExprStore m
           => Event -> m [String]
fsched_sum e = 
    case fine $ new_sched e of
        Nothing  -> return []
        Just sch -> do
            xs <- put_all_expr $ fromList [sch]
            let kw = "\\item \\textbf{upon}"
--                begin = "\\begin{block}"
--                end   = "\\end{block}"
--            str <- get_string $ sch
--            return [kw,begin,"\\item" ++ add_comments str,end]
            return $ kw:xs

param_sum :: MonadState ExprStore m
          => Event -> m [String]
param_sum e
    | M.null $ params e  = return []
    | otherwise          = do
        return ["\\item \\textbf{any} " 
            ++ intercalate "," (map name $ M.elems $ params e)]

guard_sum :: MonadState ExprStore m
          => Event -> m [String]
guard_sum e
    | M.null $ new_guard e = return []
    | otherwise            = do
        let kw = "\\item \\textbf{when}"
        xs <- put_all_expr $ new_guard e
        return $ kw:xs

act_sum :: MonadState ExprStore m
        => Event -> m [String]
act_sum e
    | M.null $ action e  = return []
    | otherwise          = do
        let kw = "\\item \\textbf{begin}"
        xs <- put_all_expr $ action e
        return $ kw:xs

