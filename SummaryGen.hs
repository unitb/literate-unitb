module SummaryGen where

import UnitB.ExpressionStore

import UnitB.AST
import UnitB.Label

    -- Libraries
import Control.Monad ( forM )

import Data.List (intercalate)
import Data.Map as M (null,elems,toList,fromList)

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

add_comments str = intercalate "\n" $ map (++ " %") $ lines $ "$" ++ f str ++ "$"
    where
        f xs = concatMap g xs
        g '&' = ""
        g x = [x]

put_expr (s,e) = do
        str <- get_string e
        return $ "\\item[ \\eqref{" ++ show s ++ "} ]" ++ add_comments str

put_all_expr xs = do
        let begin = "\\begin{block}"
            end   = "\\end{block}"
        xs <- forM (toList xs) put_expr
        return $ [begin] ++ xs ++ [end] 

index_sum lbl e = return ["\\noindent \\ref{" ++ show lbl ++ "} " ++ ind ++ " \\textbf{event}"]
    where
        ind 
            | M.null $ indices e = ""
            | otherwise          = "[" ++ intercalate "," (map name $ M.elems $ indices e) ++ "]"
csched_sum e
        | M.null $ fst $ last_schedule e = return []
        | otherwise                = do
            xs <- put_all_expr $ fst $ last_schedule e
            return $ kw:xs
    where
        kw = "\\item \\textbf{during}"    
fsched_sum e = 
    case snd $ last_schedule e of
        Nothing  -> return []
        Just sch -> do
            xs <- put_all_expr $ fromList [sch]
            let kw = "\\item \\textbf{upon}"
--                begin = "\\begin{block}"
--                end   = "\\end{block}"
--            str <- get_string $ sch
--            return [kw,begin,"\\item" ++ add_comments str,end]
            return $ kw:xs
param_sum e
    | M.null $ params e  = return []
    | otherwise          = do
        return ["\\item \\textbf{any} " 
            ++ intercalate "," (map name $ M.elems $ params e)]
guard_sum e
    | M.null $ guard e   = return []
    | otherwise          = do
        let kw = "\\item \\textbf{when}"
        xs <- put_all_expr $ guard e
        return $ kw:xs
act_sum e
    | M.null $ action e  = return []
    | otherwise          = do
        let kw = "\\item \\textbf{begin}"
        xs <- put_all_expr $ action e
        return $ kw:xs

