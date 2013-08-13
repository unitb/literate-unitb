{-# LANGUAGE ScopedTypeVariables, BangPatterns #-}
module Document.Document 
    ( module Document.Machine )
where

    -- Modules
import Document.Machine

import Latex.Parser

    -- Libraries

tex_to_string d = unlines $ concatMap (aux 0) d
    where
        aux n d =
            indent
                (case d of
                    Env s _ c _         -> begin s ++ concatMap (aux (n+1)) c ++ end s
                    Bracket True _ c _  -> ["{"] ++ concatMap (aux (n+1)) c ++ ["}"]
                    Bracket False _ c _ -> ["["] ++ concatMap (aux (n+1)) c ++ ["]"]
                    Text xs             -> lines $ concatMap f $ concatMap lexeme xs)
            where
                indent xs = map (margin ++) xs
                margin  = "|  |"
                begin s = ["begin{" ++ s ++ "}"]
                end s   = ["end{" ++ s ++ "}"]
                f '\n'  = "\\n\n"
                f '\t'  = "\\t"
                f x     = [x]

