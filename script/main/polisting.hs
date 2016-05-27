#!/usr/bin/env cabal exec runhaskell
module Main where

import Control.Applicative

import System.Process

import Text.Printf

-- try :: [a] -> [Maybe a]
-- try [] = [Nothing]
-- try xs = map Just xs

-- instance Read StrList where
--     readsPrec n xs = do
--             case xs' of
--                 '(':ys -> _ (readParen True $ fix (\rec res ys -> do
--                                         x <- try $ readsPrec n ys
--                                         case x of
--                                             Just (x,zs) -> rec (x:rec) zs
--                                             Nothing -> return (res,ys)
--                                         ) []) xs'
--                 ')':ys -> []
--                 _:_ -> [first Str $ break isSpace xs']
--                 [] -> [(List [],"")]
--         where
--             xs' = dropWhile isSpace xs

copy :: String -> IO ()
copy xs = do
    readProcess "pbcopy" [] xs
    return ()

paste :: IO String
paste = do
    readProcess "pbpaste" [] ""

leave :: Int -> [a] -> [a]
leave n xs = take (length xs - n) xs

escape :: String -> String
escape xs = concatMap f xs
    where
        f '\t' = "\\t"
        f '\\' = "\\\\"
        f '\"' = "\\\""
        f x    = [x]

main :: IO ()
main = do
    -- xs <- getArgs
    -- fn <- paste
    ln <- (leave 1 . drop 1 . lines . escape) <$> paste
    -- ln <- (drop 1 . lines) <$> readFile fn
    copy $ unlines $ 
               map (printf "    [ \"%s\"") (take 1 ln) 
            ++ map (printf "    , \"%s\"") (drop 1 ln) 
            ++ ["    ]"]
