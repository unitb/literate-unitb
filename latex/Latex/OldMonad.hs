module Latex.OldMonad where

    -- Modules
import Latex.Parser hiding (tokens)

    -- Libraries
import Control.Monad.State

import Data.List.NonEmpty (NonEmpty(..))
import Data.Semigroup

import Safe

import Utilities.Syntactic

type T = State LineInfo

makeTexDoc :: [T LatexDoc] -> LatexDoc
makeTexDoc cmd = evalState (getDoc cmd) (LI "" 1 1)

getDoc :: [T LatexDoc] -> T LatexDoc
getDoc cmd = do
    li  <- get
    xs  <- sequence cmd
    return $ sconcat $ Doc li [] li :| xs

nodeToDoc :: T LatexNode -> T LatexDoc
nodeToDoc n = Doc <$> get <*> sequence [n] <*> get

env :: String -> [T LatexDoc] -> T LatexDoc
env name xs = nodeToDoc $ do
    li0 <- get
    modify $ addCol (length $ "\\begin{")
    li1 <- get
    modify $ addCol (length $ name ++ "}")
    doc <- getDoc xs
    li2 <- get
    modify $ addCol (length $ "\\end{" ++ name ++ "}")
    return $ EnvNode $ Env li0 name li1 doc li2

bracket :: BracketType -> [T LatexDoc] -> T LatexDoc
bracket b xs = nodeToDoc $ do
    li  <- get
    modify $ addCol 1
    doc <- getDoc xs
    li' <- get
    modify $ addCol 1
    return $ BracketNode $ Bracket b li doc li'

text :: [T LatexToken] -> T LatexDoc
text xs = do
    li  <- get
    ys  <- sequence xs
    li' <- get
    return $ Doc li (map Text ys) li'

tokens :: (a -> LineInfo -> LatexToken) 
       -> a -> T LatexToken
tokens f x = do
    li@(LI fn i _) <- get
    let y = f x li
        ys = lexeme y
        ln = lines ys
        zs = zip ln $ li : [ LI fn (i+k) 1 | k <- [1..]]
        zs' = [ LI fn i (length xs + j) | (xs,LI fn i j) <- zs ]
    put $ lastDef li zs'
    return y

command :: String -> T LatexToken
command = tokens Command

textBlock :: String -> T LatexToken
textBlock = tokens TextBlock

blank :: String -> T LatexToken
blank = tokens Blank

open  :: BracketType -> T LatexToken
open = tokens Open

close :: BracketType -> T LatexToken
close = tokens Close

