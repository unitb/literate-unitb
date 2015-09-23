{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Latex.Monad where

    -- Modules
import Latex.Parser

    -- Libraries
import Control.Applicative
import Control.Lens
import Control.Monad.RWS

import Data.Char
import Data.Function
import Data.List
import Data.List.NonEmpty (nonEmpty,fromList)
import Data.Semigroup

import Utilities.Syntactic

import Text.Printf

newtype LatexGen a = LatexGen { getGen :: RWS Bool [LatexDoc] LineInfo a }
    deriving (Functor,Applicative,Monad)

makeLatex :: FilePath -> LatexGen () -> LatexDoc
makeLatex fn cmd = doc
    where
        (doc,_) = evalRWS (getGen $ getDoc cmd) True (LI fn 1 1)

next :: Int -> LatexGen ()
next ln = LatexGen $ do
    b <- ask
    if b
        then line += 1 >> column .= 1
        else column += ln

updateLI :: String -> LatexGen ()
updateLI xs = do
    next 0
    LatexGen $ case reverse $ lines xs of
        y0:_:ys -> do
            line += length ys + 1
            column .= length y0 + 1
        _ -> column .= length xs + 1

horizontal :: LatexGen a -> LatexGen a
horizontal (LatexGen cmd) = LatexGen $ local (const False) cmd

begin :: String -> [LatexGen ()] -> LatexGen a -> LatexGen a
begin name args body = do
    li <- LatexGen get
    updateLI $ printf "\\begin{%s}" name
    args <- horizontal $ do
        forM args $ getDoc . brackets
    (x,body) <- getDoc' body
    li'  <- LatexGen get
    node $ Env name li (sconcat $ fromList $ args ++ [body]) li'
    return x

brackets :: LatexGen a -> LatexGen a
brackets body = do
    next 1
    li  <- LatexGen get
    (x,doc) <- getDoc' body
    next 1
    li' <- LatexGen get
    node $ Bracket Curly li doc li'
    return x

node :: LatexNode -> LatexGen ()
node n = LatexGen $ get >>= \li -> tell [Doc [n] li]

token :: LatexToken -> LatexGen () 
token tok = do
    li <- LatexGen get
    node $ Text [tok] li

getDoc' :: LatexGen a -> LatexGen (a,LatexDoc)
getDoc' (LatexGen cmd) = LatexGen $ do
        (x,xs) <- censor (const []) $ listen cmd
        li <- get
        return (x,maybe (Doc [] li) sconcat $ nonEmpty xs)

getDoc :: LatexGen a -> LatexGen LatexDoc
getDoc = fmap snd . getDoc'

command :: String -> [LatexGen ()] -> LatexGen ()
command name args = do
    let name' 
            | take 1 name == "\\" = name
            | otherwise           = "\\" ++ name
    li <- LatexGen get
    updateLI name'
    token $ Command name' li
    horizontal $
        forM_ args brackets

text :: String -> LatexGen ()
text xs = do
    forM_ (lines xs) $ \ln -> do
        let ys = groupBy eq ln
            eq = (==) `on` isSpace
        ys <- forM ys $ \w -> do
            li <- LatexGen get
            LatexGen $ column += length w 
            return $ if any isSpace w 
                then Blank w li
                else TextBlock w li
        li <- LatexGen get
        LatexGen $ line += 1 
        LatexGen $ column .= 1 
        node $ Text ys li

