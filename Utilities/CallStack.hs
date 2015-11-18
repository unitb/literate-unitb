module Utilities.CallStack 
    ( module Utilities.CallStack
    , module GHC.Stack )
where

import Control.Lens

import Data.Maybe

import GHC.Stack
import GHC.SrcLoc

import PseudoMacros

import Text.Printf

import Utilities.Syntactic

stackTrace' :: [FilePath] -> CallStack -> String -> String
stackTrace' fs stack str = fromMaybe str $ stackTrace fs stack

errorTrace :: [FilePath] -> CallStack -> String -> [Error]
errorTrace fs stack msg = [MLError msg $ map (_2 %~ locToLI) loc]
    where
        loc = getSrcLocs fs stack
        
getSrcLocs :: [FilePath] -> CallStack -> [(String,SrcLoc)]
getSrcLocs fs cs = filter notHere $ getCallStack cs
    where
        notHere :: (a,SrcLoc) -> Bool
        notHere (_,x) = srcLocFile x `notElem` $__FILE__:fs

stackTrace :: [FilePath] -> CallStack -> Maybe String
stackTrace fs cs | null loc  = Just $ '\n':concatMap f loc
                 | otherwise = Nothing
    where
        loc = getSrcLocs fs cs
        f (fn,loc) = printf "%s - %s\n" (locToString loc) fn

locToString :: SrcLoc -> String
locToString loc = printf "%s:%d:%d" 
            (srcLocFile loc) 
            (srcLocStartLine loc)
            (srcLocStartCol loc)

locToLI :: SrcLoc -> LineInfo
locToLI loc = LI
            (srcLocFile loc) 
            (srcLocStartLine loc)
            (srcLocStartCol loc)
