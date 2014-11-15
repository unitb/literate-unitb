module Document.Tests.Suite where

    -- Modules
import Document.Machine

import Logic.Expr
import Logic.Proof

import UnitB.PO

import Z3.Z3

    -- Libraries
import Control.Monad.Trans.Either

import Data.List as L
import Data.Map as M

import Utilities.Format

verify :: FilePath -> Int -> IO (String, Map Label Sequent)
verify path i = do
    r <- list_file_obligations path
    case r of
        Right ms -> do
            let (m,pos) = ms !! i
            (s,_,_) <- str_verify_machine m
            return (s, pos)
        Left x -> return (unlines $ L.map show x, empty)

proof_obligation :: FilePath -> String -> Int -> IO String
proof_obligation path lbl i = eitherT (return . show) return $ do
        xs <- bimapEitherT show id
            $ EitherT $ list_file_obligations path
        let pos = snd $ xs !! i
        po <- maybe 
                (left $ format "invalid label: {0}" lbl)
                right
            $ label lbl `M.lookup` pos
        let cmd = concatMap pretty_print' $ z3_code po
        return cmd

find_errors :: FilePath -> IO String 
find_errors path = do
    m <- parse_machine path
    return $ either 
        (unlines . L.map show) 
        (const $ "no errors")
        m