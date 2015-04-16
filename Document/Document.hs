{-# LANGUAGE ScopedTypeVariables, BangPatterns  #-}
{-# LANGUAGE ExplicitNamespaces, Arrows         #-}
module Document.Document where

    --
    -- Modules
    --
import Document.Context   as Ctx
import Document.Machine   as Mch
import Document.Pipeline
import Document.Phase as P
import Document.Scope
import Document.Proof
import Document.Visitor

import Latex.Parser

import Logic.Expr
import Logic.Proof hiding ( with_line_info )

import UnitB.AST as AST
import UnitB.PO


    --
    -- Libraries
    --
import Control.Arrow hiding (left,app) -- (Arrow,arr,(>>>))

import           Control.Monad 
import           Control.Monad.State.Class 
import           Control.Monad.Trans
import           Control.Monad.Trans.Either
import           Control.Monad.Trans.RWS as RWS ( runRWS )
import           Data.Map   as M hiding ( map, foldl, (\\) )
import qualified Data.Map   as M
import           Data.List.Ordered (sortOn)
import Utilities.Syntactic
import Utilities.Trace ()

read_document :: [LatexDoc] -> M ()
read_document xs = bimapEitherT (sortOn line_info . shrink_error_list) id $ do
            let li = line_info xs
            (ms,cs) <- hoistEither $ get_components xs li
            ms <- runPipeline' ms cs $ proc doc -> do
                let mch = M.map (const ()) $ getMachineInput doc
                    ctx = M.map (const ()) $ getContextInput doc
                    m0 = M.mapWithKey (const . MachinePh0 mch) mch
                    c0 = M.map (const $ TheoryP0 ()) ctx
                (r_ord,m1) <- Mch.run_phase1_types -<  m0
                _c1 <- Ctx.run_phase1_types -< c0
                m2 <- Mch.run_phase2_vars   -< (r_ord, m1)
                m3 <- Mch.run_phase3_exprs  -< (r_ord, m2)
                m4 <- Mch.run_phase4_proofs -< (r_ord, m3)
                let ms = M.mapWithKey make_machine m4 :: MTable (Either [Error] Machine)
                One machines <- triggerP -< One (all_errors ms)
                returnA -< machines
            lift $ modify $ \s -> s { machines = M.mapKeys (\(MId s) -> s) ms }

all_machines :: [LatexDoc] -> Either [Error] System
all_machines xs = do
        cmd
        return s
    where
        (cmd,s,_) = runRWS (runEitherT $ read_document xs) li empty_system
        li = LI "" 1 1 

list_machines :: FilePath
              -> EitherT [Error] IO [Machine]
list_machines fn = do
        xs <- EitherT $ parse_latex_document fn
        ms <- hoistEither $ all_machines xs
        return $ map snd $ toList $ machines ms

list_proof_obligations :: FilePath
                       -> EitherT [Error] IO [(Machine, Map Label Sequent)]
list_proof_obligations fn = do
        xs <- list_machines fn
        hoistEither $ forM xs $ \x -> do
            y <- proof_obligation x
            return (x,y)

list_file_obligations :: FilePath
                       -> IO (Either [Error] [(Machine, Map Label Sequent)])
list_file_obligations fn = do
        runEitherT $ list_proof_obligations fn

parse_system :: FilePath -> IO (Either [Error] System)
parse_system fn = runEitherT $ do
        xs <- EitherT $ parse_latex_document fn
        hoistEither $ all_machines xs
        
parse_machine :: FilePath -> IO (Either [Error] [Machine])
parse_machine fn = runEitherT $ do
        xs <- EitherT $ parse_latex_document fn
        ms <- hoistEither $ all_machines xs
        return $ map snd $ toList $ machines ms
