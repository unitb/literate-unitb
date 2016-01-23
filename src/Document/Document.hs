{-# LANGUAGE ScopedTypeVariables, BangPatterns  #-}
{-# LANGUAGE ExplicitNamespaces, Arrows         #-}
module Document.Document where

    --
    -- Modules
    --
import Document.Machine   as Mch
import Document.Pipeline
import Document.Phase as P
import Document.Phase.Types
import Document.Phase.Structures as Mch
import Document.Phase.Declarations as Mch
import Document.Phase.Expressions as Mch
import Document.Phase.Proofs as Mch
import Document.Visitor

import Latex.Parser

import Logic.Expr
import Logic.Proof

import UnitB.UnitB

    --
    -- Libraries
    --
import Control.Arrow hiding (left,app) -- (Arrow,arr,(>>>))

import           Control.Lens
import           Control.Monad 
import qualified Control.Monad.Reader as R
import           Control.Monad.Trans
import           Control.Monad.Trans.Either
import qualified Control.Monad.Writer as W

import           Data.Either.Combinators
import           Data.List.Ordered (sortOn)

import           Utilities.Map   as M hiding ( map, (\\) )
import qualified Utilities.Map   as M
import Utilities.Syntactic as Syn
import Utilities.Table

read_document :: LatexDoc -> Either [Error] System
read_document xs = mapBoth (sortOn line_info . shrink_error_list) id $ do
            let li = line_info xs
            (ms,cs) <- get_components xs li
            runPipeline' ms cs () system

system :: Pipeline MM () System
system =     run_phase0_blocks 
         >>> run_phase1_types 
         >>> run_phase2_vars
         >>> run_phase3_exprs
         >>> run_phase4_proofs
         >>> wrap_machine

wrap_machine :: Pipeline MM SystemP4 System
wrap_machine = proc m4 -> do
                sys <- liftP id -< m4 & mchTable (M.traverseWithKey make_machine)
                returnA -< create' assert $ do
                    machines   .= sys^.mchTable
                    ref_struct .= (Nothing <$ sys^.mchTable)
                    ref_struct %= M.union (sys^.refineStruct.to (M.map Just .edges))

all_machines :: LatexDoc -> Either [Error] System
all_machines xs = read_document xs

list_machines :: FilePath
              -> EitherT [Error] IO [Machine]
list_machines fn = do
        xs <- EitherT $ parse_latex_document fn
        ms <- hoistEither $ all_machines xs
        return $ map snd $ toAscList $ ms!.machines

list_proof_obligations :: FilePath
                       -> EitherT [Error] IO [(Machine, Table Label Sequent)]
list_proof_obligations fn = do
        xs <- list_machines fn
        return [ (m,proof_obligation m) | m <- xs ]

list_file_obligations :: FilePath
                       -> IO (Either [Error] [(Machine, Table Label Sequent)])
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
        return $ map snd $ toAscList $ ms!.machines

get_components :: LatexDoc -> LineInfo 
               -> Either [Error] (Table Name [LatexDoc],Table String [LatexDoc])
get_components xs li = 
        liftM g
            $ R.runReader (runEitherT $ W.execWriterT 
                    (mapM_ f $ contents' xs)) li

    where
        with_li li cmd = R.local (const li) cmd
        get_name li xs = with_li li $ liftM fst $ lift $ get_1_lbl xs
        f x@(Env _ tag li0 xs _li1) 
            | tag == "machine" = do
                    n <- get_name li0 xs
                    n' <- lift $ hoistEither $ Syn.with_li li $ isName n
                    W.tell ([(n',[xs])],[])
            | tag == "context" = do
                    n <- get_name li0 xs
                    W.tell ([],[(n,[xs])])
            | otherwise      = map_docM_ f x
        f x = map_docM_ f x
        g (x,y) = (M.fromListWith (++) x, M.fromListWith (++) y)

syntaxSummary :: [String]
syntaxSummary = machineSyntax system
