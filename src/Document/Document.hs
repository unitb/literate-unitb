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
import Document.Visitor hiding (hoistEither)

import Latex.Parser

import Logic.Expr
import Logic.Proof

import UnitB.UnitB

    --
    -- Libraries
    --
import Control.Arrow hiding (left,app) -- (Arrow,arr,(>>>))
import Control.Category

import           Control.Lens
import           Control.Lens.Misc
import           Control.Monad 
import qualified Control.Monad.Reader as R
import           Control.Monad.Trans
import           Control.Monad.Trans.Either
import qualified Control.Monad.Writer as W

import           Data.Either.Combinators
import           Data.List.Ordered (sortOn)
import qualified Data.List.NonEmpty as NE
import           Data.Map   as M hiding ( map, (\\) )
import qualified Data.Map   as M
import           Data.Semigroup

import Prelude hiding ((.),id)

import Utilities.Syntactic as Syn

read_document :: LatexDoc -> Either [Error] System
read_document = parseWith system

{-# INLINABLE parseWith #-}
parseWith :: Pipeline MM () a -> LatexDoc -> Either [Error] a
parseWith parser xs = mapBoth (sortOn line_info . shrink_error_list) id $ do
            let li = line_info xs
            (ms,cs) <- get_components xs li
            runPipeline' ms cs () parser

{-# INLINABLE system #-}
system :: Pipeline MM () System
system =     run_phase0_blocks 
         >>> run_phase1_types 
         >>> run_phase2_vars
         >>> run_phase3_exprs
         >>> run_phase4_proofs
         >>> wrap_machine

wrap_machine :: Pipeline MM SystemP4 System
wrap_machine = proc m4 -> do
                sys <- liftP id -< m4 & mchMap (M.traverseWithKey make_machine)
                returnA -< create' $ do
                    machines   .= sys^.mchMap
                    ref_struct .= (Nothing <$ sys^.mchMap)
                    ref_struct %= M.union (sys^.refineStruct.to (M.map Just .edges))

all_machines :: LatexDoc -> Either [Error] System
all_machines xs = read_document xs

list_machines :: FilePath
              -> EitherT [Error] IO [Machine]
list_machines fn = do
        doc <- liftIO $ readFile fn
        xs  <- hoistEither $ latex_structure fn doc
        ms <- hoistEither $ all_machines xs
        return $ map snd $ toAscList $ ms!.machines

list_proof_obligations :: FilePath
                       -> EitherT [Error] IO [(Machine, Map Label Sequent)]
list_proof_obligations fn = do
        xs <- list_machines fn
        return [ (m,proof_obligation m) | m <- xs ]

list_file_obligations :: FilePath
                       -> IO (Either [Error] [(Machine, Map Label Sequent)])
list_file_obligations fn = do
        runEitherT $ list_proof_obligations fn

parse_system :: FilePath -> IO (Either [Error] System)
parse_system fn = parse_system' $ pure fn

parse_system' :: NonEmpty FilePath -> IO (Either [Error] System)
parse_system' fs = runEitherT $ do
        docs <- liftIO $ mapM readFile fs
        xs <- hoistEither $ flip traverseValidation (NE.zip fs docs) $ 
            \(fn,doc) -> do
                latex_structure fn doc
        hoistEither $ all_machines $ sconcat xs
        
parse_machine :: FilePath -> IO (Either [Error] [Machine])
parse_machine fn = runEitherT $ do
        doc <- liftIO $ readFile fn
        xs  <- hoistEither $ latex_structure fn doc
        ms  <- hoistEither $ all_machines xs
        return $ map snd $ toAscList $ ms!.machines

get_components :: LatexDoc -> LineInfo 
               -> Either [Error] (Map Name [LatexDoc],Map String [LatexDoc])
get_components xs li = 
        liftM g
            $ R.runReader (runEitherT $ W.execWriterT 
                    (mapM_ f $ contents' xs)) li

    where
        with_li li cmd = R.local (const li) cmd
        get_name li xs = with_li li $ liftM fst $ lift $ get_1_lbl xs
        f x@(EnvNode (Env _ tag li0 xs _li1)) 
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
