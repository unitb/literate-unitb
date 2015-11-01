{-# LANGUAGE ScopedTypeVariables, BangPatterns  #-}
{-# LANGUAGE ExplicitNamespaces, Arrows         #-}
module Document.Document where

    --
    -- Modules
    --
import Document.Machine   as Mch
import Document.Pipeline
import Document.Phase as P
import Document.Phase.Structures as Mch
import Document.Phase.Declarations as Mch
import Document.Phase.Expressions as Mch
import Document.Phase.Proofs as Mch
import Document.Visitor

import Latex.Parser

import Logic.Expr
import Logic.Proof

import UnitB.AST as AST
import UnitB.PO

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
import           Data.Map   as M hiding ( map, foldl, (\\) )
import           Data.List.Ordered (sortOn)

import Utilities.Syntactic

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
                machines <- liftP id -< m4 & mchTable (M.traverseWithKey make_machine)
                -- let ms = _ -- M.mapWithKey make_machine m4 :: MTable (Either [Error] Machine)
                -- machines <- triggerP -< _ ms
                -- let refs' = M.mapKeys as_label $ M.map as_label $ P.edges $ r_ord
                    -- mam2maybe = fmap (as_label . fst) . (() `M.lookup`)
                --     check0 = forM_ (keys mch) $ \m -> check_schedule_ref_struct
                --                 refs' (as_label m)
                --                 _ -- (prog_dep ! m)
                --                 (events $ machines ! m)
                --                 (transient $ props $ machines ! m)
                --                 ((m4 ! m) ^. pProgress) -- exprs ! m)
                -- liftP -< toEither check0
                returnA -< empty_system 
                    { machines = M.mapKeys (\(MId s) -> s) $ machines^.mchTable }


all_machines :: LatexDoc -> Either [Error] System
all_machines xs = read_document xs

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

get_components :: LatexDoc -> LineInfo 
               -> Either [Error] (M.Map String [LatexDoc],M.Map String [LatexDoc])
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
                    W.tell ([(n,[xs])],[])
            | tag == "context" = do
                    n <- get_name li0 xs
                    W.tell ([],[(n,[xs])])
            | otherwise      = map_docM_ f x
        f x = map_docM_ f x
        g (x,y) = (M.fromListWith (++) x, M.fromListWith (++) y)
