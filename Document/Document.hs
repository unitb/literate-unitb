{-# LANGUAGE ScopedTypeVariables, BangPatterns  #-}
{-# LANGUAGE ExplicitNamespaces, Arrows         #-}
module Document.Document where

    --
    -- Modules
    --
import Document.Machine   as Mch
import Document.Pipeline
import Document.Phase as P
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

import           Control.Monad 
import qualified Control.Monad.Reader as R
import           Control.Monad.Trans
import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans.Either
import           Control.Monad.Trans.RWS as RWS ( runRWS )
import qualified Control.Monad.Writer as W

import           Data.Either.Combinators
import           Data.Map   as M hiding ( map, foldl, (\\) )
import qualified Data.Map   as M
import           Data.Monoid
import           Data.List as L hiding ( union, insert, inits )
import           Data.List.Ordered (sortOn)
import qualified Data.Traversable as T

import Utilities.Syntactic

read_document :: LatexDoc -> Either [Error] System
read_document xs = mapBoth (sortOn line_info . shrink_error_list) id $ do
            let li = line_info xs
            (ms,cs) <- get_components xs li
            runPipeline' ms cs $ proc doc -> do
                let mch = M.map (const ()) $ getMachineInput doc
                    _ctx = M.map (const ()) $ getContextInput doc
                    m0 = M.mapWithKey (const . MachineP0 mch) mch
                    _c0 = M.map (const $ TheoryP0 ()) _ctx
                (r_ord,m1) <- Mch.run_phase1_types -<  m0
                m2 <- Mch.run_phase2_vars   -< (r_ord, m1)
                (m3,es) <- Mch.run_phase3_exprs  -< (r_ord, m2)
                m4 <- Mch.run_phase4_proofs -< (r_ord, m3)
                ms <- liftP' $ fmap Just . T.sequence -< Just $ M.mapWithKey make_machine m4
                machines <- triggerP -< ms
                returnA -< empty_system 
                    { machines = M.mapKeys (\(MId s) -> s) machines 
                    , expr_store = es }

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
        f x@(Env tag li0 xs _li1) 
            | tag == "machine" = do
                    n <- get_name li0 xs
                    W.tell ([(n,[xs])],[])
            | tag == "context" = do
                    n <- get_name li0 xs
                    W.tell ([],[(n,[xs])])
            | otherwise      = map_docM_ f x
        f x = map_docM_ f x
        g (x,y) = (M.fromListWith (++) x, M.fromListWith (++) y)

runPipeline' :: M.Map String [LatexDoc]
             -> M.Map String [LatexDoc]
             -> Pipeline MM Input a 
             -> Either [Error] a
runPipeline' ms cs p = case x of
                            Nothing -> Left w
                            Just x
                                | L.null w -> Right x
                                | otherwise -> Left w 
    where
        (x,(),w) = runRWS (runMaybeT $ f input) input ()
        input = Input mch ctx
        mch   = M.mapKeys MId $ M.map (mconcat . map (getLatexBlocks m_spec)) ms
        ctx   = M.mapKeys CId $ M.map (mconcat . map (getLatexBlocks c_spec)) cs
        Pipeline m_spec c_spec f = p
