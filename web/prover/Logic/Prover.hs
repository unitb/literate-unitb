module Logic.Prover where

import Logic.Expr
import Logic.Proof.Monad
import Logic.Theories
import Logic.Theories.IntervalTheory (interval_theory)
import Logic.Theory
import Utilities.Syntactic
import qualified Z3.Z3 as Z3

import Control.Lens
import Control.Precondition
import qualified Data.Map as M
import Data.Maybe

import Import

import Model.ProofForm
import Model.ProofResult

pfStringToPfStringLi :: ProofForm String -> ProofForm StringLi
pfStringToPfStringLi p@(ProofForm _ d a g) =
    p { declarations = d & traverse %~ (\(lbl,decl) -> (lbl, toSringLi lbl decl))
      , assumptions  = a & traverse._2 %~ (\(lbl,asm)  -> (lbl, toSringLi lbl asm))
      , goal = toSringLi "goal" g
    }

pfStringLiToSequent :: ProofForm StringLi -> Either [Error] SequentWithWD
pfStringLiToSequent (ProofForm t d a g) = runSequent $ do
    let theories = getTheories t
    mapM_ include  theories
    mapM_ declareE (map snd d)
    mapM_ assumeE  (map snd $ map snd a)
    checkE g

discharge :: Either [Error] SequentWithWD -> IO ProofResult
discharge e = do
    case e of
        Left err ->
            return $ ProofResult $ Left err
        Right s -> do
            val <- Z3.dischargeBoth "goal" s
            return $ ProofResult $ Right val

prove :: ProofForm String -> IO ProofResult
prove = discharge . pfStringLiToSequent . pfStringToPfStringLi

getTheories :: Vector String -> Vector Theory
getTheories = fromList . concat . map getTheory

getTheory :: Pre => String -> [Theory]
getTheory str@"arithmetic" =
    (fromJust . M.lookup (makeName str) $ supportedTheories)
    : interval_theory : []
getTheory str = (fromJust . M.lookup (makeName str) $ supportedTheories) : []

toSringLi :: String -> String -> StringLi
toSringLi lbl = asStringLi . mkLI $ lbl
