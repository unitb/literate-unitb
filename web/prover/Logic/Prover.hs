module Logic.Prover where

import           Logic.Expr hiding ( (</>) )
import           Logic.Proof.Monad hiding (_goal)
import           Logic.Theories
import           Logic.Theories.IntervalTheory (interval_theory)
import           Logic.Theory
import           Utilities.Syntactic
import qualified Z3.Z3 as Z3

import           Control.Lens
import           Control.Precondition
import qualified Data.Map as M
import           Data.Maybe

import           Import

import           Model.ProofForm
import           Model.ProofResult

pfStringToPfStringLi :: ProofForm String -> ProofForm StringLi
pfStringToPfStringLi = imap toStringLi

pfStringLiToSequent :: ProofForm StringLi -> Either [Error] DispSequentWithWD
pfStringLiToSequent (ProofForm t d a g) = runSequent $ do
    let ts = getTheories t
    mapM_ include  ts
    mapM_ declareE (map snd d)
    mapM_ assumeE  (map snd a)
    checkE' g

discharge :: Either [Error] DispSequentWithWD -> IO ProofResult
discharge e = do
    case e of
        Left err ->
            return $ ProofResult { _result = Left err }
        Right s -> do
            val <- Z3.dischargeBoth "goal" s
            return $ ProofResult { _result = Right val }

prove :: ProofForm String -> IO ProofResult
prove = discharge . pfStringLiToSequent . pfStringToPfStringLi

getTheories :: Vector String -> Vector Theory
getTheories = fromList . concat . map getTheory

getTheory :: Pre => String -> [Theory]
getTheory str@"arithmetic" =
    (fromJust . M.lookup (makeName str) $ supportedTheories)
    : interval_theory : []
getTheory str = (fromJust . M.lookup (makeName str) $ supportedTheories) : []

toStringLi :: String -> String -> StringLi
toStringLi lbl = asStringLi . mkLI $ lbl
