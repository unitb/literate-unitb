module Logic.Prover where

import Logic.Expr
import Logic.Proof.Monad
import Logic.Proof.Sequent hiding (goal)
import Logic.Theories
import Logic.Theory
import Utilities.Syntactic
import qualified Z3.Z3 as Z3

import Control.Lens
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

pfStringLiToSequent :: ProofForm StringLi -> Either [Error] Sequent
pfStringLiToSequent (ProofForm t d a g) = runSequent $ do
    let theories = getTheories t
    mapM_ include  theories
    mapM_ declareE (map snd d)
    mapM_ assumeE  (map snd $ map snd a)
    checkE g

discharge :: Either [Error] Sequent -> IO ProofResult
discharge e = do
    case e of
        Left err ->
            return $ ProofResult $ Left err
        Right s -> do
            val <- Z3.discharge "goal" s
            return $ ProofResult $ Right val

prove :: ProofForm String -> IO ProofResult
prove = discharge . pfStringLiToSequent . pfStringToPfStringLi

getTheories :: Vector String -> Vector Theory
getTheories = map getTheory

getTheory :: String -> Theory
getTheory str = fromJust . M.lookup (makeName str) $ supportedTheories

toSringLi :: String -> String -> StringLi
toSringLi lbl = asStringLi . mkLI $ lbl
