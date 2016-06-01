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

pfStringToPfStringLi :: ProofForm String -> ProofForm StringLi
pfStringToPfStringLi p@(ProofForm _ d g) =
    p { declarations = d & traverse %~ (\(lbl,decl) -> (lbl, toSringLi lbl decl))
      , goal = toSringLi "goal" g
    }

pfStringLiToSequent :: ProofForm StringLi -> Sequent
pfStringLiToSequent (ProofForm t d g) = runSequent $ do
    let theories = getTheories t
    mapM_ include theories
    mapM_ declareE (map snd d)
    goalE g

discharge :: Sequent -> IO (Either String String)
discharge s = do
    val <- Z3.discharge "goal" s
    case val of
        Z3.Valid -> return $ Right "Valid"
        Z3.Invalid -> return $ Left "Invalid"
        Z3.ValUnknown -> return $ Left "Unknown"

getTheories :: Vector String -> Vector Theory
getTheories = map getTheory

getTheory :: String -> Theory
getTheory str = fromJust . M.lookup (makeName str) $ supportedTheories

toSringLi :: String -> String -> StringLi
toSringLi lbl = asStringLi . mkLI $ lbl
