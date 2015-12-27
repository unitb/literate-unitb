module Logic.Proof 
    ( module Logic.Proof.ProofTree
    , module Logic.Proof.Sequent
    , module Logic.Expr.Label 
    , firstOrderSequent
    )
where

import Logic.Expr.Label hiding ((</>))
import Logic.Proof.ProofTree
import Logic.Proof.Sequent
import Logic.Proof.Lambda

firstOrderSequent :: Sequent -> FOSequent
firstOrderSequent = remove_type_vars . one_point . delambdify . apply_monotonicity
