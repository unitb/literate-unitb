module Logic.Proof 
    ( module Logic.Proof.ProofTree
    , module Logic.Proof.Sequent
    , module Logic.Proof.Tactics 
    , module Logic.Expr.Label )
where

import Logic.Expr.Label hiding ((</>))
import Logic.Proof.ProofTree hiding (context)
import Logic.Proof.Sequent
import Logic.Proof.Tactics
