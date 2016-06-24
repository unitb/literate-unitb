module Handler.Goal where

import Import

import Data.JSON()
import Logic.Prover
import Model.ProofForm

postGoalR :: Handler Value
postGoalR = do
    pf <- requireJsonBody :: Handler (ProofForm String)
    liftIO $ prove pf >>= returnJson
