{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

module Handler.Goal where
import Import

import Data.Aeson

data ProofForm = ProofForm {
    theories     :: Vector Text,
    declarations :: Vector Text,
    goal         :: Text
}

instance FromJSON ProofForm where
  parseJSON = withObject "proof" $ \o -> do
    theories     <- o .: "theories"
    declarations <- o .: "declarations"
    goal         <- o .: "goal"
    return ProofForm{..}

instance ToJSON ProofForm where
  toJSON ProofForm{..} = object [
    "theories"     .= theories,
    "declarations" .= declarations,
    "goal"         .= goal ]

postGoalR :: Handler Value
postGoalR = do
    pf <- requireJsonBody :: Handler ProofForm
    returnJson pf
