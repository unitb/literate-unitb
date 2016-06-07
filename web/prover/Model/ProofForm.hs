module Model.ProofForm where

import ClassyPrelude.Yesod

import Data.Aeson

data ProofForm a = ProofForm {
    theories     :: Vector String,
    declarations :: Vector (String, a),
    goal         :: a
} deriving (Eq, Show)

instance (FromJSON a) => FromJSON (ProofForm a) where
  parseJSON = withObject "proof" $ \o -> do
    theories     <- o .: "theories"
    declarations <- o .: "declarations"
    goal         <- o .: "goal"
    return ProofForm{..}

instance (ToJSON a) => ToJSON (ProofForm a) where
  toJSON ProofForm{..} = object [
    "theories"     .= theories,
    "declarations" .= declarations,
    "goal"         .= goal ]

mkProofForm :: Vector String -> Vector (String, a) -> a -> ProofForm a
mkProofForm ts ds g = ProofForm { 
    theories = ts,
    declarations = ds,
    goal = g }
