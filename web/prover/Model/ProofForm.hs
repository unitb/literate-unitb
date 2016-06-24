module Model.ProofForm where

import ClassyPrelude.Yesod

data ProofForm a = ProofForm {
    theories     :: Vector String,
    declarations :: Vector (String, a),
    assumptions  :: Vector (String, (String, a)),
    goal         :: a
} deriving (Eq, Show)
