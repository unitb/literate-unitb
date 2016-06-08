{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Model.ProofResult where

import ClassyPrelude.Yesod

data ProofResult a = ProofResult {
    result :: a
} deriving (Generic, ToJSON, FromJSON, Eq, Show)
