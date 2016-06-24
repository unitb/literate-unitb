{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Model.ProofResult where

import ClassyPrelude.Yesod

import Utilities.Syntactic
import qualified Z3.Z3 as Z3

data ProofResult = ProofResult {
    result :: Either [Error] Z3.Validity
} deriving (Generic, Eq, Show)
