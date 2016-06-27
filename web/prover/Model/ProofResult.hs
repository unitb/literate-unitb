{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Model.ProofResult where

import ClassyPrelude.Yesod

import Utilities.Syntactic
import qualified Z3.Z3 as Z3

type Result = Either [Error] Z3.Validity

data ProofResult = ProofResult {
  result :: Result
} deriving (Generic, Eq, Show)

colorClassFromResult :: Result -> Text
colorClassFromResult (Left _) = "alert-danger"
colorClassFromResult (Right v) = case v of
  Z3.Valid      -> "alert-success"
  Z3.Invalid    -> "alert-warning"
  Z3.ValUnknown -> "alert-warning"


iconClassFromResult :: Result -> Text
iconClassFromResult (Left _) = "glyphicon-exclamation-sign"
iconClassFromResult (Right v) = case v of
  Z3.Valid      -> "glyphicon-ok-sign"
  Z3.Invalid    -> "glyphicon-remove-sign"
  Z3.ValUnknown -> "glyphicon-question-sign"
