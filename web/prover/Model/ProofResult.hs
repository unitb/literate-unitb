{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Model.ProofResult where

import ClassyPrelude.Yesod
import Control.Lens hiding ( (.=) )

import Utilities.Syntactic
import qualified Z3.Z3 as Z3

type Result = Either [Error] Z3.Validity

newtype ProofResult = ProofResult {
  _result :: Result
} deriving (Generic, Eq, Show)

makeLenses ''ProofResult

colorClassFromResult :: Result -> Text
colorClassFromResult (Left _) = "alert-danger"
colorClassFromResult (Right v) = case v of
  Z3.Valid      -> "alert-success"
  Z3.Invalid    -> "alert-danger"
  Z3.ValUnknown -> "alert-warning"


iconClassFromResult :: Result -> Text
iconClassFromResult (Left _) = "glyphicon-info-sign"
iconClassFromResult (Right v) = case v of
  Z3.Valid      -> "glyphicon-ok-sign"
  Z3.Invalid    -> "glyphicon-remove-sign"
  Z3.ValUnknown -> "glyphicon-question-sign"


instance FromJSON Error
instance ToJSON Error

instance FromJSON Z3.Validity
instance ToJSON Z3.Validity

instance FromJSON LineInfo
instance ToJSON LineInfo

instance FromJSON ProofResult
instance ToJSON ProofResult where
  toJSON pr@ProofResult{..} = object [
    either
      (\errs -> "error" .= show_err errs)
      (\val -> "result" .= show val)
      (pr ^. result),
    "colorClass" .= colorClassFromResult (pr ^. result),
    "iconClass"  .= iconClassFromResult (pr ^. result)
    ]
