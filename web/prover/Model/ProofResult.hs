{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Model.ProofResult where

import ClassyPrelude.Yesod
import Control.Lens hiding ( (.=) )

import Logic.Proof.Monad
import Utilities.Syntactic
import qualified Z3.Z3 as Z3

type Result = Either [Error] (SequentWithWD' Z3.Validity)

newtype ProofResult = ProofResult {
  _result :: Result
} deriving (Generic, Eq, Show)

makeLenses ''ProofResult

colorClassFromResult :: Result -> Text
colorClassFromResult (Left _) = "alert-danger"
colorClassFromResult (Right s) = case s of
  SequentWithWD {_wd = Z3.Valid, _goal = v}      -> case v of
    Z3.Valid      -> "alert-success"
    Z3.Invalid    -> "alert-info"
    Z3.ValUnknown -> "alert-warning"
  SequentWithWD {_wd = Z3.Invalid, _goal = _}    -> "alert-warning"
  SequentWithWD {_wd = Z3.ValUnknown, _goal = _} -> "alert-warning"

iconClassFromResult :: Result -> Text
iconClassFromResult (Left _) = "glyphicon-info-sign"
iconClassFromResult (Right s) = case s of
  SequentWithWD {_wd = Z3.Valid, _goal = v}      -> case v of
    Z3.Valid      -> "glyphicon-ok-sign"
    Z3.Invalid    -> "glyphicon-remove-sign"
    Z3.ValUnknown -> "glyphicon-question-sign"
  SequentWithWD {_wd = Z3.Invalid, _goal = _}    -> "glyphicon-info-sign"
  SequentWithWD {_wd = Z3.ValUnknown, _goal = _} -> "glyphicon-info-sign"


instance FromJSON Error
instance ToJSON Error

instance FromJSON Z3.Validity
instance ToJSON Z3.Validity

instance FromJSON LineInfo
instance ToJSON LineInfo

--instance FromJSON ProofResult
instance ToJSON ProofResult where
  toJSON pr@ProofResult{..} = object [
    either
      (\errs -> "error" .= show_err errs)
      (\val -> "result" .= intersperse " " [showValidity (_wd val), showValidity (_goal val)])
      (pr ^. result),
    "colorClass" .= colorClassFromResult (pr ^. result),
    "iconClass"  .= iconClassFromResult (pr ^. result)
    ]

showValidity :: Z3.Validity -> Text
showValidity Z3.Valid      = "Valid"
showValidity Z3.Invalid    = "Invalid"
showValidity Z3.ValUnknown = "Unknown"
