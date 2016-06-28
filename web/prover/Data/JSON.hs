{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.JSON
    (module Data.Aeson)
where

import ClassyPrelude.Yesod
import Control.Lens ((^.))
import Data.Aeson

import Model.ProofForm
import Model.ProofResult

import Utilities.Syntactic
import qualified Z3.Z3 as Z3

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

instance (FromJSON a) => FromJSON (ProofForm a) where
  parseJSON = withObject "proof" $ \o -> do
    theories     <- o .: "theories"
    declarations <- o .: "declarations"
    assumptions  <- o .: "assumptions"
    goal         <- o .: "goal"
    return ProofForm{..}

instance (ToJSON a) => ToJSON (ProofForm a) where
  toJSON ProofForm{..} = object [
    "theories"     .= theories,
    "declarations" .= declarations,
    "assumptions"  .= assumptions,
    "goal"         .= goal ]
