{-# LANGUAGE OverloadedStrings
, DeriveGeneric
, DeriveFunctor #-}
module Model.ProofForm where

import ClassyPrelude.Yesod
import Control.Lens
import Data.Aeson
import Data.Aeson.Types (fieldLabelModifier)

data ProofForm a = ProofForm {
    _theories     :: Vector String,
    _declarations :: Vector (String, a),
    _assumptions  :: Vector (String, (String, a)),
    _goal         :: a
} deriving (Eq, Show, Generic, Functor)

makeLenses ''ProofForm

instance FunctorWithIndex String ProofForm where
  imap f (ProofForm t d a g) = ProofForm
                               t
                               (fmap (\(lbl,decl) -> (lbl, f lbl decl)) d)
                               (fmap (\(x,(lbl,asm)) -> (x,(lbl, f lbl asm))) a)
                               (f "goal" g)

-- Use fieldLabelModifier and drop the underscore (_) from
-- the field names when generating JSON instances.

instance (FromJSON a) => FromJSON (ProofForm a) where
  parseJSON = genericParseJSON defaultOptions {
    fieldLabelModifier = drop 1
    }

instance (ToJSON a) => ToJSON (ProofForm a) where
  toJSON = genericToJSON defaultOptions {
    fieldLabelModifier = drop 1
    }
