module Model.Presets where

import ClassyPrelude.Yesod
import Control.Exception   (throw)
import Data.Aeson          (Result (..), fromJSON, withObject)
import Data.FileEmbed      (embedFile)
import Data.Yaml

import Model.ProofForm

data PresetItem a = PresetItem {
    desc :: a,
    form :: ProofForm a
}

data Preset a = Preset {
    name  :: a,
    items :: [PresetItem a]
}

type Presets a = [Preset a]

-- | Raw bytes at compile time of @config/presets.yml@
presetsYmlBS :: ByteString
presetsYmlBS = $(embedFile "config/presets.yml")

-- | @config/presets.yml@, parsed to a @Value@.
presetsYmlValue :: Value
presetsYmlValue = either throw id $ decodeEither' presetsYmlBS

-- | @presets@ parsed from @config/presets.yml@.
presets :: Presets Text
presets =
    case fromJSON presetsYmlValue of
        Error e -> error e
        Success ps -> ps


instance (FromJSON a) => FromJSON (PresetItem a) where
  parseJSON = withObject "PresetItem" $ \o -> do
    desc  <- o .: "desc"
    form  <- o .: "form"
    return PresetItem{..}

instance (ToJSON a) => ToJSON (PresetItem a) where
  toJSON PresetItem{..} = object [
    "desc"  .= desc,
    "form"  .= form ]

instance (FromJSON a) => FromJSON (Preset a) where
  parseJSON = withObject "Preset" $ \o -> do
    name   <- o .: "name"
    items  <- o .: "items"
    return Preset{..}

instance (ToJSON a) => ToJSON (Preset a) where
  toJSON Preset{..} = object [
    "name"   .= name,
    "items"  .= items ]
