module Model.Presets where

import ClassyPrelude.Yesod hiding (fromList)
import Control.Exception   (throw)
import Data.Aeson          (Result (..), fromJSON, withObject)
import Data.FileEmbed      (embedFile)
import Data.IntMap         ((!), fromList)
import Data.Yaml

import Model.ProofForm

data PresetItem a = PresetItem {
    piid :: Int,
    desc :: a,
    form :: ProofForm a
}

data Preset a = Preset {
    pname  :: a,
    pitems :: [PresetItem a]
}

data PresetMap a = PresetMap {
    pmid    :: Int,
    name  :: a,
    items :: IntMap (PresetItem a)
}

-- | Raw bytes at compile time of @config/presets.yml@
presetsYmlBS :: ByteString
presetsYmlBS = $(embedFile "config/presets.yml")

-- | @config/presets.yml@, parsed to a @Value@.
presetsYmlValue :: Value
presetsYmlValue = either throw id $ decodeEither' presetsYmlBS

-- | @presets@ parsed from @config/presets.yml@.
presets :: (FromJSON a, ToJSON a) => [Preset a]
presets =
    case fromJSON presetsYmlValue of
        Error e -> error e
        Success ps -> ps

presetItemMap :: (FromJSON a, ToJSON a) => [PresetItem a] -> IntMap (PresetItem a)
presetItemMap pis = fromList [(i, presetItem {piid = i}) | (i, presetItem) <- pis']
    where pis' = zip [0..] pis

presetToPresetMap :: (FromJSON a, ToJSON a) => Int -> Preset a -> PresetMap a
presetToPresetMap i p = PresetMap { pmid = i, name = pname p, items = presetItemMap $ pitems p }

presetMaps :: (FromJSON a, ToJSON a) => [Preset a] -> IntMap (PresetMap a)
presetMaps ps = fromList [(i, presetToPresetMap i preset) | (i, preset) <- ps']
    where ps' = zip [0..] ps

getPresetItem :: (FromJSON a, ToJSON a) => Int -> Int -> PresetItem a
getPresetItem presetId itemId = items ((presetMaps presets) ! presetId) ! itemId


instance (FromJSON a) => FromJSON (PresetItem a) where
  parseJSON = withObject "PresetItem" $ \o -> do
    desc  <- o .: "desc"
    form  <- o .: "form"
    return PresetItem{piid = 0,..}

instance (ToJSON a) => ToJSON (PresetItem a) where
  toJSON PresetItem{..} = object [
    "id"    .= piid,
    "desc"  .= desc,
    "form"  .= form ]

instance (FromJSON a) => FromJSON (Preset a) where
  parseJSON = withObject "Preset" $ \o -> do
    pname  <- o .: "name"
    pitems <- o .: "items"
    return Preset{..}

instance (ToJSON a) => ToJSON (Preset a) where
  toJSON Preset{..} = object [
    "name"  .= pname,
    "items" .= pitems ]

instance (FromJSON a) => FromJSON (PresetMap a) where
  parseJSON = withObject "PresetMap" $ \o -> do
    name  <- o .: "name"
    items <- o .: "items"
    return PresetMap{pmid = 0,..}

instance (ToJSON a) => ToJSON (PresetMap a) where
  toJSON PresetMap{..} = object [
    "id"    .= pmid,
    "name"  .= name,
    "items" .= items ]
