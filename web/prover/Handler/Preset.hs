module Handler.Preset where

import Import

import Model.Presets

postPresetR :: Handler Value
postPresetR = do
    (presetId, itemId) <- requireJsonBody :: Handler (Int, Int)
    returnJson $ (getPresetItem presetId itemId :: PresetItem Text)
