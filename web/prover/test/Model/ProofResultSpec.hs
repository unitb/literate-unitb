module Model.ProofResultSpec (spec) where

import TestImport
import Model.ProofResult

import Data.Aeson

spec :: Spec
spec = do
    describe "to/from is idempotent" $ do
        it "encodes a ProofResult into a JSON object, decodes it back" $ do
            (decode . encode $ pr) `shouldBe` (Just pr)

    describe "FromJSON" $ do
        it "decodes a JSON object into a ProofResult" $ do
            decode prStr `shouldBe` (Just pr)

    where
        pr    = ProofResult { result = ("Valid" :: String) }
        prStr = "{\"result\":\"Valid\"}"
