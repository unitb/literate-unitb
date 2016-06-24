module Model.ProofResultSpec (spec) where

import TestImport
import Model.ProofResult

import Data.JSON
import qualified Z3.Z3 as Z3

spec :: Spec
spec = do
    describe "to/from is idempotent" $ do
        it "encodes a ProofResult into a JSON object, decodes it back" $ do
            (decode . encode $ pr) `shouldBe` (Just pr)

    describe "FromJSON" $ do
        it "decodes a JSON object into a ProofResult" $ do
            decode prStr `shouldBe` (Just pr)

    where
        pr    = ProofResult { result = Right Z3.Valid }
        prStr = "{\"result\":{\"Right\":\"Valid\"}}"
