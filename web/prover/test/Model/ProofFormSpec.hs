module Model.ProofFormSpec (spec) where

import TestImport
import Model.ProofForm

import Data.JSON

spec :: Spec
spec = do
    describe "to/from is idempotent" $ do
        it "encodes a ProofForm into a JSON object, decodes it back" $ do
            (decode . encode $ pf) `shouldBe` (Just pf)

    describe "FromJSON" $ do
        it "decodes a JSON object into a ProofForm" $ do
            decode pfStr `shouldBe` (Just pf)

    where
        pf = ProofForm { 
            theories     = fromList [],
            declarations = fromList [],
            assumptions  = fromList [],
            goal         = ("2 = 2" :: String)
        }
        pfStr = concat [
            "{\"theories\":[],\"declarations\":[],",
            "\"assumptions\":[],\"goal\":\"2 = 2\"}" ]
