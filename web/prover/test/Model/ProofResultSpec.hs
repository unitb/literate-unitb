module Model.ProofResultSpec (spec) where

import TestImport
import Model.ProofResult

import Control.Lens ((^.))
import Data.Aeson
import qualified Data.Text.Lazy as T
import qualified Data.Text.Lazy.Encoding as T
import qualified Z3.Z3 as Z3

spec :: Spec
spec = do
    describe "ToJSON" $ do
        it "encodes a ProofResult into a JSON object" $ do
            encode pr `shouldBe` T.encodeUtf8 prStr2

    describe "FromJSON" $ do
        it "decodes a JSON object into a ProofResult" $ do
            decode prStr `shouldBe` (Just pr)

    where
        pr    = ProofResult { _result = Right $ Just Z3.Valid }
        prStr = "{\"_result\":{\"Right\":\"Valid\"}}"
        prStr2 = T.concat
            [ "{\"result\":\"Valid\","
            , "\"iconClass\":\""
            , T.fromStrict $ iconClassFromResult (pr ^. result)
            , "\",\"colorClass\":\""
            , T.fromStrict $ colorClassFromResult (pr ^. result)
            , "\"}"
            ]
