module Logic.ProverSpec (spec) where

import TestImport
import Logic.Prover
import Model.ProofForm
import Model.ProofResult

import Data.Aeson
import Data.Maybe

spec :: Spec
spec = describe "prove" $ do
    it "2 = 2 should be Valid" $ do
        (prove pf1) `shouldReturn` pr1

    it "\\neg 2 = 2 should be Invalid" $ do
         shouldReturn
            (prove . justPFStr . decode $ pfStr2)
            (justPRStr . decode $ prStr2)

    it "2 /= 2 should cause an error (not Valid or Invalid)" $ do
        (prove pf3) `shouldNotReturn` pr1
        (prove pf3) `shouldNotReturn` (justPRStr . decode $ prStr2)

    where
        pf1    = mkProofForm (fromList []) (fromList []) ("2 = 2" :: String)
        pfStr2 = "{\"theories\":[],\"declarations\":[],\"goal\":\"\\\\neg 2 = 2\"}"
        pf3    = mkProofForm (fromList []) (fromList []) ("2 /= 2" :: String)
        pr1    = mkProofResult ("Valid" :: String)
        prStr2 = "{\"result\":\"Invalid\"}"
        justPFStr = fromJust :: Maybe (ProofForm String) -> ProofForm String
        justPRStr = fromJust :: Maybe (ProofResult String) -> ProofResult String
