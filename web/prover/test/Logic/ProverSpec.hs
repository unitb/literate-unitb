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
        pf1 = ProofForm {
            theories     = fromList [],
            declarations = fromList [],
            assumptions  = fromList [],
            goal         = ("2 = 2" :: String)
        }
        pfStr2 = concat [
            "{\"theories\":[],\"declarations\":[],",
            "\"assumptions\":[],\"goal\":\"\\\\neg 2 = 2\"}" ]
        pf3 = ProofForm {
            theories     = fromList [],
            declarations = fromList [],
            assumptions  = fromList [],
            goal         = ("2 /= 2" :: String)
        }
        pr1    = ProofResult { result = ("Valid" :: String) }
        prStr2 = "{\"result\":\"Invalid\"}"
        justPFStr = fromJust :: Maybe (ProofForm String) -> ProofForm String
        justPRStr = fromJust :: Maybe (ProofResult String) -> ProofResult String
