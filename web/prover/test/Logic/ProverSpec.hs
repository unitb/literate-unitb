module Logic.ProverSpec (spec) where

import TestImport
import Logic.Prover
import Model.ProofForm
import Model.ProofResult

import Data.Aeson
import qualified Z3.Z3 as Z3
import Data.Maybe

spec :: Spec
spec = describe "prove" $ do
    it "2 = 2 should be Valid" $ do
        (prove pf1) `shouldReturn` prValid

    it "\\neg 2 = 2 should be Invalid" $ do
         shouldReturn
            (prove . justPFStr . decode $ pfStr2)
            (justPR . decode $ prStrInvalid)

    it "2 /= 2 should cause an error (not Valid or Invalid)" $ do
        (prove pf3) `shouldNotReturn` prValid
        (prove pf3) `shouldNotReturn` (justPR . decode $ prStrInvalid)

    it "x : \\Int, x = 3, x < 3 should be Invalid" $ do
        (prove pf4) `shouldReturn` prInvalid

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
        pf4 = ProofForm {
            theories     = fromList [],
            declarations = fromList [("decl1", "x : \\Int" :: String)],
            assumptions  = fromList [("asm1", ("xIs3", "x = 3"))],
            goal         = ("x < 3" :: String)
        }
        prValid      = ProofResult { _result = Right $ Just Z3.Valid }
        prStrInvalid = "{\"_result\":{\"Right\":\"Invalid\"}}"
        prInvalid    = ProofResult { _result = Right $ Just Z3.Invalid }
        justPFStr = fromJust :: Maybe (ProofForm String) -> ProofForm String
        justPR    = fromJust :: Maybe ProofResult -> ProofResult
