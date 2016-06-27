module Handler.Home where

import Import
import Text.Julius (RawJS (..))

import qualified Data.Char as C
import qualified Data.Map as M
import qualified Logic.Theories as Theories
import Logic.Names (render)

-- This is a handler function for the GET request method on the HomeR
-- resource pattern. All of your resource patterns are defined in
-- config/routes
--
-- The majority of the code you will write in Yesod lives in these handler
-- functions. You can spread them across multiple files if you are so
-- inclined, or create a single monolithic file.
getHomeR :: Handler Html
getHomeR = do
    defaultLayout $ do
        let (goalFormId, goalTextareaId) = goalIds
            (declPrefix, declContainerPrefix) = declarationIds
            (asmPrefix, asmContainerPrefix) = assumptionIds
            resultBar = resultBarId
        setTitle "Literate Unit-B"
        $(widgetFile "homepage")


goalIds, declarationIds, assumptionIds :: (Text, Text)
goalIds = ("js-goalForm", "js-goalTextarea")
declarationIds = ("decl", "div-decl")
assumptionIds  = ("asm", "div-asm")

resultBarId :: Text
resultBarId = "resultBar"


theoryNames :: [String]
theoryNames = render <$> M.keys Theories.supportedTheories

capitalize :: String -> String
capitalize (h:rest) = C.toUpper h : (C.toLower <$> rest)
capitalize [] = []
