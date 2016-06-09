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
        let (goalFormId, goalTextareaId, goalListId) = goalIds
        let (declPrefix, declContainerPrefix) = declarationIds
        let (asmPrefix, asmContainerPrefix) = assumptionIds
        jsReqWarning <- newIdent
        setTitle "Literate Unit-B"
        $(widgetFile "homepage")


goalIds :: (Text, Text, Text)
goalIds = ("js-goalForm", "js-goalTextarea", "js-goalList")

declarationIds :: (Text, Text)
declarationIds = ("decl", "div-decl")

assumptionIds :: (Text, Text)
assumptionIds = ("asm", "div-asm")

theoryNames :: [String]
theoryNames = render <$> M.keys Theories.supportedTheories

capitalize :: String -> String
capitalize (h:rest) = C.toUpper h : (C.toLower <$> rest)
capitalize [] = []
