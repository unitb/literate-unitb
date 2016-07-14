module Handler.Home where

import Import
import Text.Julius (RawJS (..))

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
        jsReqWarning <- newIdent
        setTitle "Literate Unit-B"
        $(widgetFile "homepage")


goalIds :: (Text, Text, Text)
goalIds = ("js-goalForm", "js-createGoalTextarea", "js-goalList")