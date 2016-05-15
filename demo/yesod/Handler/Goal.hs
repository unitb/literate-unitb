module Handler.Goal where

import qualified Data.HashMap.Strict as HM
import qualified Data.Text as T
import GHC.Exts as E

import Import

postGoalR :: Handler Value
postGoalR = do
    goal <- (requireJsonBody :: Handler Value)
    returnJson . revStrings $ goal

revStrings :: Value -> Value
revStrings (String x) = String (T.reverse x)
revStrings (Object x) = let revVal (k, v) = (k, revStrings v)
                        in  Object . E.fromList . map revVal . HM.toList $ x
revStrings other      = other
