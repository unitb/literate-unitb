module UnitB.QuasiQuote
    ( module UnitB.QuasiQuote
    , module Logic.QuasiQuote
    )
where

import Logic.Expr
import Logic.Expr.Parser
import Logic.QuasiQuote

    -- Libraries
import Control.Arrow
import Control.Lens hiding (uncons)

import Data.List
import Data.Maybe
import Data.String.Utils as S

import Language.Haskell.TH hiding (Name)
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax hiding (Name)

import Text.Printf.TH

import UnitB.Event
import UnitB.Property

import Utilities.Syntactic

act :: QuasiQuoter
act = QuasiQuoter
    { quoteExp  = \x -> [e| \p -> let loc = $(lift =<< location) in parseAction loc p $(litE (stringL x)) |]
    , quotePat  = undefined
    , quoteDec  = undefined
    , quoteType = undefined }

safe :: QuasiQuoter 
safe = QuasiQuoter
    { quoteExp  = \x -> [e| \p -> let loc = $(lift =<< location) in parseSafetyProp loc p $(litE (stringL x)) |]
    , quotePat  = undefined
    , quoteDec  = undefined
    , quoteType = undefined }

prog :: QuasiQuoter
prog = QuasiQuoter
    { quoteExp = \x -> [e| \p -> let loc = $(lift =<< location) in parseProgressProp loc p $(litE (stringL x)) |]
    , quotePat = undefined
    , quoteDec = undefined
    , quoteType = undefined
    }

parseAction :: Loc -> ParserSetting -> String -> Action
parseAction loc p str = Assign v e
    where
        (rVar,rExpr) = second (intercalate ":=") $ fromMaybe err $ uncons (S.split ":=" str)
        v@(Var _ t)  = parseVar loc p rVar
        e  = parseExpr loc p' rExpr
        p' = p & expected_type .~ Just t
        li = asLI loc
        err = error $ "\n"++ show_err [Error ([s|misshapen assignment: '%s'|] str) li]

parseSafetyProp :: Loc -> ParserSetting -> String -> SafetyProp
parseSafetyProp = parseParts makeSafety "UNLESS" "safety property" parseExpr parseExpr
    where
        makeSafety e0 e1 = Unless [] e0 e1

parseProgressProp :: Loc -> ParserSetting -> String -> ProgressProp
parseProgressProp = parseParts makeProgress "LEADS-TO" "progress property" parseExpr parseExpr
    where
        makeProgress e0 e1 = LeadsTo [] e0 e1
