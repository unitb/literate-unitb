{-# LANGUAGE TypeOperators
    ,QuasiQuotes 
    #-}

module Logic.Expr.QuasiQuote where

    -- Modules
import Document.Proof

import Logic.Expr
import Logic.Expr.Printable
import Logic.Theory

import Theories.Arithmetic

    -- Libraries
import Control.Monad.State hiding (lift)

import Data.Map

import Language.Haskell.TH
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax

import Utilities.Instances
import Utilities.Syntactic

expr :: QuasiQuoter
expr = QuasiQuoter
    { quoteExp  = \x -> [e| \p -> let loc = $(lift =<< location) in parseExpr loc p $(litE (stringL x)) |]
    , quotePat  = undefined
    , quoteDec  = undefined
    , quoteType = undefined }

parseExpr :: Loc -> ParserSetting -> String -> DispExpr
parseExpr loc p str = either (error.("\n"++).show_err) id
            $ parse_expr p (asStringLi li str)
    where li = asLI loc
    -- either fail lift.

ctx :: State ParserSetting a -> (ParserSetting -> b) -> b
ctx cmd f = f r
    where
        r = execState cmd (default_setting $ th_notation empty_theory { _extends = 
                fromList [("arithmetic",arithmetic),("basic",basic_theory)] } )

instance Lift Var where
    lift = defaultLift

instance Lift Expr where
    lift = defaultLift

instance Lift Fun where
    lift = defaultLift

instance Lift HOQuantifier where
    lift = defaultLift

instance Lift QuantifierType where
    lift = defaultLift

instance Lift QuantifierWD where
    lift = defaultLift

instance Lift Lifting where
    lift = defaultLift

instance Lift Value where
    lift = defaultLift

instance Lift Double where
    lift x = litE $ doublePrimL $ toRational x

instance Lift Loc where
    lift (Loc a b c d e) = appsE [conE 'Loc,lift a,lift b,lift c,lift d,lift e]

instance Lift DispExpr where
    lift = defaultLift
