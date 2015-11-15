{-# LANGUAGE TypeOperators
    ,QuasiQuotes 
    #-}

module Logic.Expr.QuasiQuote where

    -- Modules
import Document.Proof
import Document.Expression (get_variables'')

import Logic.Expr
import Logic.Expr.Printable
import Logic.Theory

import UnitB.Event

import Theories.Arithmetic
import Theories.FunctionTheory
import Theories.SetTheory

    -- Libraries
import Control.Arrow
import Control.Lens hiding (uncons)
import Control.Monad.Reader hiding (lift)
import Control.Monad.State  hiding (lift)
import Control.Monad.Trans.Either

import Data.Char
import Data.List
import Data.Map as M
import Data.Maybe
import Data.String.Utils as S

import Language.Haskell.TH
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax

import Text.Printf

import Utilities.Instances
import Utilities.Syntactic

expr :: QuasiQuoter
expr = QuasiQuoter
    { quoteExp  = \x -> [e| \p -> let loc = $(lift =<< location) in parseExpr loc p $(litE (stringL x)) |]
    , quotePat  = undefined
    , quoteDec  = undefined
    , quoteType = undefined }

act :: QuasiQuoter
act = QuasiQuoter
    { quoteExp  = \x -> [e| \p -> let loc = $(lift =<< location) in parseAction loc p $(litE (stringL x)) |]
    , quotePat  = undefined
    , quoteDec  = undefined
    , quoteType = undefined }

var :: QuasiQuoter
var = QuasiQuoter
    { quoteExp  = \x -> [e| let loc = $(lift =<< location) in parseVarDecl loc $(litE (stringL x)) |]
    , quotePat  = undefined
    , quoteDec  = undefined
    , quoteType = undefined }

carrier :: QuasiQuoter
carrier = QuasiQuoter
    { quoteExp  = parseTypeDecl
    , quotePat  = undefined
    , quoteDec  = undefined
    , quoteType = undefined }

parseAction :: Loc -> ParserSetting -> String -> Action
parseAction loc p str = Assign v e
    where
        (rVar,rExpr) = second (intercalate ":=") $ fromMaybe err $ uncons (S.split ":=" str)
        v@(Var _ t)  = parseVar loc p rVar
        e  = parseExpr loc p' rExpr
        p' = p & expected_type .~ Just t
        li = asLI loc
        err = error $ "\n"++ show_err [Error (printf "misshapen assignment: '%s'" str) li]

parseVarDecl :: Loc -> String -> State ParserSetting ()
parseVarDecl loc str = do
        ctx <- gets contextOf
        let e  = fromList $ run $ get_variables'' ctx (asStringLi li str)
            e' = M.map f e
            f (Var n t) = Var (S.replace "'" "@prime" n) t
        decls %= M.union e'
    where
        li  = asLI loc
        run = either (error.("\n"++).show_err) id . flip runReader li . runEitherT

parseTypeDecl :: String -> ExpQ -- State ParserSetting ()
parseTypeDecl str = do
        let str'    = strip str
            texName = concatMap f str'
            f '\\'  = "sl@"
            f x     = [x]
            s       = Sort str' texName 0
            
        unless (all isAlphaNum $ dropWhile ('\\' ==) str') 
            $ fail "invalid type name"
        [e| do
                let t       = set_type $ make_type s []
                sorts %= M.insert str' s
                decls %= M.insert str' (Var texName t) |]

primable :: State ParserSetting () -> State ParserSetting ()
primable cmd = do
    s  <- use decls
    cmd
    s' <- use decls
    primed_vars %= M.union (s' `M.difference` s)

parseVar :: Loc -> ParserSetting -> String -> Var
parseVar loc p str = fromMaybe err $ M.lookup n $ p^.decls
    where
        n = strip str
        li = asLI loc
        err = error $ "\n"++ show_err [Error (printf "unknown variables: '%s'" n) li]

parseExpr :: Loc -> ParserSetting -> String -> DispExpr
parseExpr loc p str = either (error.("\n"++).show_err) id
            $ parse_expr p (asStringLi li str)
    where li = asLI loc
    -- either fail lift.

type Ctx = (ParserSetting -> DispExpr) -> DispExpr

impFunctions :: (String,Theory)
impFunctions = ("functions",function_theory)

impSets :: (String,Theory)
impSets = ("sets",set_theory)

ctxWith :: [(String,Theory)] 
        -> State ParserSetting a 
        -> (ParserSetting -> b) -> b
ctxWith xs cmd f = f r
    where
        r = execState cmd (theory_setting $ empty_theory { _extends = 
                fromList $ xs ++ [("arithmetic",arithmetic),("basic",basic_theory)] } )

ctx :: State ParserSetting a 
    -> (ParserSetting -> b) -> b
ctx = ctxWith []

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

instance Lift Loc where
    lift (Loc a b c d e) = appsE [conE 'Loc,lift a,lift b,lift c,lift d,lift e]

instance Lift DispExpr where
    lift = defaultLift
