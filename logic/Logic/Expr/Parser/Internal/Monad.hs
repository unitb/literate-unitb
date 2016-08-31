module Logic.Expr.Parser.Internal.Monad where

    -- Modules
import Latex.Scanner 

import Logic.Expr
import Logic.Expr.Parser.Internal.Scanner 
import Logic.Expr.Parser.Internal.Setting
import Logic.Operator

    -- Libraries
import qualified Control.Applicative as A 
import Control.Lens hiding (Context,from)

import           Control.Monad
import           Control.Monad.Trans
import           Control.Monad.Trans.Maybe
import qualified Control.Monad.Trans.Reader as R

import           Data.List as L
import           Data.Map.Class as M hiding ( map )
import qualified Data.Map.Class as M

import Utilities.Syntactic
import Utilities.Table

data Param = Param 
    { context   :: Context
    , notation  :: Notation
    , variables :: Table Name UntypedExpr
    }

data Parser a = Parser { fromParser :: MaybeT (R.ReaderT Param (Scanner ExprToken)) a }
    deriving (Functor)

-- instance Functor Parser where
--     fmap = liftM

instance A.Applicative Parser where
    f <*> x = f `ap` x
    pure = return

instance A.Alternative Parser where
    m0 <|> m1 = m0 `mplus` m1
    empty     = mzero

instance Monad Parser where
    Parser m0 >>= f = Parser $ m0 >>= (fromParser . f)
    return x = Parser $ return x
    fail x   = Parser $ lift $ fail x

instance MonadPlus Parser where
    Parser m0 `mplus` Parser m1 = Parser $ m0 `mplus` m1
    mzero = Parser mzero
    
get_params :: Parser Param
get_params = Parser $ lift R.ask

look_aheadP :: Parser a -> Parser Bool
look_aheadP = liftHOF look_ahead

liftP :: Scanner ExprToken a -> Parser a
liftP = Parser . lift . lift

liftHOF :: (   Scanner ExprToken a
            -> Scanner ExprToken b )
        -> Parser a -> Parser b
liftHOF f m = do
        x <- get_params
        liftP $ f $ runParserWith x m

tryP :: Parser a -> (a -> Parser b) -> Parser b -> Parser b
tryP m0 m1 m2 = do
        x <- get_params
        let run m = R.runReaderT (runMaybeT $ fromParser m) x
        Parser $ MaybeT $ R.ReaderT $ const $ try 
            (run m0) 
            (\k -> case k of
                    Just x  -> run $ m1 x
                    Nothing -> run m2)
            (run m2)

choiceP :: [Parser a] -> Parser a -> (a -> Parser a) -> Parser a
choiceP xs x final = do
        y <- get_params
        liftP $ choice 
            (map (runParserWith y) xs)
            (runParserWith y x)
            (runParserWith y . final)

getToken :: Prism' ExprToken a 
         -> String
         -> Parser a
getToken pr lb = liftP $ do
            x <- read_char
            case x^?pr of
                Just x -> return x
                _ -> fail $ "expecting a \'" ++ lb ++ "\': " ++ lexeme x

manyP :: Parser a -> Parser [a]
manyP p = do
        x <- get_params
        liftP $ many
            (runParserWith x p)

sepP :: Parser a -> Parser b -> Parser [a]
sepP m0 m1 = do
        x <- get_params
        liftP $ sep
            (runParserWith x m0)
            (runParserWith x m1)

sep1P :: Parser a -> Parser b -> Parser [a]
sep1P m0 m1 = do
        x <- get_params
        liftP $ sep1 
            (runParserWith x m0)
            (runParserWith x m1)

choose_la :: [Parser a] -> Parser a
choose_la (x:xs) = do
        x `mplus` choose_la xs
choose_la [] = mzero

add_context :: String -> Parser a -> Parser a
add_context _ cmd = cmd

attempt :: Parser a -> Parser a
attempt cmd = do
        tryP cmd 
            return 
            (Parser $ fail (error "Expression.attempt: shouldn't be evaluated"))

runParser' :: ParserSetting 
           -> Parser a 
           -> Scanner ExprToken a
runParser' p = runParserWith $ Param 
        ctx 
        (p^.language) 
        vars'
    where
        -- | f <$> y
        -- | x <$ y = const x <$> y
        -- | f <$> Just x  = Just (f x)
        -- | f <$> Nothing = Nothing
        -- | const x _ = x
        -- |   x <$ Just y
        -- | = const x <$> Just y
        -- | = Just (const x y)
        -- | = Just x
        ctx = contextOf p
        vars  = (() <$) <$> ctx^.constants
        vars' = M.map Word vars `M.union` M.mapMaybe f defs
        f (Def xs n args t _e) = do
                guard (L.null args)
                Just $ funApp (mk_fun xs n [] t) []
        defs = ctx^.definitions
            
runParser :: Context -> Notation 
          -> Table Name UntypedExpr
          -> Parser a 
          -> Scanner ExprToken a
runParser x y w m = runParserWith (Param x y w) m

runParserWith :: Param -> Parser a -> Scanner ExprToken a
runParserWith x m = do
        x <- R.runReaderT (runMaybeT $ fromParser m) x
        maybe (fail "runParserWith: unmatched lookahead") return x

contextOf :: ParserSetting -> Context
contextOf set = Context (set^.sorts) (unions [set^.decls, ctx0, ctx1]) M.empty M.empty (set^.dum_ctx)
    where
        ctx0
            | set^.is_step = primeAll $ set^.primed_vars
            | otherwise    = M.empty
        ctx1 
            | set^.free_dummies = set^.dum_ctx
            | otherwise         = M.empty
