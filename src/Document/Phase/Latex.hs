{-# LANGUAGE ScopedTypeVariables,Arrows
        ,ConstraintKinds
        ,ExistentialQuantification
        ,LiberalTypeSynonyms
        ,ImpredicativeTypes
        ,KindSignatures #-}
module Document.Phase.Latex 
    ( module Document.Phase.Latex 
    , Alt (..) )
where

    -- Modules
import Document.Phase.Parameters
import Document.Visitor (M,unM)

import Latex.Parser

import UnitB.Syntax hiding (Constraint)

    -- Libraries
import Control.Applicative
import Control.Arrow
import Control.Arrow.Unfold
import Control.Category
import Control.Lens
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Either
import Control.Monad.Trans.Maybe
import Control.Precondition

import Data.Either.Validation
import Data.Existential
import Data.Functor.Alt
import Data.Functor.Compose
import Data.List as L
import Data.Map as M
import Data.Proxy.TH
import Data.Tuple.Generics
import Data.Typeable
--import Data.Validation
--import Data.Validation (ValidationT(..),_Either)
--import qualified Data.Validation as V

--import GHC.Exts (Constraint)

import Prelude hiding ((.),id)

import Text.Printf.TH

import Utilities.Syntactic

data LatexMatch = CmdMatch String [Bracket] | EnvMatch Environment

makePrisms ''LatexMatch

type LatexParser = LatexParserA ()
type LatexParserA = LatexParserT M

data LatexParserT m a b = LatexParser 
        { _expectedEnv :: [String] 
        , _expectedCmd :: [(String,Cell1 Proxy (IsTuple LatexArg))] 
        , envLookAhead :: [String] 
        , cmdLookAhead :: [String] 
        , _hasNull :: Bool
        , _runLatexParser :: a -> ValState m b
        }
    deriving (Functor)

type ValState m = EitherT [Error] (StateT (TokenStream LatexMatch) m)

makeLenses ''LatexParserT

first' :: Monad m => (a -> m b) -> ((a,c) -> m (b,c))
first' = kleisli' %~ first

instance ArrowUnfold LatexParserA where
    fixExA = runLatexParser.kleisli' %~ fixExA

instance Applicative (LatexParserA a) where
    pure = LatexParser [] [] [] [] True . pure . pure
    f <*> x = (f &&& x) >>> arr (uncurry ($))

instance Arrow (LatexParserA) where
    arr f = lift' $ pure . f
    first = runLatexParser %~ first'
instance Category LatexParserA where
    id = arr id
    LatexParser xs0 ys0 eLu0 cLu0 e0 f . LatexParser xs1 ys1 eLu1 cLu1 e1 g
        | e0        = LatexParser (xs0++xs1) (ys0++ys1) (eLu0++eLu1) (cLu0++cLu1) e1 $ f <=< g
        | otherwise = LatexParser (xs0++xs1) (ys0++ys1) eLu0 cLu0 False $ f <=< g

withLineInfo :: MonadReader LineInfo m
             => LatexParserT m a b 
             -> LatexParserT m a b
withLineInfo = runLatexParser.mapped %~ \cmd -> do
        li <- gets line_info
        local (const li) cmd

fromMonad :: MonadReader LineInfo m
          => (a -> ValState m b)
          -> LatexParserT m a b
fromMonad = LatexParser [] [] [] [] True

lift' :: MonadReader LineInfo m
      => (a -> m b)
      -> LatexParserT m a b
lift' f = fromMonad $ lift . lift . f

--readEnv :: String -> LatexParser Environment
--readEnv tok = token $ _EnvMatch.prism id f
--    where
--        f e | envType e == tok = Right e
--            | otherwise        = Left e

readEnv :: String -> LatexParser Environment
readEnv tag = LatexParser [tag] [] [tag] [] False $ \() -> EitherT $ do
            xs <- get
            case unconsStream xs of
                Just (EnvMatch e,_,xs) 
                    | envType e == tag -> do
                        put xs
                        return $ Right e
                _ -> return $ Left [Error ([s|expecting environment '%s'|] tag) $ line_info xs]

insideOneEnvOf :: Pre
               => [String] 
               -> LatexParserA a b
               -> LatexParserA a b
insideOneEnvOf [] _ = undefined'
insideOneEnvOf [tag] m = insideEnv tag m
insideOneEnvOf (x0:x1:xs) m = insideEnv x0 m <!> insideOneEnvOf (x1:xs) m

insideEnv :: String -> LatexParserA a b
          -> LatexParserA a b
insideEnv tag cmd = proc x -> do
    d <- arr contents <<< readEnv tag -< ()
    withLineInfo $ lift' (\(d,x) -> parseLatex cmd d x) -< (d,x)

--readCommand :: forall a. IsTuple LatexArg a 
--            => String -> LatexParser a
--readCommand = _

withCommand :: (Typeable a,IsTuple LatexArg a)
            => String 
            -> (a -> M b)
            -> LatexParser b
withCommand tag cmd = withLineInfo $ readCommand tag >>> lift' cmd

readCommand :: forall a. (Typeable a,IsTuple LatexArg a)
            => String -> LatexParser a
readCommand tag = provided ("\\" `isPrefixOf` tag) 
        $ LatexParser [] [(tag,tupleType)] [] [tag] False
        $ \() -> EitherT $ do
            xs <- get
            case unconsStream xs of
                Just (CmdMatch t x,_,xs) 
                    | t == tag -> do
                        put xs
                        return $ evalState (getCompose $ makeTuple' [pr|LatexArg|] next) x
                _ -> return $ Left [Error ([s|expecting command '%s'|] tag) $ line_info xs]
    where
        tupleType = Cell [pr|a|]
        next :: forall b. LatexArg b 
             => Compose (State [Bracket]) (Either [Error]) b
        next = Compose $ do
                x <- gets $ contents . BracketNode . head
                modify tail
                return $ read_one x

consume' :: LatexParserA (Either [Error] a) a
consume' = fromMonad $ EitherT . pure
    -- (pure ()) { _runLatexParser = ValidationT . pure . eitherToValidation }

--consumeV' :: LatexParserA (Validation [Error] a) a
--consumeV' = consume' <<< arr validationToEither

consume :: Either [Error] a
        -> LatexParser a
consume x = pure x >>> consume'

--consumeV :: Validation [Error] a
--         -> LatexParser a
--consumeV = consume . validationToEither

compose :: Iso (f (g a)) (f' (g' a')) (Compose f g a) (Compose f' g' a')
compose = iso Compose getCompose

eithT :: Iso (EitherT e m a) (EitherT e' m' a') (m (Either e a)) (m' (Either e' a'))
eithT = iso runEitherT EitherT

recCall :: LatexParserT m a b -> LatexParserT m a b
recCall = (hasNull .~ True) . (expectedEnv .~ []) . (expectedCmd .~ [])

parseLatex :: LatexParserA a b
           -> LatexDoc
           -> a -> M b
parseLatex cmd doc x = parseLatexT cmd doc x & unM.eithT.mapped %~ join

parseLatexT :: Monad m
            => LatexParserT m a b
            -> LatexDoc
            -> a
            -> m (Either [Error] b)
parseLatexT (LatexParser env cmd _eLu _cLu _e f) xs x = runEitherT $ do
    --fmap join $  fmap (fmap validationToEither)
    --          $  fmap validationToEither
        pruned <- hoistEither $ validationToEither 
            $ rewriteDoc (fromList $ (,()) <$> env) (fromList cmd) xs
        EitherT $ evalStateT (runEitherT $ f x) pruned

rewriteDoc :: Map String ()
           -> Map String (Cell1 Proxy (IsTuple LatexArg))
           -> LatexDoc
           -> Validation [Error] (TokenStream LatexMatch)
rewriteDoc es cs d = case unconsTex d of
        Just (EnvNode e,doc)
            | envType e `member` es -> ((EnvMatch e,line_info d) `consStream`) <$> rewriteDoc es cs doc
            | otherwise -> rewriteDoc es cs 
                $ prependNodes (contents' $ contents $ EnvNode e) doc
        Just (Text t,doc) -> fromMaybe (rewriteDoc es cs doc) $ do
                (tag',li) <- t^?_Command
                argSpec <- M.lookup tag' cs
                let n = readCell1 (len [pr|LatexArg|]) argSpec
                    docs = readCell1 (foldMapTupleType [pr|LatexArg|] ((:[]) . argKind)) argSpec
                    docs' = concatMap ([s|{%s}|]) docs :: String
                    (args,doc') = takeArgs n doc
                    checkedArgs | length args == n = pure args
                                | otherwise        = Failure [Error ([s|expecting %d arguments: %s|] n docs') li]
                return $ consStream . (,li) . CmdMatch tag' 
                            <$> checkedArgs 
                            <*> rewriteDoc es cs doc'
        Just (BracketNode _,doc) -> rewriteDoc es cs doc
        Nothing -> pure $ stream $ line_info d

takeArgs :: Int -> LatexDoc -> ([Bracket], LatexDoc)
takeArgs 0 d = ([],d)
takeArgs n d = case unconsTex d of
                    Just (Text (Blank _ _),doc) -> takeArgs n doc
                    Just (BracketNode br,doc) -> takeArgs (n-1) doc & _1 %~ (br:)
                    _ -> ([],d)

instance Alt (LatexParserA a) where
    --empty = _
    x <!> y = provided b $
            LatexParser 
            { _expectedEnv  = _expectedEnv x  ++ _expectedEnv y 
            , _expectedCmd  = _expectedCmd x  ++ _expectedCmd y 
            , envLookAhead = envLookAhead x ++ envLookAhead y
            , cmdLookAhead = cmdLookAhead x ++ cmdLookAhead y
            , _hasNull = _hasNull x || _hasNull y
            , _runLatexParser = \arg -> do
                    x <- matchLookAhead x arg
                    maybe (_runLatexParser y arg) 
                        return x
            }
        where
            b = L.null (intersect (envLookAhead x) (envLookAhead y)) 
                && L.null (intersect (cmdLookAhead x) (cmdLookAhead y))

exViewA' :: forall f constr c r. (HasCell c (Cell1 f constr))
         => (forall a. LatexParserA (Inst1 f constr a) r)
         -> LatexParserA c r
exViewA' a = exLensA' (a >>> arr Const) >>> arr getConst

exLensA' :: forall f g constr c. (Functor g,HasCell c (Cell1 f constr))
         => (forall a. LatexParserA (Inst1 f constr a) (g (f a)))
         -> LatexParserA c (g c)
exLensA' a = arr (view cell) >>> exLensA a >>> arr (fmap $ view $ from cell)

exLensA :: forall f g constr. Functor g
        => (forall a. LatexParserA (Inst1 f constr a) (g (f a)))
        -> LatexParserA (Cell1 f constr) (g (Cell1 f constr))
exLensA cmd = cmd & (runLatexParser .~ getCompose . traverseCell1 (Compose . f . Inst)) 
        -- getCompose . traverseCell1 (Compose . f)
    where
        f :: forall a. (Inst1 f constr a) -> ValState M (g (f a))
        f = _runLatexParser cmd

getLineInfo :: LatexParserA a LineInfo
getLineInfo = fromMonad $ \_ -> gets line_info

withLookAhead :: LatexParserA a b 
              -> LatexParserA a (Maybe b)
withLookAhead x = x & runLatexParser .~ matchLookAhead x

matchLookAhead :: LatexParserA a b
               -> a
               -> EitherT [Error] (StateT (TokenStream LatexMatch) M) (Maybe b)
matchLookAhead cmd arg = runMaybeT $ do
        (x,_li,_xs) <- MaybeT $ lift $ gets unconsStream
        case x of
            CmdMatch n _ 
                | n `elem` cmdLookAhead cmd || _hasNull cmd 
                    -> lift $ _runLatexParser cmd arg
            EnvMatch n
                | envType n `elem` envLookAhead cmd     
                        || _hasNull cmd 
                    -> lift $ _runLatexParser cmd arg
            _ -> mzero
