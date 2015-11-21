{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE Arrows #-}
module Document.Pipeline where

    -- Modules
import Latex.Parser as P
import UnitB.AST

    -- Libraries
import Control.Applicative
import Control.Arrow hiding (left)
import qualified Control.Category as C

import Control.Monad.Fix
import Control.Monad.RWS
import Control.Monad.Trans.Maybe
import Control.Monad.Writer

import Data.List as L
import qualified Data.Map as M
import Data.String

import Utilities.Syntactic

newtype MM' a b = MM (MaybeT (RWS a [Error] ()) b)
    deriving ( Functor,Applicative,Monad,MonadPlus
             , MonadWriter [Error],MonadReader a
             , Alternative, MonadFix )

type MM = MM' Input

data DocSpec = DocSpec (M.Map String Int) (M.Map String Int)

data Input = Input 
    { getMachineInput :: M.Map MachineId DocBlocks
    , getContextInput :: M.Map ContextId DocBlocks
    } deriving Show

newtype ContextId = CId { getCId :: String }
    deriving (Eq,Ord)

instance Show ContextId where
    show = getCId

instance IsString ContextId where
    fromString = CId

runMM :: MM' a b -> a -> Either [Error] b
runMM (MM cmd) input = case r of
                            Nothing -> Left es
                            Just x
                                | L.null es -> Right x
                                | otherwise -> Left es
    where
        (r,(),es) = runRWS (runMaybeT cmd) input ()

empty_spec :: DocSpec
empty_spec = DocSpec M.empty M.empty

instance Monoid DocSpec where
    mappend (DocSpec xs0 ys0) (DocSpec xs1 ys1) = DocSpec (xs0 `unionM` xs1) (ys0 `unionM` ys1) 
        where
            unionM = M.unionWithKey (\k _ -> error $ "command name clash: " ++ k)
    mempty = empty_spec

data Pipeline m a b = Pipeline DocSpec DocSpec (a -> m b)

instance Monad m => C.Category (Pipeline m) where
    id = Pipeline empty_spec empty_spec return
    Pipeline xs0 xs1 f . Pipeline ys0 ys1 g = Pipeline (xs0 `mappend` ys0) (xs1 `mappend` ys1) $ (>>= f) . g

instance Monad m => Arrow (Pipeline m) where
    arr f = Pipeline empty_spec empty_spec $ return . f
    first (Pipeline xs ys f) = Pipeline xs ys $ \(x,y) -> f x >>= \z -> return (z,y)

instance Monad m => ArrowApply (Pipeline m) where
    app = Pipeline empty_spec empty_spec $ \(Pipeline _ _ f, x) -> f x

data Env = BlockEnv 
    { getEnvArgs :: ([LatexDoc],LineInfo)
    , getEnvContent :: LatexDoc
    , envLI :: LineInfo }
    deriving (Show)
data Cmd = BlockCmd 
    { getCmdArgs :: ([LatexDoc],LineInfo)
    , cmdLI :: LineInfo }
    deriving (Show)

data DocBlocks = DocBlocks 
    { getEnv :: M.Map String [Env]
    , getCmd :: M.Map String [Cmd]
    } deriving (Show)

instance Monoid DocBlocks where
    mempty = DocBlocks M.empty M.empty
    mappend (DocBlocks xs0 xs1) (DocBlocks ys0 ys1) = 
            DocBlocks 
                (M.unionWith (++) xs0 ys0)
                (M.unionWith (++) xs1 ys1)

machine_spec :: Pipeline m a b -> DocSpec
machine_spec (Pipeline m _ _) = m

context_spec :: Pipeline m a b -> DocSpec
context_spec (Pipeline _ c _) = c

getLatexBlocks :: DocSpec
               -> LatexDoc
               -> DocBlocks
getLatexBlocks (DocSpec envs cmds) xs = execWriter (f $ unconsTex xs)
    where
        f :: Maybe (LatexNode,LatexDoc) -> Writer DocBlocks ()
        f (Just (Env _ name li ys _,xs)) = do
                case name `M.lookup` envs of
                    Just nargs -> do
                        let (args,rest) = brackets nargs ys
                            li' = line_info rest 
                        tell (DocBlocks (M.singleton name 
                            [BlockEnv (args,li') rest li]) M.empty) 
                    Nothing -> f $ unconsTex ys
                f $ unconsTex xs
        f (Just (Bracket _ _ ys _,xs)) = do
                f $ unconsTex ys
                f $ unconsTex xs
        f (Just (Text (Command name li),xs)) = do
                case name `M.lookup` cmds of
                    Just nargs
                        | nargs == 0 -> do
                            tell (DocBlocks M.empty (M.singleton name [BlockCmd ([],li) li]))
                            f $ unconsTex xs
                        | otherwise -> do
                            let (args,rest) = brackets nargs xs
                                li' = line_info rest
                            tell (DocBlocks M.empty (M.singleton name [BlockCmd (args,li') li]))
                            f $ unconsTex rest
                    Nothing    -> f $ unconsTex xs
        f (Just (Text _,xs)) = f $ unconsTex xs
        f Nothing = return ()

brackets :: Int -> LatexDoc -> ([LatexDoc],LatexDoc)
brackets 0 xs = ([],xs)
brackets n doc = case unconsTex doc of
        Just (Bracket Curly _ ys _,xs) -> (ys:args,r)
            where
                (args,r) = brackets (n-1) xs
        Just (Text (Blank _ _),ys) -> brackets n ys
            -- | otherwise      -> ([],doc)
        _ -> ([],doc)

withInput :: Pipeline MM Input b -> Pipeline MM a b
withInput (Pipeline s0 s1 f) = Pipeline s0 s1 $ \_ -> ask >>= f

isBlank :: LatexToken -> Bool
isBlank (Blank _ _) = True
isBlank _ = False 

runPipeline' :: M.Map String [LatexDoc]
             -> M.Map String [LatexDoc]
             -> a
             -> Pipeline MM a b 
             -> Either [Error] b
runPipeline' ms cs arg p = runMM (f arg) input
    where
        input = Input mch ctx
        mch   = M.mapKeys MId $ M.map (mconcat . map (getLatexBlocks m_spec)) ms
        ctx   = M.mapKeys CId $ M.map (mconcat . map (getLatexBlocks c_spec)) cs
        Pipeline m_spec c_spec f = p
