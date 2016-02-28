{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE Arrows #-}
module Document.Pipeline where

    -- Modules
import Document.Phase.Parameters
import Latex.Parser as P 
import Logic.Names
import UnitB.Syntax

    -- Libraries
import Control.Applicative
import Control.Arrow hiding (left)
import qualified Control.Category as C
import Control.Lens

import Control.Monad.Fix
import Control.Monad.RWS
import Control.Monad.Trans.Maybe
import Control.Monad.Writer

import Data.DList (DList)
import qualified Data.DList as D
import Data.Hashable
import Data.List as L
import Data.String

import Utilities.Instances
import qualified Utilities.Map as M
import Utilities.PrintfTH
import Utilities.Syntactic
import Utilities.Table
import Utilities.Tuple.Generics

newtype MM' a b = MM (MaybeT (RWS a [Error] ()) b)
    deriving ( Functor,Applicative,MonadPlus
             , MonadWriter [Error],MonadReader a
             , Alternative, MonadFix )

type MM = MM' Input

instance Monad (MM' a) where
    {-# INLINE (>>=) #-}
    MM x >>= f = MM $ x >>= run . f
        where
            run (MM x) = x

data DocSpec = DocSpec 
            { getEnvSpec :: M.Map String ArgumentSpec 
            , getCommandSpec :: M.Map String ArgumentSpec
            }

data ArgumentSpec = forall a. IsTuple LatexArg a => ArgumentSpec Int (Proxy a)

type Input = InputRaw []
type InputBuilder = InputRaw DList

data InputRaw f = Input 
    { getMachineInput :: Table MachineId (DocBlocksRaw f)
    , getContextInput :: Table ContextId (DocBlocksRaw f)
    } deriving Show

convertInput :: (forall a. f a -> g a)
             -> InputRaw f
             -> InputRaw g
convertInput f (Input mch ctx) = Input 
        (M.map (convertBlocks f) mch) 
        (M.map (convertBlocks f) ctx)

newtype ContextId = CId { getCId :: String }
    deriving (Eq,Ord,Hashable)

instance Show ContextId where
    show = getCId

instance IsString ContextId where
    fromString = CId

liftEither :: Either [Error] a -> MM' c a
liftEither (Left xs) = MM $ tell xs >> mzero
liftEither (Right r) = return r

argCount :: ArgumentSpec -> Int
argCount (ArgumentSpec n _) = n

{-# INLINE runMM #-}
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
    {-# INLINE (.) #-}
    Pipeline xs0 xs1 f . Pipeline ys0 ys1 g = Pipeline (xs0 `mappend` ys0) (xs1 `mappend` ys1) $ (>>= f) . g

instance Monad m => Arrow (Pipeline m) where
    {-# INLINE arr #-}
    arr f = Pipeline empty_spec empty_spec $ return . f
    {-# INLINE first #-}
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

type DocBlocks = DocBlocksRaw []
type DocBlocksBuilder = DocBlocksRaw DList

data DocBlocksRaw f = DocBlocks 
    { getEnv :: Table String (OnFunctor f Env)
    , getCmd :: Table String (OnFunctor f Cmd)
    } deriving (Show)

convertBlocks :: (forall a. f a -> g a)
              -> DocBlocksRaw f -> DocBlocksRaw g
convertBlocks f (DocBlocks env cmd) = DocBlocks
    (env & traverse._Wrapped %~ f)
    (cmd & traverse._Wrapped %~ f)

instance Monoid1 f => Monoid (DocBlocksRaw f) where
    mempty = DocBlocks M.empty M.empty
    mappend (DocBlocks xs0 xs1) (DocBlocks ys0 ys1) = 
            DocBlocks 
                (M.unionWith (<>) xs0 ys0)
                (M.unionWith (<>) xs1 ys1)

machine_spec :: Pipeline m a b -> DocSpec
machine_spec (Pipeline m _ _) = m

context_spec :: Pipeline m a b -> DocSpec
context_spec (Pipeline _ c _) = c

getLatexBlocks :: DocSpec
               -> LatexDoc
               -> DocBlocksBuilder
getLatexBlocks (DocSpec envs cmds) xs = execWriter (f $ unconsTex xs)
    where
        f :: Maybe (LatexNode,LatexDoc) -> Writer DocBlocksBuilder ()
        f (Just ((EnvNode (Env _ name li ys _),xs))) = do
                case name `M.lookup` envs of
                    Just nargs -> do
                        let (args,rest) = brackets (argCount nargs) ys
                            li' = line_info rest 
                        tell (DocBlocks (M.singleton name 
                            $ pure $ BlockEnv (args,li') rest li) M.empty) 
                    Nothing -> f $ unconsTex ys
                f $ unconsTex xs
        f (Just ((BracketNode (Bracket _ _ ys _),xs))) = do
                f $ unconsTex ys
                f $ unconsTex xs
        f (Just (Text (Command name li),xs)) = do
                case argCount <$> name `M.lookup` cmds of
                    Just nargs
                        | nargs == 0 -> do
                            tell (DocBlocks M.empty (M.singleton name
                                $ pure $ BlockCmd ([],li) li))
                            f $ unconsTex xs
                        | otherwise -> do
                            let (args,rest) = brackets nargs xs
                                li' = line_info rest
                            tell (DocBlocks M.empty
                                (M.singleton name
                                    $ pure $ BlockCmd (args,li') li))
                            f $ unconsTex rest
                    Nothing    -> f $ unconsTex xs
        f (Just (Text _,xs)) = f $ unconsTex xs
        f Nothing = return ()

brackets :: Int -> LatexDoc -> ([LatexDoc],LatexDoc)
brackets 0 xs = ([],xs)
brackets n doc = case unconsTex doc of
        Just ((BracketNode (Bracket Curly _ ys _),xs)) -> (ys:args,r)
            where
                (args,r) = brackets (n-1) xs
        Just (Text (Blank _ _),ys) -> brackets n ys
            -- | otherwise      -> ([],doc)
        _ -> ([],doc)

{-# INLINE withInput #-}
withInput :: Pipeline MM Input b -> Pipeline MM a b
withInput (Pipeline s0 s1 f) = Pipeline s0 s1 $ \_ -> ask >>= f

isBlank :: LatexToken -> Bool
isBlank (Blank _ _) = True
isBlank _ = False 

{-# INLINE runPipeline' #-}
runPipeline' :: Table Name [LatexDoc]
             -> Table String [LatexDoc]
             -> a
             -> Pipeline MM a b 
             -> Either [Error] b
runPipeline' ms cs arg p = runMM (f arg) input
    where
        input = Input 
                (M.map (convertBlocks D.toList) mch) 
                (M.map (convertBlocks D.toList) ctx)
        mch   = M.mapKeys MId $ M.map (mconcat . map (getLatexBlocks m_spec)) ms
        ctx   = M.mapKeys CId $ M.map (mconcat . map (getLatexBlocks c_spec)) cs
        Pipeline m_spec c_spec f = p

latexArgProxy :: Proxy LatexArg
latexArgProxy = Proxy

machineSyntax :: Pipeline m a b -> [String]
machineSyntax (Pipeline mch _ _) = 
           M.foldMapWithKey cmd (getCommandSpec mch)
        ++ M.foldMapWithKey env (getEnvSpec mch)
    where
        argument p = [printf|{%s}|] (argKind p)
        cmd x (ArgumentSpec _ xs) = [x ++ foldMapTupleType latexArgProxy argument xs]
        env x (ArgumentSpec _ xs) = [[printf|\\begin{%s}%s .. \\end{%s}|] x
                    (foldMapTupleType latexArgProxy argument xs :: String) x]

