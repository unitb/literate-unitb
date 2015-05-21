{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TemplateHaskell        #-}
module Document.Pipeline where

    -- Modules
import Latex.Parser

    -- Libraries
import Control.Arrow
import qualified Control.Category as C

import Control.Monad.RWS
import Control.Monad.Trans.Maybe
import Control.Monad.Writer

import qualified Data.Map as M

import Utilities.Syntactic

type MM = MaybeT (RWS Input [Error] ())

data DocSpec = DocSpec (M.Map String Int) (M.Map String Int)

data Input = Input 
    { getMachineInput :: M.Map MachineId DocBlocks
    , getContextInput :: M.Map ContextId DocBlocks
    }

newtype MachineId = MId { getMId :: String }
    deriving (Eq,Ord)

newtype ContextId = CId { getCId :: String }
    deriving (Eq,Ord)


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
data Cmd = BlockCmd 
    { getCmdArgs :: ([LatexDoc],LineInfo)
    , cmdLI :: LineInfo }


data DocBlocks = DocBlocks 
    { getEnv :: M.Map String [Env]
    , getCmd :: M.Map String [Cmd]
    }

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
        f (Just (Env name li ys _,xs)) = do
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
        f (Just (Text [] _,xs)) = f $ unconsTex xs
        f (Just (Text (Command name li:ys) li1,xs)) = do
                case name `M.lookup` cmds of
                    Just nargs
                        | nargs == 0 || not (all isBlank ys) -> do
                            tell (DocBlocks M.empty (M.singleton name [BlockCmd ([],li1) li]))
                            f $ Just (Text ys li1, xs)
                        | otherwise -> do
                            let (args,rest) = brackets nargs xs
                                li' = line_info rest
                            tell (DocBlocks M.empty (M.singleton name [BlockCmd (args,li') li]))
                            f $ unconsTex rest
                    Nothing    -> f $ Just (Text ys li1, xs)
        f (Just (Text (_:ys) li0,xs)) = f $ Just (Text ys li0, xs)
        f Nothing = return ()

brackets :: Int -> LatexDoc -> ([LatexDoc],LatexDoc)
brackets 0 xs = ([],xs)
brackets n (Doc (Bracket Curly _ ys _:xs) li) = (ys:args,r)
    where
        (args,r) = brackets (n-1) $ Doc xs li
brackets n (Doc zs@(Text xs _:ys) li)
    | all isBlank xs = brackets n (Doc ys li)
    | otherwise      = ([],Doc zs li)
brackets _ zs@(Doc (Bracket Square _ _ _:_) _) = ([],zs)
brackets _ zs@(Doc (Env _ _ _ _:_) _) = ([],zs)
brackets _ zs@(Doc [] _) = ([],zs)


isBlank :: LatexToken -> Bool
isBlank (Blank _ _) = True
isBlank _ = False 
