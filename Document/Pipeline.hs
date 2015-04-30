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
import Utilities.Tuple

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

infixr <*

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

data Env = BlockEnv { getEnvArgs :: [[LatexDoc]], getEnvContent :: [LatexDoc], envLI :: LineInfo }
data Cmd = BlockCmd { getCmdArgs :: [[LatexDoc]], cmdLI :: LineInfo }


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

ident :: Arrow arr => arr b ()
ident = arr $ \_ -> ()

(<*) :: Arrow arr => arr a b -> arr a bs -> arr a (b :+: bs)
(<*) x y = combine x y

combine :: Arrow arr => arr a b -> arr a bs -> arr a (b :+: bs)
combine a0 a1 = (a0 &&& a1) >>> arr (uncurry (:+:))

toTupleA :: (Arrow arr, IsTuple b) => arr (TypeList b) b
toTupleA = arr fromTuple

foo :: forall arr a b c d. Arrow arr => arr a b -> arr a c -> arr a d -> arr a (b,c,d)
foo x y z = (x <* y <* z <* ident) >>> toTupleA

machine_spec :: Pipeline m a b -> DocSpec
machine_spec (Pipeline m _ _) = m

context_spec :: Pipeline m a b -> DocSpec
context_spec (Pipeline _ c _) = c

getLatexBlocks :: DocSpec
               -> [LatexDoc] 
               -> DocBlocks
getLatexBlocks (DocSpec envs cmds) xs = execWriter (f xs)
    where
        f (Env name li ys _:xs) = do
                case name `M.lookup` envs of
                    Just nargs -> do
                        let (args,rest) = brackets nargs ys
                        tell (DocBlocks (M.singleton name [BlockEnv args rest li]) M.empty) 
                    Nothing -> f ys
                f xs
        f (Bracket _ _ ys _:xs) = do
                f ys
                f xs
        f (Text []:xs) = f xs
        f (Text (Command name li:ys):xs) = do
                case name `M.lookup` cmds of
                    Just nargs
                        | nargs == 0 || not (all isBlank ys) -> do
                            tell (DocBlocks M.empty (M.singleton name [BlockCmd [] li]))
                            f (Text ys : xs)
                        | otherwise -> do
                            let (args,rest) = brackets nargs xs
                            tell (DocBlocks M.empty (M.singleton name [BlockCmd args li]))
                            f rest
                    Nothing    -> f $ Text ys : xs
        f (Text (_:ys):xs) = f $ Text ys : xs
        f [] = return ()

brackets :: Int -> [LatexDoc] -> ([[LatexDoc]],[LatexDoc])
brackets 0 xs = ([],xs)
brackets n (Bracket Curly _ ys _:xs) = (ys:args,r)
    where
        (args,r) = brackets (n-1) xs
brackets n zs@(Text xs:ys)
    | all isBlank xs = brackets n ys
    | otherwise      = ([],zs)
brackets _ zs@(Bracket Square _ _ _:_) = ([],zs)
brackets _ zs@(Env _ _ _ _:_) = ([],zs)
brackets _ [] = ([],[])


isBlank :: LatexToken -> Bool
isBlank (Blank _ _) = True
isBlank _ = False 
