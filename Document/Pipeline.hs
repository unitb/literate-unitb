{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
module Document.Pipeline where

    -- Modules
import Document.Proof

import Latex.Parser

import Logic.Expr

    -- Libraries
import Control.Arrow
import qualified Control.Category as C

import Control.Monad.Writer

import           Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Set as S

import Utilities.Tuple

data DocSpec = DocSpec (S.Set String) (M.Map String Int)

infixr <*

empty_spec :: DocSpec
empty_spec = DocSpec S.empty M.empty

instance Monoid DocSpec where
    mappend (DocSpec xs0 ys0) (DocSpec xs1 ys1) = DocSpec (xs0 `unionS` xs1) (ys0 `unionM` ys1) 
        where
            unionS xs ys
                    | S.null zs = S.union xs ys
                    | otherwise = error $ "environment name clash: " ++ show (S.toList zs)
                where
                    zs = S.intersection xs ys
            unionM = M.unionWithKey (\k _ -> error $ "command name clash: " ++ k)
    mempty = empty_spec

data Pipeline m a b = Pipeline DocSpec DocSpec (a -> m b)

instance Monad m => C.Category (Pipeline m) where
    id = Pipeline empty_spec empty_spec return
    Pipeline xs0 xs1 f . Pipeline ys0 ys1 g = Pipeline (xs0 `mappend` ys0) (xs1 `mappend` ys1) $ (>>= f) . g

instance Monad m => Arrow (Pipeline m) where
    arr f = Pipeline empty_spec empty_spec $ return . f
    first (Pipeline xs ys f) = Pipeline xs ys $ \(x,y) -> f x >>= \z -> return (z,y)

newtype Env = BlockEnv { getEnvContent :: [LatexDoc] }
newtype Cmd = BlockCmd { getCmdArgs :: [[LatexDoc]] }

runPipeline :: [LatexDoc] 
            -> Pipeline m DocBlocks b 
            -> m b
runPipeline xs (Pipeline mch _ f) = f (getLatexBlocks mch xs)

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
        f (Env name _ ys _:xs) = do
                if name `S.member` envs 
                    then tell (DocBlocks (M.singleton name [BlockEnv ys]) M.empty) 
                    else f ys
                f xs
        f (Bracket _ _ ys _:xs) = do
                f ys
                f xs
        f (Text []:xs) = f xs
        f (Text (Command name _:ys):xs) = do
                case name `M.lookup` cmds of
                    Just nargs
                        | nargs == 0 || not (all isBlank ys) -> do
                            tell (DocBlocks M.empty (M.singleton name [BlockCmd []]))
                            f (Text ys : xs)
                        | otherwise -> do
                            let (args,rest) = brackets nargs xs
                            tell (DocBlocks M.empty (M.singleton name [BlockCmd args]))
                            f rest
                    Nothing    -> f $ Text ys : xs
        f (Text (_:ys):xs) = f $ Text ys : xs
        f [] = return ()

brackets :: Int -> [LatexDoc] -> ([[LatexDoc]],[LatexDoc])
brackets 0 xs = ([],xs)
brackets n (Bracket True _ ys _:xs) = (ys:args,r)
    where
        (args,r) = brackets (n-1) xs
brackets n zs@(Text xs:ys)
    | all isBlank xs = brackets n ys
    | otherwise      = ([],zs)
brackets _ zs@(Bracket False _ _ _:_) = ([],zs)
brackets _ zs@(Env _ _ _ _:_) = ([],zs)
brackets _ [] = ([],[])


isBlank :: LatexToken -> Bool
isBlank (Blank _ _) = True
isBlank _ = False

data Phase2 = Phase2
        (MTable (Map Label EventId))               -- 
        (MTable (Map String Var))               -- machine variables
        (MTable (Map String Var))               -- abstract machine variables
        (MTable (Map String Var))               -- dummy variables
        (MTable (Map EventId (Map String Var))) -- event indices
        (MTable ParserSetting)                  -- parsing assumptions
        (MTable ParserSetting)                  -- parsing invariants and properties
        (MTable (Map EventId ParserSetting))    -- parsing schedule
        (MTable (Map EventId ParserSetting))    -- parsing guards and actions

newtype MachineId = MId { getMId :: String }
    deriving (Eq,Ord)

newtype ContextId = CId { getCId :: String }
    deriving (Eq,Ord)

newtype EventId = EventId Label
    deriving (Eq,Ord,Show)

type MTable = Map MachineId
type CTable = Map ContextId
