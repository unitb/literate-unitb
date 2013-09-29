{-# LANGUAGE BangPatterns, RankNTypes, FlexibleContexts #-} 
{-# LANGUAGE ExistentialQuantification #-}
module Document.Visitor 
    ( module Document.TypeList 
    , fromEither
    , find_cmd_arg 
    , visit_doc 
    , toEither 
    , EnvBlock (..) 
    , CmdBlock (..) 
    , error_list 
    , MSEitherT 
    , MSEither 
    , with_line_info )
where

    -- Modules
import Latex.Parser

import Document.Expression
import Document.TypeList

    -- Libraries
import 
    Control.Monad.Trans.RWS hiding ( ask, tell, asks, local )
import qualified
    Control.Monad.Trans.RWS as RWS
import Control.Monad.Reader
import Control.Monad.Trans.Either

import Data.Monoid

import System.IO
import System.IO.Unsafe

import Utilities.Syntactic

trim_blanks :: [LatexToken] -> [LatexToken]
trim_blanks xs = reverse $ skip_blanks $ reverse $ skip_blanks xs

with_line_info :: (Int, Int) -> EitherT a (ReaderT (Int,Int) m) b -> EitherT a m b
with_line_info li cmd = 
        EitherT $ runReaderT (runEitherT cmd) li
        

    -- Given a Latex document piece, find one instance
    -- of the given command, its arguments and the
    -- the parts surrounding it to the left and right
find_cmd_arg :: Int -> [String] -> [LatexDoc] 
             -> Maybe ([LatexDoc],LatexToken,[[LatexDoc]],[LatexDoc])
find_cmd_arg n cmds (x@(Text xs) : cs) =
        case (trim_blanks $ reverse xs) of
            (t@(Command ys (i,j)):zs) -> 
                    if ys `elem` cmds
                    then eitherT
                            (\_       -> Nothing)
                            (\(xs,ws) -> Just (f zs,t,xs,ws))
                        $ with_line_info (i,j)
                        $ cmd_params n cs
                    else continue
            _    -> continue
    where
        continue = do
                (a,t,b,c) <- find_cmd_arg n cmds cs
                return (x:a,t,b,c)
        f [] = []
        f xs = [Text $ reverse xs]
find_cmd_arg _ cmds []     = Nothing
find_cmd_arg n cmds (x:xs) = do
                (a,t,b,c) <- find_cmd_arg n cmds xs
                return (x:a,t,b,c)

type Node s = EitherT [Error] (RWS (Int,Int) [Error] s)
type NodeT s m = EitherT [Error] (RWST (Int,Int) [Error] s m)

data EnvBlock s a = 
            forall t. TypeList t => EnvBlock (t -> [LatexDoc] -> a -> Node s a)

data CmdBlock s a =
            forall t. TypeList t => CmdBlock (t -> a -> Node s a)

type MEither a = RWS () [a] ()

type MEitherT a m = RWST () [a] () m

type MSEither a s = RWS () [a] s

type MSEitherT a s m = RWST () [a] s m

data Param s a = Param 
    { blocks :: [(String, EnvBlock s a)]
    , cmds   :: [(String, CmdBlock s a)] }

fromEither :: Monad m => a -> EitherT [b] (RWST c [b] d m) a -> RWST c [b] d m a
fromEither y m = do
        x <- runEitherT m
        case x of
            Right x -> do
                RWS.tell []
                return x
            Left xs -> do
                RWS.tell xs
                return y

toEither :: Monad m => RWST a [c] d m b -> EitherT [c] (RWST a [c] d m) b
toEither m = EitherT $ mapRWST f $ do
        (x,xs) <- RWS.listen m
        case xs of
            [] -> return $ Right x
            xs -> return $ Left xs
    where
        f m = m >>= \(x,y,z) -> return (x,y,[])

error_list :: Monad m
           => [(Bool, String)] -> RWST (Int,Int) [Error] s m ()
error_list [] = return ()
error_list ( (b,msg):xs )
        | not b = error_list xs
        | b     = do
            (i,j) <- RWS.ask 
            RWS.tell [(msg,i,j)]
            error_list xs

visit_doc :: Monad m 
          => [(String,EnvBlock s a)] 
          -> [(String,CmdBlock s a)] 
          -> [LatexDoc] -> a 
          -> RWST b [Error] s m a
visit_doc blks cmds cs x = do
        s0 <- RWS.get
        let (r,s1,w) = runRWS (do
                        x <- foldM (f blks) x cs
                        g x cs)
                        (Param blks cmds) s0
        RWS.put s1
        RWS.tell w
        return r

run :: Monoid c
    => (Int,Int) 
    -> EitherT [Error] (RWS (Int,Int) c d) a
    -> EitherT [Error] (RWS b c d) a
run li m = EitherT $ do 
        s <- get
        x <- withRWS (const (const (li,s))) $ runEitherT m
        return x

pushEither :: Monoid c => e -> EitherT c (RWS a c d) e -> RWS a c d e
pushEither y m = do
        x <- runEitherT m
        case x of
            Right x -> return x
            Left xs -> do
                RWS.tell xs
                return y

f :: [(String, EnvBlock s a)] -> a -> LatexDoc 
  -> RWS (Param s a) [Error] s a
f ((name,EnvBlock g):cs) x e@(Env s (i,j) xs _)
        | name == s = do
                pushEither x $ run (i,j) $ do
                    (args,xs) <- get_tuple xs 
                    g args xs x
        | otherwise = f cs x e
f [] x e@(Env s (i,j) xs _)  = do
        blks <- asks blocks
        x    <- foldM (f blks) x xs
        g x xs
f _ x (Bracket _ _ cs _)     = do
        blks <- asks blocks
        x    <- foldM (f blks) x cs
        g x cs
f _ x (Text _)               = return x

g :: a -> [LatexDoc] 
  -> RWS (Param s a) [Error] s a
g x (Text xs : ts) = do
    case trim_blanks $ reverse xs of
        Command c (i,j):_   -> do
                cmds <- asks cmds
                h cmds x c ts (i,j)
        _                   -> g x ts
g x (t : ts) = g x ts
g x [] = return x

h :: [(String,CmdBlock s a)] -> a -> String -> [LatexDoc] 
  -> (Int,Int) -> RWS (Param s a) [Error] s a
h ((name,c):cs) x cmd ts (i,j)
    | name == cmd   =
            case c of 
                CmdBlock f -> do
                    x <- pushEither x $ run (i,j) $ do
                        (args,_) <- get_tuple ts
                        f args x 
                    r <- g x ts
                    return r
    | otherwise     = h cs x cmd ts (i,j)
h [] x cmd ts (i,j) = g x ts 
