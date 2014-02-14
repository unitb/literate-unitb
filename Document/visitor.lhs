\subsection{Visitor}

\begin{code}
{-# LANGUAGE BangPatterns, RankNTypes, FlexibleContexts #-} 
{-# LANGUAGE ExistentialQuantification, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Document.Visitor 
    ( module Document.TypeList 
    , fromEither
    , find_cmd_arg 
    , visit_doc 
    , toEither 
    , Str (..)
    , EnvBlock (..) 
    , CmdBlock (..) 
    , error_list 
    , MSEitherT 
    , MSEither 
    , with_line_info
    , drop_blank_text
    , get_1_lbl
    , System(..)
    , focus_es, focusT
    , focus, def_opt, expr_opt
    , proof_opt
    , Opt ( .. )
    , Focus(..) )
where

    -- Modules
import Document.TypeList

import Latex.Parser

import Logic.ExpressionStore
import Logic.Label

import UnitB.AST

    -- Libraries
import           Control.Monad.Trans.RWS hiding ( ask, tell, asks, local, writer, reader )
import qualified Control.Monad.Trans.RWS as RWS
import           Control.Monad.Reader hiding ( reader )
import           Control.Monad.State.Class (MonadState)
import           Control.Monad.Trans.Either
import qualified Control.Monad.Trans.State as ST

import Data.Char
import Data.Monoid
import Data.Set hiding (map)
import Data.String.Utils

--import System.IO.Unsafe

import Utilities.Syntactic
import Utilities.Format 

trim xs = reverse $ f $ reverse $ f xs
    where
        f = dropWhile isSpace

comma_sep :: String -> [String]
comma_sep [] = []
comma_sep xs = trim ys : comma_sep (drop 1 zs)
    where
        (ys,zs) = break (== ',') xs

trim_blanks :: [LatexToken] -> [LatexToken]
trim_blanks xs = reverse $ skip_blanks $ reverse $ skip_blanks xs

instance Readable [LatexDoc] where
    read_args = do
        ts <- ST.get
        ([arg],ts) <- lift $ cmd_params 1 ts
        ST.put ts
        return arg

data Str = String { toString :: String }

instance Readable Str where
    read_args = do
        ts <- ST.get
        (arg,ts) <- lift $ get_1_lbl ts
        ST.put ts
        return $ String arg

instance Readable Int where
    read_args = do
        ts <- ST.get
        (arg,ts) <- lift $ get_1_lbl ts
        ST.put ts
        case reads arg of 
            [(n,"")] -> return n
            _ -> lift $ do
                li <- lift ask
                left [Error (format "invalid integer: '{0}'" arg) li]

instance Readable (Maybe Label) where
    read_args = do
        ts <- ST.get
        (arg,ts) <- lift $ cmd_params 1 ts
        ST.put ts
        let xs = (concatMap (concatMap flatten) arg)
        if strip xs == "" then 
            return Nothing
        else return $ Just $ label xs

instance Readable Label where
    read_args = do
        ts <- ST.get
        (arg,ts) <- lift $ get_1_lbl ts
        ST.put ts
        return $ label arg

instance Readable [Label] where
    read_args = do
        ts <- ST.get
        ([arg],ts) <- lift $ cmd_params 1 ts
        ST.put ts
        return $ map label $ comma_sep (concatMap flatten arg)

instance Readable (Set Label) where
    read_args = do
        ts <- ST.get
        ([arg],ts) <- lift $ cmd_params 1 ts
        ST.put ts
        return $ fromList $ map label $ comma_sep (concatMap flatten arg)

--instance Readable a => Readable (Maybe a) where
--    read_args = do
--        ts <- ST.get
--        lift $ eitherTx $ read_args
----        case x of
----            Just ([arg],ts) -> do
----                return x
----            Nothing         -> 
----        return $ fromList $ map label $ comma_sep (concatMap flatten arg)
--
--eitherTx :: Monad m
--         => EitherT a m b 
--         -> EitherT a m (Maybe b)
--eitherTx m = lift $ eitherT (const $ return Nothing) (return . Just) m

cmd_params :: (Monad m, MonadReader LineInfo m)
           => Int -> [LatexDoc] 
           -> EitherT [Error] m ([[LatexDoc]], [LatexDoc])
cmd_params 0 xs     = right ([], xs)
cmd_params n xs     = do
        li <- lift $ ask
        case drop_blank_text xs of
            Bracket _ _ xs li : ys -> do
                (ws, zs) <- local (const li) $ cmd_params (n-1) ys
                right (xs:ws, zs)
            _                 -> left [Error ("bad argument: " ++ show xs) li]

get_1_lbl :: (Monad m, MonadReader LineInfo m)
          => [LatexDoc] -> EitherT [Error] m (String, [LatexDoc])
get_1_lbl xs = do 
        ([x],z) <- cmd_params 1 xs
        case trim_blank_text x of
            ([Text [TextBlock x _]]) 
                -> right (x,z)
            ([Text [Command x _]]) 
                -> right (x,z)
            _   -> err_msg (line_info xs)
    where
        err_msg li = left [Error "expecting a label" li]
        
--get_2_lbl :: (Monad m, MonadReader (Int,Int) m)
--          => [LatexDoc] 
--          -> EitherT [Error] m (String, String, [LatexDoc])
--get_2_lbl xs = do
--        (lbl0,xs) <- get_1_lbl xs
--        (lbl1,xs) <- get_1_lbl xs
--        return (lbl0,lbl1,xs)
--
--get_3_lbl xs = do
--        (lbl0,xs) <- get_1_lbl xs
--        (lbl1,xs) <- get_1_lbl xs
--        (lbl2,xs) <- get_1_lbl xs
--        return (lbl0,lbl1,lbl2,xs)
--
--get_4_lbl xs = do
--        (lbl0,xs) <- get_1_lbl xs
--        (lbl1,xs) <- get_1_lbl xs
--        (lbl2,xs) <- get_1_lbl xs
--        (lbl3,xs) <- get_1_lbl xs
--        return (lbl0,lbl1,lbl2,lbl3,xs)

drop_blank_text :: [LatexDoc] -> [LatexDoc]
drop_blank_text ( Text [Blank _ _] : ys ) = drop_blank_text ys
drop_blank_text ( Text (Blank _ _ : xs) : ys ) = drop_blank_text ( Text xs : ys )
drop_blank_text xs = xs

trim_blank_text xs = reverse $ drop_blank_text (reverse $ drop_blank_text xs)

skip_blanks :: [LatexToken] -> [LatexToken]
skip_blanks (Blank _ _ : xs) = xs
skip_blanks xs = xs 

with_line_info :: LineInfo -> EitherT a (ReaderT LineInfo m) b -> EitherT a m b
with_line_info li cmd = 
        EitherT $ runReaderT (runEitherT cmd) li
        

    -- Given a Latex document piece, find one instance
    -- of the given command, its arguments and the
    -- the parts surrounding it to the left and right
find_cmd_arg :: Int -> [String] -> [LatexDoc] 
             -> Maybe ([LatexDoc],LatexToken,[[LatexDoc]],[LatexDoc])
find_cmd_arg n cmds (x@(Text xs) : cs) =
        case (trim_blanks $ reverse xs) of
            (t@(Command ys li):zs) -> 
                    if ys `elem` cmds
                    then eitherT
                            (\_       -> Nothing)
                            (\(xs,ws) -> Just (f zs,t,xs,ws))
                        $ with_line_info li
                        $ cmd_params n cs
                    else continue
            _    -> continue
    where
        continue = do
                (a,t,b,c) <- find_cmd_arg n cmds cs
                return (x:a,t,b,c)
        f [] = []
        f xs = [Text $ reverse xs]
find_cmd_arg _ _ []     = Nothing
find_cmd_arg n cmds (x:xs) = do
                (a,t,b,c) <- find_cmd_arg n cmds xs
                return (x:a,t,b,c)

focus :: Monad m 
      => (Opt r1 r2 w1 w2 s1 s2) 
      -> RWST r2 w2 s2 m a
      -> RWST r1 w1 s1 m a
focus opt m = RWST $ \r s1 -> do
        (x,s2,w) <- runRWST m (reader opt r) (getter opt s1)
        return (x,setter opt s2 s1, writer opt w)

focusT opt m = EitherT $ focus opt $ runEitherT m

focus_es :: Monad m
         => EitherT e (RWST a1 b ExprStore m) a
         -> EitherT e (RWST a1 b System m) a
focus_es m = focusT expr_opt m

data Opt a b c d f e = Opt 
        { reader :: (a -> b)
        , writer :: (d -> c)
        , setter :: e -> f -> f
        , getter :: f -> e }

def_opt  = Opt id id (flip $ const id) id

proof_opt = Opt id id set (expr_store . fst)
    where
        set x (a,b) = (a { expr_store = x }, b)

expr_opt = Opt id id set expr_store
    where
        set x a = a { expr_store = x }

    -- Bad, bad... unify the monad system of refinement, proof and machine already!
class ( MonadState ExprStore m0
      , MonadState System m1 ) 
   => Focus m0 m1 where
    focus' :: m0 a -> m1 a
    
instance (Monoid b, Monad m) 
        => Focus (RWST a b ExprStore m) (RWST a b System m) where
    focus' cmd = RWST $ \r s1 -> do
            (x,s2,w) <- runRWST cmd r (get s1)
            return (x,set s2 s1,w)
        where
            set x a = a { expr_store = x }
            get = expr_store

instance (Monad m) 
        => Focus (ST.StateT ExprStore m) (ST.StateT System m) where
    focus' cmd = ST.StateT $ \s1 -> do
            (x,s2) <- ST.runStateT cmd (get s1)
            return (x,set s2 s1)
        where
            set x a = a { expr_store = x }
            get = expr_store

instance (Focus m0 m1) => Focus (EitherT a m0) (EitherT a m1) where
    focus' cmd = EitherT $ focus' $ runEitherT cmd

type Node s = EitherT [Error] (RWS LineInfo [Error] s)
--type NodeT s m = EitherT [Error] (RWST (Int,Int) [Error] s m)

data EnvBlock s a = 
            forall t. TypeList t => EnvBlock (t -> [LatexDoc] -> a -> Node s a)

data CmdBlock s a =
            forall t. TypeList t => CmdBlock (t -> a -> Node s a)

--type MEither a = RWS () [a] ()

--type MEitherT a m = RWST () [a] () m

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
        f m = m >>= \(x,y,_) -> return (x,y,[])

error_list :: Monad m
           => [(Bool, String)] -> RWST LineInfo [Error] s m ()
error_list [] = return ()
error_list ( (b,msg):xs ) =
            if not b then
                error_list xs
            else do
                li <- RWS.ask 
                RWS.tell [Error msg li]
                error_list xs

visit_doc :: Monad m 
          => [(String,EnvBlock s a)] 
          -> [(String,CmdBlock s a)] 
          -> [LatexDoc] -> a 
          -> RWST b [Error] s m a
visit_doc blks cmds cs x = do
        s0 <- RWS.get
        unless (all (\(x,_) -> take 1 x == "\\") cmds) 
            $ error $ format ("Document.Visitor.visit_doc: "
                    ++ "all commands must start with '\\': {0}")
                $ map fst cmds
        let (r,s1,w) = runRWS (do
                        x <- foldM (f blks) x cs
                        g x cs)
                        (Param blks cmds) s0
        RWS.put s1
        RWS.tell w
        return r

run :: Monoid c
    => LineInfo
    -> EitherT [Error] (RWS LineInfo c d) a
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
f ((name,EnvBlock g):cs) x e@(Env s li xs _)
        | name == s = do
                pushEither x $ run li $ do
                    (args,xs) <- get_tuple xs 
                    g args xs x
        | otherwise = f cs x e
f [] x (Env _ _ xs _)  = do
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
        Command c li:_   -> do
                cmds <- asks cmds
                h cmds x c ts li
        _                   -> g x ts
g x (_ : ts) = g x ts
g x [] = return x

h :: [(String,CmdBlock s a)] -> a -> String -> [LatexDoc] 
  -> LineInfo -> RWS (Param s a) [Error] s a
h ((name,c):cs) x cmd ts li
    | name == cmd   =
            case c of 
                CmdBlock f -> do
                    x <- pushEither x $ run li $ do
                        (args,_) <- get_tuple ts
                        f args x 
                    r <- g x ts
                    return r
    | otherwise     = h cs x cmd ts li
h [] x _ ts _       = g x ts 

\end{code}
