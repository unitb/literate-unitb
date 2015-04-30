\subsection{Visitor}

\begin{code}
{-# LANGUAGE BangPatterns, RankNTypes   #-}
{-# LANGUAGE FlexibleContexts           #-} 
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE TypeOperators              #-}
module Document.Visitor 
    ( module Utilities.Tuple
    , fromEither
    , find_cmd_arg 
    , visit_doc 
    , toEither 
    , Str (..)
    , EnvBlock (..) 
    , CmdBlock (..) 
    , VEnvBlock (..) 
    , VCmdBlock (..) 
    , error_list 
    , MSEither 
    , with_line_info
    , drop_blank_text
    , drop_blank_text'
    , get_1_lbl
    , System(..)
    , focus_es, focusT
    , focus, def_opt, expr_opt
    , proof_opt
    , Opt ( .. )
    , Focus(..)
    , visitor, raise
    , VisitorT ( .. )
    , run_visitor
    , add_state
    , add_writer
    , lift_i
    , bind, bind_all
    , insert_new
    , get_content
    , with_content
    , Readable (..)
    , AllReadable (..) )
where

    -- Modules

import Latex.Parser

import Logic.Expr
import Logic.ExpressionStore

import UnitB.AST

    -- Libraries
import           Control.Applicative
import           Control.Monad.Reader.Class hiding (reader)
import           Control.Monad.Trans.RWS 
        hiding ( ask, tell, asks, local, writer, reader )
import qualified Control.Monad.Trans.RWS as RWS
import           Control.Monad.Reader       hiding ( reader )
--import           Control.Monad.Reader.Class hiding ( reader )
import qualified Control.Monad.State.Class as S
import           Control.Monad.Trans.Either
import qualified Control.Monad.Trans.State as ST
import           Control.Monad.Trans.Writer ( WriterT ( .. ), runWriterT )

import           Data.Char
import           Data.List as L
import qualified Data.Map as M
import           Data.Maybe
import           Data.Monoid
import           Data.Set hiding (map)
import           Data.String.Utils

import qualified Text.ParserCombinators.ReadPrec as RP ( get, pfail, (<++) )

import GHC.Read

import Utilities.Error
import Utilities.Format 
import Utilities.Syntactic
import Utilities.Tuple

class Readable a where
    read_args :: (Monad m, MonadReader LineInfo m)
              => ST.StateT [LatexDoc] (EitherT [Error] m) a
    read_one :: (Monad m, MonadReader LineInfo m)
             => ST.StateT [[LatexDoc]] (EitherT [Error] m) a

get_tuple' :: (Monad m, IsTuple a, AllReadable (TypeList a))
           => [LatexDoc] -> LineInfo 
           -> EitherT [Error] m (a, [LatexDoc])
get_tuple' xs li = EitherT $ do
        x <- runReaderT (runEitherT $ ST.runStateT get_tuple xs) li
        return $ liftM (\(x,y) -> (fromTuple x,y)) x

class AllReadable a where
    get_tuple :: (Monad m, MonadReader LineInfo m) 
              => ST.StateT [LatexDoc] (EitherT [Error] m) a
    read_all :: (Monad m, MonadReader LineInfo m) 
             => ST.StateT [[LatexDoc]] (EitherT [Error] m) a

instance AllReadable () where
    get_tuple = return () 
    read_all = do
        xs <- ST.get
        li <- lift $ lift $ ask
        unless (L.null xs) 
            $ lift $ left [Error "too many arguments" li]
        return ()

instance (AllReadable as, Readable a) => AllReadable (a :+: as) where
    get_tuple = do
        x  <- read_args 
        xs <- get_tuple
        return (x :+: xs)
    read_all = do
        x  <- read_one
        xs <- read_all
        return (x :+: xs)

trim :: [Char] -> [Char]
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

get_next :: (Monad m, MonadReader LineInfo m)
         => ST.StateT [[LatexDoc]] (EitherT [Error] m) [LatexDoc]
get_next = do
    li <- lift $ lift $ ask
    s  <- ST.get
    case s of
        x:xs -> ST.put xs >> return x
        [] -> lift $ left [Error "expecting more arguments" li]

instance Readable [LatexDoc] where
    read_args = do
        ts <- ST.get
        ([arg],ts) <- lift $ cmd_params 1 ts
        ST.put ts
        return arg
    read_one = get_next

instance Readable LatexDoc' where
    read_args = do
        ts <- read_args
        li <- ask
        return $ LatexDoc' li ts
    read_one = do
        li <- ask
        LatexDoc' li <$> get_next

data Str = String { toString :: String }

read_label :: (Monad m, MonadReader LineInfo m)
           => ST.StateT [[LatexDoc]] (EitherT [Error] m) String
read_label = do
    li <- lift $ lift $ ask
    x  <- get_next    
    lift $ case trim_blank_text x of
        ([Text [TextBlock x _]]) 
            -> right x
        ([Text [Command x _]]) 
            -> right x
        _   -> left [Error "expecting a label" li]

instance Readable Str where
    read_args = do
        ts <- ST.get
        (arg,ts) <- lift $ get_1_lbl ts
        ST.put ts
        return $ String arg
    read_one = do
        x <- read_label
        return $ String x

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
    read_one = do
        arg <- read_label
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
    read_one = do
        arg <- get_next
        let xs = concatMap flatten arg
        if strip xs == "" then
            return Nothing
        else return $ Just $ label xs

instance Readable Label where
    read_args = do
        ts <- ST.get
        (arg,ts) <- lift $ get_1_lbl ts
        ST.put ts
        return $ label arg
    read_one = do
        label `liftM` read_label

instance Readable [Label] where
    read_args = do
        ts <- ST.get
        ([arg],ts) <- lift $ cmd_params 1 ts
        ST.put ts
        return $ map label $ comma_sep (concatMap flatten arg)
    read_one = do
        arg <- get_next
        return $ map label $ comma_sep (concatMap flatten arg)

instance Readable [Str] where
    read_args = do
        ts <- ST.get
        ([arg],ts) <- lift $ cmd_params 1 ts
        ST.put ts
        return $ map String $ comma_sep (concatMap flatten arg)
    read_one = do
        arg <- get_next
        return $ map String $ comma_sep (concatMap flatten arg)

instance Readable [[Str]] where
    read_args = do
        ts <- ST.get
        ([arg],ts) <- lift $ cmd_params 1 ts
        ST.put ts
        case reads $ concatMap flatten arg of 
            [(n,"")] -> return n
            _ -> lift $ do
                li <- lift ask
                left [Error (format "invalid list of strings: '{0}'" arg) li]
    read_one = do
        arg <- get_next
        case reads $ concatMap flatten arg of 
            [(n,"")] -> return n
            _ -> lift $ do
                li <- lift ask
                left [Error (format "invalid list of strings: '{0}'" arg) li]

instance Read Str where
    readPrec = do
        c <- RP.get
        when (c == ',' || c == ']') $ RP.pfail
        fix (\rec xs -> do
            (do c <- RP.get
                when (c == ',' || c == ']') $ RP.pfail
                rec (c:xs)) RP.<++
                return (String $ reverse xs)) [c]
    
instance Readable (Set Label) where
    read_args = do
        ts <- ST.get
        ([arg],ts) <- lift $ cmd_params 1 ts
        ST.put ts
        return $ fromList $ map label $ comma_sep (concatMap flatten arg)
    read_one = do
        arg <- get_next
        return $ fromList $ map label $ comma_sep (concatMap flatten arg)

instance Readable (M.Map Label ()) where
    read_args = do
        M.fromSet (const ()) <$> read_args
    read_one = do
        M.fromSet (const ()) <$> read_one

raise :: Monad m => Error -> EitherT [Error] m a
raise e = left [e]

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
            _                 -> left [Error ("Expecting one more argument") li]

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

drop_blank_text' :: LatexDoc' -> LatexDoc'
drop_blank_text' (LatexDoc' li xs) = drop_blank_text_aux li xs
    where
        drop_blank_text_aux li ( Text [] : ys ) = drop_blank_text_aux li ys
        drop_blank_text_aux _ ( Text [Blank _ li] : ys ) = drop_blank_text_aux li ys
        drop_blank_text_aux _ ( Text (Blank _ li : xs) : ys ) = drop_blank_text_aux li ( Text xs : ys )
        drop_blank_text_aux li xs = LatexDoc' li xs

trim_blank_text :: [LatexDoc] -> [LatexDoc]
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

focusT :: Monad m
       => Opt r1 r2 w1 w2 s1 s2
       -> EitherT e (RWST r2 w2 s2 m) a -> EitherT e (RWST r1 w1 s1 m) a
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

def_opt :: Opt b b c c f f
def_opt = Opt id id (flip $ const id) id

proof_opt :: Opt b b c c (System, t) ExprStore
proof_opt = Opt id id set (expr_store . fst)
    where
        set x (a,b) = (a { expr_store = x }, b)

expr_opt :: Opt b b c c System ExprStore
expr_opt = Opt id id set expr_store
    where
        set x a = a { expr_store = x }

    -- Bad, bad... unify the monad system of refinement, proof and machine already!
class ( S.MonadState ExprStore m0
      , S.MonadState System m1 ) 
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

data EnvBlock s a = 
            forall t. (IsTuple t, AllReadable (TypeList t))
         => EnvBlock (t -> [LatexDoc] -> a -> Node s a)

data CmdBlock s a =
            forall t. (IsTuple t, AllReadable (TypeList t))
         => CmdBlock (t -> a -> Node s a)

data VEnvBlock m = forall t. (IsTuple t, AllReadable (TypeList t))
                => VEnvBlock (t -> [LatexDoc] -> VisitorT m ())

data VCmdBlock m =
               forall t. (IsTuple t, AllReadable (TypeList t))
            => VCmdBlock (t -> VisitorT m ())

type MSEither = RWS LineInfo [Error] System

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

bind :: MonadReader LineInfo m
     => String -> Maybe a -> EitherT [Error] m a
bind msg Nothing = do
        li <- ask
        left [Error msg li]
bind _ (Just x) = return x

bind_all :: Monad m
         => [a]
         -> (a -> String) 
         -> (a -> Maybe b)
         -> EitherT [Error] (RWST LineInfo [Error] s m) [b]
bind_all xs msgs lu = do
            let ys = map lu xs
                zs = map (msgs . fst) 
                    $ L.filter (isNothing . snd) 
                    $ zip xs ys
            li <- lift $ ask
            toEither $ forM_ zs $ \msg ->  
                RWS.tell [Error msg li]
            return $ catMaybes ys


insert_new :: Ord a 
           => a -> b -> M.Map a b 
           -> Maybe (M.Map a b)
insert_new x y m
    | x `M.member` m    = Nothing
    | otherwise         = Just $ M.insert x y m

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

data ParamT m = ParamT
    { blocksT :: [(String, VEnvBlock m)]
    , cmdsT   :: [(String, VCmdBlock m)] 
    }

data VisitorT m a = VisitorT { unVisitor :: ErrorT (ReaderT (LineInfo, [LatexDoc]) m) a }

instance Monad m => Functor (VisitorT m) where
    fmap = liftM

instance Monad m => Applicative (VisitorT m) where
    (<*>) = ap
    pure = return

instance Monad m => Monad (VisitorT m) where
    VisitorT cmd >>= f = VisitorT $ cmd >>= (unVisitor . f)
    return = VisitorT . return

instance MonadTrans VisitorT where
    lift = VisitorT . lift . lift

--instance Monad m => MonadReader (LineInfo,[LatexDoc]) (VisitorT m) where
--    ask = VisitorT $ lift ask -- fst
--    local f (VisitorT cmd) = VisitorT $ ErrorT $ do
--            local f $ runErrorT cmd

instance Monad m => MonadReader LineInfo (VisitorT m) where
    ask = VisitorT $ lift $ asks fst
    local f (VisitorT cmd) = VisitorT $ ErrorT $ do
            local g $ runErrorT cmd
        where
            g (li,x) = (f li, x)

instance S.MonadState s m => S.MonadState s (VisitorT m) where
    get = lift $ S.get
    put x = lift $ S.put x

get_content :: Monad m => VisitorT m [LatexDoc]
get_content = VisitorT $ lift $ asks snd

with_content :: Monad m
             => LineInfo -> [LatexDoc]
             -> VisitorT m a -> VisitorT m a
with_content li xs (VisitorT cmd) = VisitorT $ local (const (li,xs)) cmd


instance Monad m => MonadError (VisitorT m) where
    soft_error x = VisitorT $ soft_error x
    hard_error x = VisitorT $ hard_error x
    make_hard (VisitorT cmd) = VisitorT $ make_hard cmd
    make_soft x (VisitorT cmd) = VisitorT $ make_soft x cmd

--instance Monad m => MonadReader (ParamT m) (VisitorT m) where

add_state :: Monad m
          => s -> VisitorT (ST.StateT s m) a 
          -> VisitorT m (a,s)
add_state s (VisitorT cmd) = VisitorT $ ErrorT $ ReaderT $ \r -> do
        (x,s) <- ST.runStateT (runReaderT (runErrorT cmd) r) s
        let f (x,y) = ((x,s),y)
        return $ either Left (Right . f) x

add_writer :: Monad m
           => VisitorT (WriterT w m) a 
           -> VisitorT m (a,w)
add_writer (VisitorT cmd) = VisitorT $ ErrorT $ ReaderT $ \r -> do
        (x,s) <- runWriterT (runReaderT (runErrorT cmd) r) 
        let f (x,y) = ((x,s),y)
        return $ either Left (Right . f) x

lift_i :: (Monad m, MonadTrans t)
       => VisitorT m a
       -> VisitorT (t m) a
lift_i (VisitorT cmd) = VisitorT $ ErrorT $ ReaderT $ \r -> do
        lift (runReaderT (runErrorT cmd) r)
--        let f (x,y) = (x,y)
--        return $ either Left (Right . f) x

run_visitor :: Monad m 
            => LineInfo
            -> [LatexDoc]
            -> VisitorT m a
            -> EitherT [Error] m a
run_visitor li xs (VisitorT cmd) = EitherT $ do
        x <- runReaderT (runErrorT cmd) (li,xs)
        case x of
            Right (x,[])  -> return $ Right x
            Right (_,err) -> return $ Left err
            Left err      -> return $ Left err

visitor :: Monad m 
        => [(String,VEnvBlock m)] 
        -> [(String,VCmdBlock m)] 
        -> VisitorT m ()
visitor blks cmds = do
        unless (all (\(x,_) -> take 1 x == "\\") cmds) 
            $ error $ format ("Document.Visitor.visitor: "
                    ++ "all commands must start with '\\': {0}")
                $ map fst cmds
        xs <- VisitorT $ lift $ asks snd
        runReaderT (do
            forM_ xs ff
            gg xs
            ) (ParamT blks cmds)
--        VisitorT $ RWS.tell w
--        forM 

visit_doc :: [(String,EnvBlock s a)] 
          -> [(String,CmdBlock s a)] 
          -> [LatexDoc] -> a 
          -> RWS b [Error] s a
visit_doc blks cmds cs x = do
--        s0 <- RWS.get
        unless (all (\(x,_) -> take 1 x == "\\") cmds) 
            $ error $ format ("Document.Visitor.visit_doc: "
                    ++ "all commands must start with '\\': {0}")
                $ map fst cmds
        (err,x) <- flip ST.runStateT x $ 
            runEitherT $ 
            run_visitor (line_info cs) cs $ visitor 
                (L.map f blks) 
                (L.map g cmds)
        either RWS.tell return err
        return x
    where
        f (x,EnvBlock g) = (x,VEnvBlock $ \y z -> VisitorT $ do
                    li <- lift $ asks fst
                    lift $ lift $ do
                        x <- ST.get
                        x <- lift $ fromEither x $ run li $ g y z x
                        ST.put x)
        g (x,CmdBlock f) = (x,VCmdBlock $ \x -> VisitorT $ do
                    li <- lift $ asks fst
                    lift $ lift $ do
                        y <- ST.get
                        y <- lift $ fromEither y $ run li $ f x y
                        ST.put y)
--        f (x,EnvBlock g) = (x,VEnvBlock $ \y z -> do
----                    li <- lift $ ask
----                    lift $ do
--                    x <- ST.get
--                    x <- lift $ fromEither x $ g y z x
--                    ST.put x)
--        g (x,CmdBlock f) = (x,VCmdBlock $ \x -> do
----                    li <- lift $ ask
----                    lift $ do
--                    y <- ST.get
--                    y <- lift $ fromEither y $ f x y
--                    ST.put y)
--        let (r,s1,w) = runRWS (do
--                        x <- foldM (f blks) x cs
--                        g x cs)
--                        (Param blks cmds) s0
--        RWS.put s1
--        RWS.tell w
--        return r

run :: (Monoid c, Monad m)
    => LineInfo
    -> EitherT [Error] (RWST LineInfo c d m) a
    -> EitherT [Error] (RWST b c d m) a
run li m = EitherT $ do 
        s <- get
        x <- withRWST (const (const (li,s))) $ runEitherT m
        return x

--pushEither :: (Monoid c, Monad m)
--           => e -> EitherT c (RWST a c d m) e 
--           -> RWST a c d m e
--pushEither y m = do
--        x <- runEitherT m
--        case x of
--            Right x -> return x
--            Left xs -> do
--                RWS.tell xs
--                return y

ff :: Monad m
   => LatexDoc 
   -> ReaderT (ParamT m) (VisitorT m) ()
ff (Env s li xs _) = do
            r <- asks $ L.lookup s . blocksT
            case r of
                Just (VEnvBlock g)  -> do
                    (args,xs) <- lift $ VisitorT $ fromEitherT $ get_tuple' xs li
                    lift $ with_content li xs $ g args xs
                Nothing -> do
                    forM_ xs ff
                    gg xs
ff (Bracket _ _ cs _) = do
            forM_ cs ff
            gg cs
ff (Text _) = return ()

--f :: [(String, EnvBlock s a)] -> a -> LatexDoc 
--  -> RWS (Param s a) [Error] s a
--f ((name,EnvBlock g):cs) x e@(Env s li xs _)
--        | name == s = do
--                pushEither x $ run li $ do
--                    (args,xs) <- get_tuple xs 
--                    g args xs x
--        | otherwise = f cs x e
--f [] x (Env _ _ xs _)  = do
--        blks <- asks blocks
--        x    <- foldM (f blks) x xs
--        g x xs
--f _ x (Bracket _ _ cs _)     = do
--        blks <- asks blocks
--        x    <- foldM (f blks) x cs
--        g x cs
--f _ x (Text _)               = return x

gg :: Monad m => [LatexDoc] 
   -> ReaderT (ParamT m) (VisitorT m) ()
gg (Text xs : ts) = do
    case trim_blanks $ reverse xs of
        Command c li:_   -> do
                r <- asks $ L.lookup c . cmdsT
                case r of
                    Just (VCmdBlock f) -> do
                        (args,_) <- lift $ VisitorT $ fromEitherT $ get_tuple' ts li
                        lift $ with_content li [] $ f args 
                        r <- gg ts
                        return r
                    Nothing -> gg ts
        _                   -> gg ts
gg (_ : ts) = gg ts
gg [] = return ()

--g :: a -> [LatexDoc] 
--  -> RWS (Param s a) [Error] s a
--g x (Text xs : ts) = do
--    case trim_blanks $ reverse xs of
--        Command c li:_   -> do
--                cmds <- asks cmds
--                h cmds x c ts li
--        _                   -> g x ts
--g x (_ : ts) = g x ts
--g x [] = return x

--h :: [(String,CmdBlock s a)] -> a -> String -> [LatexDoc] 
--  -> LineInfo -> RWS (Param s a) [Error] s a
--h ((name,c):cs) x cmd ts li
--    | name == cmd   =
--            case c of 
--                CmdBlock f -> do
--                    x <- pushEither x $ run li $ do
--                        (args,_) <- get_tuple ts
--                        f args x 
--                    r <- g x ts
--                    return r
--    | otherwise     = h cs x cmd ts li
--h [] x _ ts _       = g x ts 

\end{code}
