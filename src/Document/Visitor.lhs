\subsection{Visitor}

\begin{code}
{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE ExistentialQuantification  #-}
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
    , visitor, raise, raise'
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
    , M (..)
    , unM, runM
    , Document.Visitor.hoistEither
    , hoistValidation
    , triggerV
    , unfailV
    , Document.Visitor.left
    , AllReadable (..) )
where

    -- Modules

import Latex.Parser as P

import Logic.Expr

import UnitB.Syntax

    -- Libraries
import Control.Arrow ((&&&))
import Control.Lens

import           Control.Monad.Except
import           Control.Monad.Reader.Class hiding (reader)
import           Control.Monad.Trans.RWS (RWS,RWST,mapRWST,withRWST)
import qualified Control.Monad.Trans.RWS as RWS
import           Control.Monad.Reader       hiding ( reader )
import           Control.Monad.State.Class as S
import           Control.Monad.Trans.Either as E
import qualified Control.Monad.Trans.State as ST
import           Control.Monad.Trans.Writer ( WriterT ( .. ), runWriterT )

import           Data.Char
import           Data.Either.Validation
import           Data.Foldable as F
import           Data.List as L
import qualified Data.Map as M
import           Data.Maybe
import           Data.Set hiding (map)
import           Data.String.Utils
import           Data.Traversable as T

import qualified Text.ParserCombinators.ReadPrec as RP ( get, pfail, (<++) )

import GHC.Read

import Text.Printf.TH

import Utilities.Error hiding (MonadError)
import qualified Utilities.Error as E
import Utilities.Syntactic
import Utilities.Tuple

newtype M a = M { _unM :: EitherT [Error] (RWS LineInfo [Error] ()) a }
    deriving (Functor,Monad,MonadReader LineInfo,MonadError [Error])

instance Applicative M where
    pure = M . pure
    M f <*> M x = M $ EitherT $ do
        f' <- runEitherT f
        x' <- runEitherT x
        return $ validationToEither $ eitherToValidation f' <*> eitherToValidation x'

makeLenses ''M

hoistEither :: Either [Error] a -> M a
hoistEither = M . E.hoistEither

hoistValidation :: Validation [Error] a 
                -> M a
hoistValidation = M . EitherT . return . validationToEither

triggerV :: Validation [Error] a -> M a
triggerV = hoistValidation

unfailV :: M a -> M (Validation [Error] a)
unfailV (M (EitherT cmd)) = M $ lift $ eitherToValidation <$> cmd

left :: [Error] -> M a
left = M . E.left

runM :: M a -> LineInfo -> (Either [Error] a,[Error])
runM (M cmd) li = (r,es)
    where
        (r,(),es) = RWS.runRWS (runEitherT cmd) li ()

class Readable a where
    read_args :: (Monad m)
              => ST.StateT LatexDoc (EitherT [Error] m) a
    read_one :: (Monad m)
             => Impl m a

get_tuple' :: (Monad m, IsTuple a, AllReadable (TypeList a))
           => LatexDoc -> LineInfo 
           -> EitherT [Error] m (a, LatexDoc)
get_tuple' xs li = EitherT $ do
        x <- runReaderT (runEitherT $ ST.runStateT get_tuple xs) li
        return $ liftM (\(x,y) -> (fromTuple x,y)) x

class AllReadable a where
    get_tuple :: (Monad m, MonadReader LineInfo m) 
              => ST.StateT LatexDoc (EitherT [Error] m) a
    read_all :: (Monad m, MonadReader LineInfo m) 
             => Impl m a

instance AllReadable () where
    get_tuple = return () 
    read_all = do
        (xs,_) <- get
        case xs of
            x:_ -> lift $ E.left [Error "too many arguments" $ line_info x]
            [] -> return ()

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

type Impl m = ST.StateT ([LatexDoc],LineInfo) (EitherT [Error] m)

get_next :: (Monad m)
         => Impl m LatexDoc
get_next = do
    (s,li)  <- get
    case s of
      x:xs -> put (xs,li) >> return x
      [] -> do
        -- li <- ask
        lift $ E.left [Error "expecting more arguments" li]

instance Readable LatexDoc where
    read_args = do
        -- ts <- read_args
        -- li <- ask
        -- return $ LatexDoc ts li
        ts <- ST.get
        ([arg],ts) <- lift $ cmd_params 1 ts
        ST.put ts
        return arg
    read_one = do
        get_next

data Str = String { toString :: String }

read_label :: Monad m
           => Impl m (String,LineInfo)
read_label = do
    x  <- get_next    
    let x' = trim_blank_text' x
    lift $ case isWord' x' of
        Just (x,li) -> right (x,li)
        _   -> E.left [Error "expecting a label" $ line_info x']

instance Readable Str where
    read_args = do
        ts <- ST.get
        (arg,ts) <- lift $ get_1_lbl ts
        ST.put ts
        return $ String arg
    read_one = do
        (x,_) <- read_label
        return $ String x

instance Readable Int where
    read_args = do
        ts <- ST.get
        (arg,ts) <- lift $ get_1_lbl ts
        ST.put ts
        case reads arg of 
            [(n,"")] -> return n
            _ -> lift $ do
                E.left [Error ([s|invalid integer: '%s'|] arg) $ line_info ts]
    read_one = do
        (arg,li) <- read_label
        case reads arg of
            [(n,"")] -> return n
            _ -> lift $ do
                E.left [Error ([s|invalid integer: '%s'|] arg) li]

instance Readable Double where
    read_args = do
        ts <- ST.get
        (arg,ts) <- lift $ get_1_lbl ts
        ST.put ts
        case reads arg of 
            [(n,"")] -> return n
            _ -> lift $ do
                E.left [Error ([s|invalid number: '%s'|] arg) $ line_info ts]
    read_one = do
        (arg,li) <- read_label
        case reads arg of
            [(n,"")] -> return n
            _ -> lift $ do
                E.left [Error ([s|invalid number: '%s'|] arg) li]

instance Readable (Maybe Label) where
    read_args = do
        ts <- ST.get
        (arg,ts) <- lift $ cmd_params 1 ts
        ST.put ts
        let xs = (concatMap flatten' arg)
        if strip xs == "" then 
            return Nothing
        else return $ Just $ label xs
    read_one = do
        arg <- get_next
        let xs = flatten' arg
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
        (label . fst) <$> read_label

instance Readable [Label] where
    read_args = do
        ts <- ST.get
        ([arg],ts) <- lift $ cmd_params 1 ts
        ST.put ts
        return $ map label $ comma_sep (flatten' arg)
    read_one = do
        arg <- get_next
        return $ map label $ comma_sep (flatten' arg)

instance Readable [Str] where
    read_args = do
        ts <- ST.get
        ([arg],ts) <- lift $ cmd_params 1 ts
        ST.put ts
        return $ map String $ comma_sep (flatten' arg)
    read_one = do
        arg <- get_next
        return $ map String $ comma_sep (flatten' arg)

instance Readable [[Str]] where
    read_args = do
        ts <- ST.get
        ([arg],ts) <- lift $ cmd_params 1 ts
        ST.put ts
        case reads $ flatten' arg of 
            [(n,"")] -> return n
            _ -> lift $ do
                throwError [Error ([s|invalid list of strings: '%s'|] $ show arg) $ line_info arg]
    read_one = do
        arg <- get_next
        case reads $ flatten' arg of 
            [(n,"")] -> return n
            _ -> lift $ do
                throwError [Error ([s|invalid list of strings: '%s'|] $ show arg) $ line_info arg]

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
        return $ fromList $ map label $ comma_sep (flatten' arg)
    read_one = do
        arg <- get_next
        return $ fromList $ map label $ comma_sep (flatten' arg)

instance Readable (M.Map Label ()) where
    read_args = do
        M.fromSet (const ()) <$> read_args
    read_one = do
        M.fromSet (const ()) <$> read_one

instance Readable Name where
    read_one  = do
        (xs,li) <- read_label
        lift $ E.hoistEither $ with_li li $ isName xs
    read_args = do
        xs <- read_args
        let xs' = flatten' xs
            li  = line_info xs
        lift $ E.hoistEither $ with_li li $ isName xs'

instance Readable [Name] where
    read_args = do
        arg <- read_args
        let parse x = eitherToValidation $ isName x
            li  = line_info arg
        lift $ E.hoistEither 
             $ with_li li 
             $ validationToEither 
             $ traverse parse 
             $ comma_sep (flatten' arg)
    read_one = do
        arg <- get_next
        let parse x = eitherToValidation $ isName x
            li  = line_info arg
        lift $ E.hoistEither 
             $ with_li li 
             $ validationToEither 
             $ traverse parse 
             $ comma_sep (flatten' arg)

instance Readable MachineId where
    read_one = do
        xs <- read_one
        return $ MId $ (xs :: Name)
    read_args = do
        xs <- read_args
        return $ MId $ (xs :: Name)

instance Readable ProgId where
    read_one  = liftM PId read_one
    read_args = liftM PId read_args
        
instance Readable (Maybe ProgId) where
    read_one  = fmap PId <$> read_one
    read_args = fmap PId <$> read_args

raise :: MonadError [Error] m 
      => Error -> m a
raise e = throwError [e]

raise' :: (MonadError [Error] m,MonadReader LineInfo m)
       => (LineInfo -> Error) -> m a
raise' e = do
    raise . e =<< ask

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

cmd_params :: (Monad m)
           => Int -> LatexDoc 
           -> EitherT [Error] m ([LatexDoc], LatexDoc)
cmd_params 0 xs     = right ([], xs)
cmd_params n xs     = do
        let xs' = drop_blank_text' xs
        case unconsTex xs' of
            Just (BracketNode (Bracket _ _ xs _), ys) -> do
                (ws, zs) <- cmd_params (n-1) ys
                right (xs:ws, zs)
            _                 -> throwError [Error ("Expecting one more argument") $ line_info xs]

get_1_lbl :: (Monad m)
          => LatexDoc -> EitherT [Error] m (String, LatexDoc)
get_1_lbl xs = do 
        ([x],z) <- cmd_params 1 xs
        let x' = trim_blank_text' x
        case isWord x' of
            Just x
                -> right (x,z)
            _   -> err_msg x'
    where
        err_msg x = throwError [Error "expecting a label" $ line_info x]
        
--get_2_lbl :: (Monad m, MonadReader (Int,Int) m)
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



with_line_info :: LineInfo -> EitherT a (ReaderT LineInfo m) b -> EitherT a m b
with_line_info li cmd = 
        EitherT $ runReaderT (runEitherT cmd) li
        

    -- Given a Latex document piece, find one instance
    -- of the given command, its arguments and the
    -- the parts surrounding it to the left and right
find_cmd_arg :: Int -> [String] -> LatexDoc
             -> Maybe (LatexDoc,LatexToken,[LatexDoc],LatexDoc)
find_cmd_arg n cmds xs = -- (x@(Text xs _) : cs) =
        case unconsTex xs of
          Just (Text t@(Command ys li), cs)
            --case (first reverse $ trim_blanks (xs,li')) of
            --  (t@(Command ys li):zs,li')
                | ys `elem` cmds ->
                    eitherT
                            (\_       -> Nothing)
                            (\(xs,ws) -> Just (f li,t,xs,ws))
                        $ with_line_info li
                        $ cmd_params n cs
              --_    -> do
              --  _1 `over` consTex x <$> find_cmd_arg n cmds cs
          Nothing -> Nothing
          Just (x,xs) -> do
                _1 `over` consTex x <$> find_cmd_arg n cmds xs
    where
        f li = Doc li [] li


    -- Bad, bad... unify the monad system of refinement, proof and machine already!
    

type Node s = EitherT [Error] (RWS LineInfo [Error] s)

data EnvBlock s a = 
            forall t. (IsTuple t, AllReadable (TypeList t))
         => EnvBlock (t -> LatexDoc -> a -> Node s a)

data CmdBlock s a =
            forall t. (IsTuple t, AllReadable (TypeList t))
         => CmdBlock (t -> a -> Node s a)

data VEnvBlock m = forall t. (IsTuple t, AllReadable (TypeList t))
                => VEnvBlock (t -> LatexDoc -> VisitorT m ())

data VCmdBlock m =
               forall t. (IsTuple t, AllReadable (TypeList t))
            => VCmdBlock (t -> VisitorT m ())

type MSEither = RWS LineInfo [Error] SystemAST

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

toEither :: RWS LineInfo [Error] () b -> M b
toEither m = M $ EitherT $ mapRWST f $ do
        (x,xs) <- RWS.listen m
        case xs of
            [] -> return $ Right x
            xs -> return $ Left xs
    where
        f m = m >>= \(x,y,_) -> return (x,y,[])

bind :: (MonadError [Error] m,MonadReader r m,Syntactic r)
     => String -> Maybe a -> m a
bind msg Nothing = do
        li <- asks line_info
        throwError [Error msg li]
bind _ (Just x) = return x

bind_all :: (Traversable t,MonadReader r m,Syntactic r,MonadError [Error] m)
         => t a
         -> (a -> String) 
         -> (a -> Maybe b)
         -> m (t b)
bind_all xs msgs lu = do
            let ys' = (id &&& lu) <$> xs
                ys  = T.mapM snd ys'
                zs = fmap (msgs . fst) 
                    $ L.filter (isNothing . snd) 
                    $ F.toList ys'
            -- assert $ isNothing ys == not (null zs)
            li <- asks line_info
            maybe (throwError [Error msg li | msg <- zs]) return ys


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

newtype VisitorT m a = VisitorT { unVisitor :: ErrorT (ReaderT (LineInfo, LatexDoc) m) a }
    deriving (Functor,Applicative,Monad,E.MonadError)

instance MonadTrans VisitorT where
    lift = VisitorT . lift . lift

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

get_content :: Monad m => VisitorT m LatexDoc
get_content = VisitorT $ lift $ asks snd

with_content :: Monad m
             => LatexDoc
             -> VisitorT m a -> VisitorT m a
with_content xs (VisitorT cmd) = VisitorT $ local (const (li,xs)) cmd
    where
        li = line_info xs

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
            -> LatexDoc
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
            $ error $ "Document.Visitor.visitor: "
                    ++ [s|all commands must start with '\\': %s|] (show $ map fst cmds)
        xs <- VisitorT $ lift $ asks snd
        runReaderT (do
            forM_ (contents' xs) ff
            gg xs
            ) (ParamT blks cmds)
--        VisitorT $ RWS.tell w
--        forM 

visit_doc :: [(String,EnvBlock s a)] 
          -> [(String,CmdBlock s a)] 
          -> LatexDoc -> a 
          -> RWS b [Error] s a
visit_doc blks cmds cs x = do
--        s0 <- RWS.get
        unless (all (\(x,_) -> take 1 x == "\\") cmds) 
            $ error $ "Document.Visitor.visit_doc: "
                    ++ [s|all commands must start with '\\': %s|] (show $ map fst cmds)
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
   => LatexNode 
   -> ReaderT (ParamT m) (VisitorT m) ()
ff (EnvNode (Env _ s li xs _)) = do
            r <- asks $ L.lookup s . blocksT
            case r of
                Just (VEnvBlock g)  -> do
                    (args,xs) <- lift $ VisitorT $ fromEitherT $ get_tuple' xs li
                    lift $ with_content xs $ g args xs
                Nothing -> do
                    forM_ (contents' xs) ff
                    gg xs
ff (BracketNode (Bracket _ _ cs _)) = do
            forM_ (contents' cs) ff
            gg cs
ff (Text _) = return ()

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

gg :: Monad m => LatexDoc
   -> ReaderT (ParamT m) (VisitorT m) ()
gg x =
    case unconsTex x of
      Just (Text (Command c li), ts) -> do
            r <- asks $ L.lookup c . cmdsT
            case r of
                Just (VCmdBlock f) -> do
                    (args,_) <- lift $ VisitorT $ fromEitherT $ get_tuple' ts li
                    lift $ with_content (Doc li [] li) 
                        $ f args 
                    r <- gg ts
                    return r
                Nothing -> gg ts
      Just (_, ts) -> gg ts
      Nothing -> return ()

--  -> RWS (Param s a) [Error] s a
--g x (Text xs : ts) = do
--    case trim_blanks $ reverse xs of
--        Command c li:_   -> do
--                cmds <- asks cmds
--                h cmds x c ts li
--        _                   -> g x ts
--g x (_ : ts) = g x ts
--g x [] = return x

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
