{-# LANGUAGE BangPatterns, RankNTypes #-}
module Document.Visitor where

    -- Modules
import Latex.Parser

import Document.Expression

    -- Libraries
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Trans.Either
import Control.Monad.Trans.Writer

import System.IO
import System.IO.Unsafe

import Utilities.Syntactic

drop_blank_text :: [LatexDoc] -> [LatexDoc]
drop_blank_text ( Text [Blank _ _] : ys ) = drop_blank_text ys
drop_blank_text ( Text (Blank _ _ : xs) : ys ) = drop_blank_text ( Text xs : ys )
drop_blank_text xs = xs

trim_blank_text xs = reverse $ drop_blank_text (reverse $ drop_blank_text xs)

skip_blanks :: [LatexToken] -> [LatexToken]
skip_blanks (Blank _ _ : xs) = xs
skip_blanks xs = xs 

trim_blanks :: [LatexToken] -> [LatexToken]
trim_blanks xs = reverse $ skip_blanks $ reverse $ skip_blanks xs

cmd_params :: Monad m => Int -> [LatexDoc] 
           -> EitherT [Error] m ([[LatexDoc]], [LatexDoc])
cmd_params 0 xs     = right ([], xs)
cmd_params n xs     = 
        case drop_blank_text xs of
            Bracket _ _ xs _ : ys -> do
                (ws, zs) <- cmd_params (n-1) ys
                right (xs:ws, zs)
            x                 -> left [("bad argument: " ++ show xs,-1,-1)]

cmd_params_ n xs = fmap fst $ cmd_params n xs

    -- Given a Latex document piece, find one instance
    -- of the given command, its arguments and the
    -- the parts surrounding it to the left and right
find_cmd_arg :: Int -> [String] -> [LatexDoc] 
             -> Maybe ([LatexDoc],LatexToken,[[LatexDoc]],[LatexDoc])
find_cmd_arg n cmds (x@(Text xs) : cs) = 
        case (trim_blanks $ reverse xs) of
            (t@(Command ys _):zs) -> 
                    if ys `elem` cmds
                    then eitherT
                            (\_       -> Nothing)
                            (\(xs,ws) -> Just (f zs,t,xs,ws))
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

get_1_lbl :: Monad m => [LatexDoc] -> EitherT [Error] m (String, [LatexDoc])
get_1_lbl xs = do 
        ([x],z) <- cmd_params 1 xs
        case trim_blank_text x of
            ([Text [TextBlock x _]]) 
                -> right (x,z)
            ([Text [Command x _]]) 
                -> right (x,z)
            _   -> err_msg (line_info xs)
    where
        err_msg (i,j) = left [("expecting a label",i,j)]
        
get_2_lbl :: Monad m => [LatexDoc] -> EitherT [Error] m (String, String, [LatexDoc])
get_2_lbl xs = do
        (lbl0,xs) <- get_1_lbl xs
        (lbl1,xs) <- get_1_lbl xs
        return (lbl0,lbl1,xs)

get_3_lbl xs = do
        (lbl0,xs) <- get_1_lbl xs
        (lbl1,xs) <- get_1_lbl xs
        (lbl2,xs) <- get_1_lbl xs
        return (lbl0,lbl1,lbl2,xs)

get_4_lbl xs = do
        (lbl0,xs) <- get_1_lbl xs
        (lbl1,xs) <- get_1_lbl xs
        (lbl2,xs) <- get_1_lbl xs
        (lbl3,xs) <- get_1_lbl xs
        return (lbl0,lbl1,lbl2,lbl3,xs)

type Node = EitherT [Error] (Reader (Int,Int))

type NodeT m = EitherT [Error] (ReaderT (Int,Int) m)

data EnvBlock a = 
        Env0Args (forall m. Monad m => () -> [LatexDoc] -> a -> (Int,Int) -> NodeT m a)
        | Env0Args1Blocks (forall m. Monad m => ([LatexDoc],()) -> [LatexDoc] -> a -> (Int,Int) -> NodeT m a)
        | Env1Args (forall m. Monad m => (String, ()) -> [LatexDoc] -> a -> (Int,Int) -> NodeT m a)
        | Env1Args1Blocks (forall m. Monad m => (String, [LatexDoc]) -> [LatexDoc] -> a -> (Int,Int) -> NodeT m a)
        | Env1Args2Blocks (forall m. Monad m => (String, [LatexDoc], [LatexDoc]) -> [LatexDoc] -> a -> (Int,Int) -> NodeT m a)
        | Env2Args (forall m. Monad m => (String, String) -> [LatexDoc] -> a -> (Int,Int) -> NodeT m a)

data CmdBlock a =
        Cmd0Args (forall m. Monad m => () -> a -> (Int,Int) -> NodeT m a)
        | Cmd0Args1Blocks (forall m. Monad m => ([LatexDoc], ()) -> a -> (Int,Int) -> NodeT m a)
        | Cmd0Args2Blocks (forall m. Monad m => ([LatexDoc], [LatexDoc]) -> a -> (Int,Int) -> NodeT m a)
        | Cmd1Args (forall m. Monad m => (String,()) -> a -> (Int,Int) -> NodeT m a)
        | Cmd1Args1Blocks (forall m. Monad m => (String, [LatexDoc]) -> a -> (Int,Int) -> NodeT m a)
        | Cmd1Args2Blocks (forall m. Monad m => (String, [LatexDoc], [LatexDoc]) -> a -> (Int,Int) -> NodeT m a)
        | Cmd2Args (forall m. Monad m => (String, String) -> a -> (Int,Int) -> NodeT m a)
        | Cmd2Args1Blocks (forall m. Monad m => (String, String, [LatexDoc]) -> a -> (Int,Int) -> NodeT m a)
        | Cmd2Args2Blocks (forall m. Monad m => (String, String, [LatexDoc], [LatexDoc]) -> a -> (Int,Int) -> NodeT m a)
        | Cmd3Args (forall m. Monad m => (String, String, String) -> a -> (Int,Int) -> NodeT m a)
        | Cmd4Args (forall m. Monad m => (String, String, String, String) -> a -> (Int,Int) -> NodeT m a)

type MEither a = Writer [a]

data Param a = Param 
    { blocks :: [(String, EnvBlock a)]
    , cmds   :: [(String, CmdBlock a)] }

--fromEither :: Monad m => a -> EitherT [b] m a -> MEither b a
fromEither y m =
        eitherT
            (\xs -> do
                tell xs
                return y)
            return
            m

toEither :: Monad m => MEither a b -> EitherT [a] m b
toEither m = 
    case runWriter m of
        (x, []) -> right x
        (x, xs) -> left xs

error_list :: (Int,Int) -> [(Bool, String)] -> MEither Error ()
error_list _ [] = return ()
error_list li@(i,j) ( (b,msg):xs )
        | not b = error_list li xs
        | b     = do
            tell [(msg,i,j)]
            error_list li xs

visit_doc :: [(String,EnvBlock a)] -> [(String,CmdBlock a)] -> [LatexDoc] -> a -> MEither Error a
visit_doc blks cmds cs x = runReaderT (do
        x <- foldM (f blks) x cs
        g x cs) (Param blks cmds)

run :: Monad m => EitherT [Error] (ReaderT (Int,Int) m) a -> (Int,Int) -> EitherT [Error] m a
run m li = EitherT (runReaderT (runEitherT m) li)

f :: [(String, EnvBlock a)] -> a -> LatexDoc 
  -> ReaderT (Param a) (MEither Error) a
f ((name,c):cs) x e@(Env s (i,j) xs _)
        | name == s = do
--                let !() = unsafePerformIO (putStrLn ("matching " ++ name))
                lift $ fromEither x 
                     $ run
                 (case c of
                    Env0Args g -> do
                        g () xs x (i,j)
                    Env0Args1Blocks g -> do
                        ([arg0],xs) <- cmd_params 1 xs
                        g (arg0,()) xs x (i,j)
                    Env1Args g -> do
                        (arg,xs) <- get_1_lbl xs
                        g (arg,()) xs x (i,j)
                    Env1Args1Blocks g -> do
                        (arg0,xs) <- get_1_lbl xs
                        ([arg1],xs) <- cmd_params 1 xs
                        g (arg0,arg1) xs x (i,j)
                    Env1Args2Blocks g -> do
                        (arg0,xs) <- get_1_lbl xs
                        ([arg1,arg2],xs) <- cmd_params 2 xs
                        g (arg0,arg1,arg2) xs x (i,j)
                    Env2Args g -> do
                        (arg0,arg1,xs) <- get_2_lbl xs
                        g (arg0,arg1) xs x (i,j))
                    (i,j)
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

g :: a -> [LatexDoc] -> ReaderT (Param a) (MEither Error) a 
g x (Text xs : ts) = do
    case trim_blanks $ reverse xs of
        Command c (i,j):_   -> do
                cmds <- asks cmds
                h cmds x c ts (i,j)
        _                   -> g x ts
g x (t : ts) = g x ts
g x [] = return x

h :: [(String,CmdBlock a)] -> a -> String -> [LatexDoc] 
  -> (Int,Int) -> ReaderT (Param a) (MEither Error) a 
h ((name,c):cs) x cmd ts (i,j)
    | name == cmd   = do
--            let !() = unsafePerformIO (putStrLn ("matching cmd: " ++ name))
            r <- case c of
                Cmd0Args f -> do
                    x <- lift $ fromEither x $ run (f () x (i,j)) (i,j)
                    g x ts
                Cmd1Args f -> do
                    x <- lift $ fromEither x $ run (do
                        (arg,ts) <- get_1_lbl ts
                        f (arg,()) x (i,j))
                        (i,j)
                    g x ts
                Cmd2Args f -> do
                    x <- lift $ fromEither x $ run (do
                        (arg0,arg1,ts) <- get_2_lbl ts
                        f (arg0,arg1) x (i,j))
                        (i,j)
                    g x ts
                Cmd0Args1Blocks f -> do
                    x <- lift $ fromEither x $ run (do
                        ([arg0],ts) <- cmd_params 1 ts
                        f (arg0,()) x (i,j))
                        (i,j)
                    g x ts
                Cmd0Args2Blocks f -> do
                    x <- lift $ fromEither x $ run (do
                        ([arg0,arg1],ts) <- cmd_params 2 ts
                        f (arg0,arg1) x (i,j))
                        (i,j)
                    g x ts
                Cmd1Args1Blocks f -> do
                    x <- lift $ fromEither x $ run (do
                        (arg0,ts) <- get_1_lbl ts
                        ([arg1],ts) <- cmd_params 1 ts
                        f (arg0,arg1) x (i,j))
                        (i,j)
                    g x ts
                Cmd1Args2Blocks f -> do
                    x <- lift $ fromEither x $ run (do
                        (arg0,ts) <- get_1_lbl ts
                        ([arg1,arg2],ts) <- cmd_params 2 ts
                        f (arg0,arg1,arg2) x (i,j))
                        (i,j)
                    g x ts
                Cmd2Args1Blocks f -> do
                    x <- lift $ fromEither x $ run (do
                        (arg0,arg1,ts) <- get_2_lbl ts
                        ([arg2],ts) <- cmd_params 1 ts
                        f (arg0,arg1,arg2) x (i,j))
                        (i,j)
                    g x ts
                Cmd2Args2Blocks f -> do
                    x <- lift $ fromEither x $ run (do
                        (arg0,arg1,ts) <- get_2_lbl ts
                        ([arg2,arg3],ts) <- cmd_params 2 ts
                        f (arg0,arg1,arg2,arg3) x (i,j))
                        (i,j)
                    g x ts
                Cmd3Args f -> do
                    x <- lift $ fromEither x $ run (do
                        (arg0,arg1,arg2,ts) <- get_3_lbl ts
                        f (arg0,arg1,arg2) x (i,j))
                        (i,j)
                    g x ts
                Cmd4Args f -> do
                    x <- lift $ fromEither x $ run (do
                        (arg0,arg1,arg2,arg3,ts) <- get_4_lbl ts
                        f (arg0,arg1,arg2,arg3) x (i,j))
                        (i,j)
                    g x ts
            return r
    | otherwise     = h cs x cmd ts (i,j)
h [] x cmd ts (i,j) = g x ts 
