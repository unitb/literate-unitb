{-# LANGUAGE BangPatterns, RankNTypes #-}
module Document.Visitor where

    -- Modules
import Latex.Parser

import Document.Expression

    -- Libraries
import 
    Control.Monad.Trans.RWS hiding ( ask, tell, asks )
import qualified
    Control.Monad.Trans.RWS as RWS
import Control.Monad.Reader
import Control.Monad.Trans.Either

import Data.Monoid

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

type Node s = EitherT [Error] (RWS (Int,Int) [Error] s)
type NodeT s m = EitherT [Error] (RWST (Int,Int) [Error] s m)

data EnvBlock s a = 
        Env0Args (() -> [LatexDoc] -> a -> Node s a)
        | Env0Args1Blocks (([LatexDoc],()) -> [LatexDoc] -> a -> Node s a)
        | Env1Args ((String, ()) -> [LatexDoc] -> a -> Node s a)
        | Env1Args1Blocks ((String, [LatexDoc]) -> [LatexDoc] -> a -> Node s a)
        | Env1Args2Blocks ((String, [LatexDoc], [LatexDoc]) -> [LatexDoc] -> a -> Node s a)
        | Env2Args ((String, String) -> [LatexDoc] -> a -> Node s a)

data CmdBlock s a =
        Cmd0Args (() -> a -> Node s a)
        | Cmd0Args1Blocks (([LatexDoc], ()) -> a -> Node s a)
        | Cmd0Args2Blocks (([LatexDoc], [LatexDoc]) -> a -> Node s a)
        | Cmd1Args ((String,()) -> a -> Node s a)
        | Cmd1Args1Blocks ((String, [LatexDoc]) -> a -> Node s a)
        | Cmd1Args2Blocks ((String, [LatexDoc], [LatexDoc]) -> a -> Node s a)
        | Cmd2Args ((String, String) -> a -> Node s a)
        | Cmd2Args1Blocks ((String, String, [LatexDoc]) -> a -> Node s a)
        | Cmd2Args2Blocks ((String, String, [LatexDoc], [LatexDoc]) -> a -> Node s a)
        | Cmd3Args ((String, String, String) -> a -> Node s a)
        | Cmd4Args ((String, String, String, String) -> a -> Node s a)

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
f ((name,c):cs) x e@(Env s (i,j) xs _)
        | name == s = do
                pushEither x 
                     $ run (i,j)
                 (case c of
                    Env0Args g -> do
                        g () xs x
                    Env0Args1Blocks g -> do
                        ([arg0],xs) <- cmd_params 1 xs 
                        g (arg0,()) xs x
                    Env1Args g -> do
                        (arg,xs) <- get_1_lbl xs
                        g (arg,()) xs x
                    Env1Args1Blocks g -> do
                        (arg0,xs)   <- get_1_lbl xs
                        ([arg1],xs) <- cmd_params 1 xs
                        g (arg0,arg1) xs x
                    Env1Args2Blocks g -> do
                        (arg0,xs)        <- get_1_lbl xs
                        ([arg1,arg2],xs) <- cmd_params 2 xs
                        g (arg0,arg1,arg2) xs x
                    Env2Args g -> do
                        (arg0,arg1,xs) <- get_2_lbl xs
                        g (arg0,arg1) xs x)
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
    | name == cmd   = do
            r <- case c of
                Cmd0Args f -> do
                    x <- pushEither x $ run (i,j) $ f () x
                    g x ts
                Cmd1Args f -> do
                    x <- pushEither x $ run (i,j) $ do
                        (arg,ts) <- get_1_lbl ts
                        f (arg,()) x
                    g x ts
                Cmd2Args f -> do
                    x <- pushEither x $ run (i,j) $ do
                        (arg0,arg1,ts) <- get_2_lbl ts
                        f (arg0,arg1) x
                    g x ts
                Cmd0Args1Blocks f -> do
                    x <- pushEither x $ run (i,j) $ do
                        ([arg0],ts) <- cmd_params 1 ts
                        f (arg0,()) x
                    g x ts
                Cmd0Args2Blocks f -> do
                    x <- pushEither x $ run (i,j) $ do
                        ([arg0,arg1],ts) <- cmd_params 2 ts
                        f (arg0,arg1) x
                    g x ts
                Cmd1Args1Blocks f -> do
                    x <- pushEither x $ run (i,j) $ do
                        (arg0,ts) <- get_1_lbl ts
                        ([arg1],ts) <- cmd_params 1 ts
                        f (arg0,arg1) x
                    g x ts
                Cmd1Args2Blocks f -> do
                    x <- pushEither x $ run (i,j) $ do
                        (arg0,ts) <- get_1_lbl ts
                        ([arg1,arg2],ts) <- cmd_params 2 ts
                        f (arg0,arg1,arg2) x 
                    g x ts
                Cmd2Args1Blocks f -> do
                    x <- pushEither x $ run (i,j) $ do
                        (arg0,arg1,ts) <- get_2_lbl ts
                        ([arg2],ts) <- cmd_params 1 ts
                        f (arg0,arg1,arg2) x 
                    g x ts
                Cmd2Args2Blocks f -> do
                    x <- pushEither x $ run (i,j) $ do
                        (arg0,arg1,ts) <- get_2_lbl ts
                        ([arg2,arg3],ts) <- cmd_params 2 ts
                        f (arg0,arg1,arg2,arg3) x 
                    g x ts
                Cmd3Args f -> do
                    x <- pushEither x $ run (i,j) $ do
                        (arg0,arg1,arg2,ts) <- get_3_lbl ts
                        f (arg0,arg1,arg2) x 
                    g x ts
                Cmd4Args f -> do
                    x <- pushEither x $ run (i,j) $ do
                        (arg0,arg1,arg2,arg3,ts) <- get_4_lbl ts
                        f (arg0,arg1,arg2,arg3) x 
                    g x ts
            return r
    | otherwise     = h cs x cmd ts (i,j)
h [] x cmd ts (i,j) = g x ts 
