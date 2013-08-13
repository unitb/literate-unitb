module Document.Visitor where

    -- Modules
import Latex.Parser

import Document.Expression

    -- Libraries
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

cmd_params :: Int -> [LatexDoc] -> Either [Error] ([[LatexDoc]], [LatexDoc])
cmd_params 0 xs     = Right ([], xs)
cmd_params n xs     = 
        case drop_blank_text xs of
            Bracket _ _ xs _ : ys -> do
                (ws, zs) <- cmd_params (n-1) ys
                Right (xs:ws, zs)
            x                 -> Left [("bad argument: " ++ show xs,-1,-1)]

cmd_params_ n xs = fmap fst $ cmd_params n xs

find_cmd_arg :: Int -> [String] -> [LatexDoc] 
             -> Maybe ([LatexDoc],LatexToken,[[LatexDoc]],[LatexDoc])
find_cmd_arg n cmds (x@(Text xs) : cs) = 
        case (trim_blanks $ reverse xs) of
            (t@(Command ys _):zs) -> 
                    if ys `elem` cmds
                    then do
                        case cmd_params n cs of
                            Right (xs,ws) -> Just (f zs,t,xs,ws)
                            Left _        -> Nothing
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

get_1_lbl :: [LatexDoc] -> Either [Error] (String, [LatexDoc])
get_1_lbl xs = do 
        ([x],z) <- cmd_params 1 xs
        case trim_blank_text x of
            ([Text [TextBlock x _]]) 
                -> Right (x,z)
            ([Text [Command x _]]) 
                -> Right (x,z)
            _   -> err_msg (line_info xs)
    where
        err_msg (i,j) = Left [("expecting a label",i,j)]
        
get_2_lbl :: [LatexDoc] -> Either [Error] (String, String, [LatexDoc])
get_2_lbl xs = do
        (lbl0,xs) <- get_1_lbl xs
        (lbl1,xs) <- get_1_lbl xs
        return (lbl0,lbl1,xs)

data EnvBlock a = 
        Env0Args (() -> [LatexDoc] -> a -> (Int,Int) -> Either [Error] a)
        | Env0Args1Blocks (([LatexDoc],()) -> [LatexDoc] -> a -> (Int,Int) -> Either [Error] a)
        | Env1Args ((String, ()) -> [LatexDoc] -> a -> (Int,Int) -> Either [Error] a)
        | Env1Args1Blocks ((String, [LatexDoc]) -> [LatexDoc] -> a -> (Int,Int) -> Either [Error] a)
        | Env1Args2Blocks ((String, [LatexDoc], [LatexDoc]) -> [LatexDoc] -> a -> (Int,Int) -> Either [Error] a)
        | Env2Args ((String, String) -> [LatexDoc] -> a -> (Int,Int) -> Either [Error] a)

data CmdBlock a =
        Cmd0Args (() -> a -> (Int,Int) -> Either [Error] a)
        | Cmd0Args1Blocks (([LatexDoc], ()) -> a -> (Int,Int) -> Either [Error] a)
        | Cmd0Args2Blocks (([LatexDoc], [LatexDoc]) -> a -> (Int,Int) -> Either [Error] a)
        | Cmd1Args ((String,()) -> a -> (Int,Int) -> Either [Error] a)
        | Cmd1Args1Blocks ((String, [LatexDoc]) -> a -> (Int,Int) -> Either [Error] a)
        | Cmd1Args2Blocks ((String, [LatexDoc], [LatexDoc]) -> a -> (Int,Int) -> Either [Error] a)
        | Cmd2Args ((String, String) -> a -> (Int,Int) -> Either [Error] a)
        | Cmd2Args1Blocks ((String, String, [LatexDoc]) -> a -> (Int,Int) -> Either [Error] a)
        | Cmd2Args2Blocks ((String, String, [LatexDoc], [LatexDoc]) -> a -> (Int,Int) -> Either [Error] a)

data MEither a b = MLeft [a] b | MRight b

instance Monad (MEither a) where
    MRight x >>= f = f x
    MLeft xs x >>= f =
        case f x of
            MRight y     -> MLeft xs y
            MLeft ys y   -> MLeft (xs++ys) y
    return x = MRight x

fromEither :: a -> Either [b] a -> MEither b a
fromEither _ (Right x) = MRight x
fromEither y (Left xs) = MLeft xs y

toEither :: MEither a b -> Either [a] b
toEither (MRight x)     = Right x
toEither (MLeft xs y)   = Left xs

error_list :: (Int,Int) -> [(Bool, String)] -> MEither Error ()
error_list _ [] = return ()
error_list li@(i,j) ( (b,msg):xs )
        | not b = error_list li xs
        | b     = case error_list li xs of
                        MRight ()    -> MLeft [(msg,i,j)] ()
                        MLeft xs ()  -> MLeft ((msg,i,j):xs) ()

visit_doc :: [(String,EnvBlock a)] -> [(String,CmdBlock a)] -> [LatexDoc] -> a -> MEither Error a
visit_doc blks cmds cs x = do
        x <- foldl (f blks) (MRight x) cs
        g (MRight x) cs
    where
        f ((name,c):cs) ex e@(Env s (i,j) xs _)
                | name == s = do
                        x <- ex
                        fromEither x (case c of
                            Env0Args g -> do
                                g () xs x (i,j)
                            Env0Args1Blocks g -> do
                                ([arg0],xs) <- cmd_params 1 xs
                                g (arg0, ()) xs x (i,j)
                            Env1Args g -> do
                                (arg,xs) <- get_1_lbl xs
                                g (arg,()) xs x (i,j)
                            Env2Args g -> do
                                (arg0,arg1,xs) <- get_2_lbl xs
                                g (arg0, arg1) xs x (i,j)
                            Env1Args1Blocks g -> do
                                (arg0,xs) <- get_1_lbl xs
                                ([arg1],xs) <- cmd_params 1 xs
                                g (arg0, arg1) xs x (i,j)
                            Env1Args2Blocks g -> do
                                (arg0,xs) <- get_1_lbl xs
                                ([arg1,arg2],xs) <- cmd_params 2 xs
                                g (arg0, arg1, arg2) xs x (i,j))
                | otherwise = f cs ex e
        f [] ex e@(Env s (i,j) xs _)  = do
               x <- foldl (f blks) ex xs
               g (MRight x) xs
        f _ ex (Bracket _ _ cs _)     = do
               x <- foldl (f blks) ex cs
               g (MRight x) cs
        f _ ex (Text _)               = ex
        g ex (Text xs : ts) = do
            case trim_blanks $ reverse xs of
                Command c (i,j):_   -> h cmds ex c ts (i,j)
                _                   -> g ex ts
        g ex (t : ts) = g ex ts
        g ex [] = ex
        h ((name,c):cs) ex cmd ts (i,j)
            | name == cmd   = do
                    x       <- ex
                    case c of
                        Cmd0Args f -> do
                            x <- fromEither x $ f () x (i,j)
                            g (MRight x) ts
                        Cmd1Args f -> do
                            x <- fromEither x (do
                                (arg,ts) <- get_1_lbl ts
                                f (arg,()) x (i,j))
                            g (MRight x) ts
                        Cmd2Args f -> do
                            x <- fromEither x (do
                                (arg0,arg1,ts) <- get_2_lbl ts
                                f (arg0, arg1) x (i,j))
                            g (MRight x) ts
                        Cmd0Args1Blocks f -> do
                            x <- fromEither x (do
                                ([arg0],ts) <- cmd_params 1 ts
                                f (arg0, ()) x (i,j))
                            g (MRight x) ts
                        Cmd0Args2Blocks f -> do
                            x <- fromEither x (do
                                ([arg0,arg1],ts) <- cmd_params 2 ts
                                f (arg0, arg1) x (i,j))
                            g (MRight x) ts
                        Cmd1Args1Blocks f -> do
                            x <- fromEither x (do
                                (arg0,ts) <- get_1_lbl ts
                                ([arg1],ts) <- cmd_params 1 ts
                                f (arg0, arg1) x (i,j))
                            g (MRight x) ts
                        Cmd1Args2Blocks f -> do
                            x <- fromEither x (do
                                (arg0,ts) <- get_1_lbl ts
                                ([arg1,arg2],ts) <- cmd_params 2 ts
                                f (arg0, arg1, arg2) x (i,j))
                            g (MRight x) ts
                        Cmd2Args1Blocks f -> do
                            x <- fromEither x (do
                                (arg0,arg1,ts) <- get_2_lbl ts
                                ([arg2],ts) <- cmd_params 1 ts
                                f (arg0, arg1, arg2) x (i,j))
                            g (MRight x) ts
                        Cmd2Args2Blocks f -> do
                            x <- fromEither x (do
                                (arg0,arg1,ts) <- get_2_lbl ts
                                ([arg2,arg3],ts) <- cmd_params 2 ts
                                f (arg0, arg1, arg2, arg3) x (i,j))
                            g (MRight x) ts
            | otherwise     = h cs ex cmd ts (i,j)
        h [] ex cmd ts (i,j) = g ex ts 
