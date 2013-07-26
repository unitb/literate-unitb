{-# LANGUAGE ScopedTypeVariables, BangPatterns #-}
module Document.Document where

import Control.Applicative hiding ( empty )
import Control.Monad hiding ( guard )

import Data.Char
import Data.Map hiding ( map, foldl )
import Data.Maybe
import Data.List as L hiding ( union, insert, inits )
import qualified Data.Map as M
import qualified Data.Set as S

import Document.Expression

import Latex.Scanner
import Latex.Parser

import System.IO
import System.IO.Unsafe

import Text.Printf

import UnitB.AST
import UnitB.PO
import UnitB.SetTheory
import UnitB.FunctionTheory
import UnitB.Calculation hiding ( context )
import UnitB.Operator

import Utilities.Format

import Z3.Z3 

--with_print_lbl txt x = unsafePerformIO (do
--        putStrLn ("<< " ++ txt ++ ": " ++ show x ++ " >>")
--        return x)

tex_to_string d = unlines $ concatMap (aux 0) d
    where
        aux n d =
            indent
                (case d of
                    Env s _ c _         -> begin s ++ concatMap (aux (n+1)) c ++ end s
                    Bracket True _ c _  -> ["{"] ++ concatMap (aux (n+1)) c ++ ["}"]
                    Bracket False _ c _ -> ["["] ++ concatMap (aux (n+1)) c ++ ["]"]
                    Text xs             -> lines $ concatMap f $ concatMap lexeme xs)
            where
                indent xs = map (margin ++) xs
                margin  = "|  |"
                begin s = ["begin{" ++ s ++ "}"]
                end s   = ["end{" ++ s ++ "}"]
                f '\n'  = "\\n\n"
                f '\t'  = "\\t"
                f x     = [x]

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

pop_token :: [LatexDoc] -> [LatexDoc]
pop_token (Text (x1:x2:xs):ys) = Text xs:ys
pop_token ((Text [x1]):ys) = ys

list_machines :: String -> Either [Error] [Machine]
list_machines ct = do
        xs <- latex_structure ct
        ms <- all_machines xs
        return $ map snd $ toList $ ms

all_machines :: [LatexDoc] -> Either [Error] (Map String Machine)
all_machines xs = do
        ms <- L.foldl gather (Right empty) xs
--        let !() = unsafePerformIO (putStrLn "checkpoint 1")
        ms <- toEither $ L.foldl (f type_decl) (MRight ms) xs
--        let !() = unsafePerformIO (putStrLn "checkpoint 2")

            -- take actual generic parameter from `type_decl'
        ms <- toEither $ L.foldl (f imports) (MRight ms) xs
--        let !() = unsafePerformIO (putStrLn "checkpoint 3")

            -- take the types from `imports' and `type_decl`
        ms <- toEither $ L.foldl (f declarations) (MRight ms) xs
--        let !() = unsafePerformIO (putStrLn "checkpoint 4")
            
            -- use the `declarations' of variables to check the
            -- type of expressions
        ms <- toEither $ L.foldl (f collect_expr) (MRight ms) xs
--        let !() = unsafePerformIO (putStrLn "checkpoint 5")
            
            -- use the label of expressions from `collect_expr' 
            -- in hints.
        ms <- toEither $ L.foldl (f collect_proofs) (MRight ms) xs
--        let !() = unsafePerformIO (putStrLn "checkpoint 6")
        return ms
    where
        gather em (Env n _ c _)     
                | n == "machine"    = do
                    ms          <- em
                    (name,cont) <- get_1_lbl c
                    let m        = empty_machine name
                    return (insert name m ms)
                | otherwise         = L.foldl gather em c
        gather em x                 = fold_doc gather em x
        f pass em (Env n _ c _)     
                | n == "machine"    = do
                    ms          <- em
                    fromEither ms (do
                        (name,cont) <- get_1_lbl c
                        m           <- toEither $ pass cont (ms ! name)
                        return (insert name m ms))
                | otherwise         = L.foldl (f pass) em c
        f pass em x                 = fold_doc (f pass) em x

context m = step_ctx m

data EnvBlock a = 
        Block0Args (() -> [LatexDoc] -> a -> (Int,Int) -> Either [Error] a)
        | Block1Args ((String, ()) -> [LatexDoc] -> a -> (Int,Int) -> Either [Error] a)
        | Block2Args ((String, String) -> [LatexDoc] -> a -> (Int,Int) -> Either [Error] a)

data CmdBlock a =
        Cmd0Args (() -> a -> (Int,Int) -> Either [Error] a)
        | Cmd1Args ((String,()) -> a -> (Int,Int) -> Either [Error] a)
        | Cmd2Args ((String, String) -> a -> (Int,Int) -> Either [Error] a)

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
                            Block0Args g -> do
                                g () xs x (i,j)
                            Block1Args g -> do
                                (arg,xs) <- get_1_lbl xs
                                g (arg,()) xs x (i,j)
                            Block2Args g -> do
                                (arg0,arg1,xs) <- get_2_lbl xs
                                g (arg0, arg1) xs x (i,j))
                | otherwise = f cs ex e
        f _ ex (Bracket _ _ cs _)  = do
               x <- foldl (f blks) ex cs
               g (MRight x) cs
        f _ ex e       = fold_doc (f blks) ex e
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
            | otherwise     = h cs ex cmd ts (i,j)
        h [] ex cmd ts (i,j) = g ex ts 

type_decl :: [LatexDoc] -> Machine -> MEither Error Machine
type_decl = visit_doc []
            [  (  "\\newset"
               ,  Cmd2Args (\(name, tag) m (i,j) -> do
                    let th = theory m
                    let new_sort = Sort tag name 0
                    let new_type = USER_DEFINED new_sort []
                    toEither $ error_list (i,j)
                        [ ( tag `member` types th
                          , format "a sort with name '{0}' is already declared" tag )
                        , ( tag `member` consts th
                          , format "a constant with name '{0}' is already declared" tag )
                        ]
                    let hd = th 
                            {  types = insert 
                                    tag
                                    new_sort
                                    (types th) 
                            ,  consts = insert tag (Var name $ set_type new_type) $ consts th
                            }
                    return m { theory = hd } )
               )
            ,  (  "\\newevent"
               ,  Cmd1Args (\(evt,()) m (i,j) -> do 
                        let lbl = label evt
                        toEither $ error_list (i,j)
                            [ ( lbl `member` events m
                              , format "event '{0}' is already defined" evt )
                            ]
                        return m { events = insert lbl (empty_event) $ events m } )
               )
            ]

imports :: [LatexDoc] -> Machine -> MEither Error Machine 
imports = visit_doc 
            [ ( "use:set"
              , Block1Args (\(cset,()) _ m (i,j) -> do
                    let th = theory m
                    toEither $ error_list (i,j) 
                        [ ( not (cset `member` types th)
                          , format "Carrier set {0} undefined" cset )
                        ]
                    return m { theory = th {
                                extends = set_theory (USER_DEFINED (types th ! cset) []) : extends th } } )
              )
            , ( "use:fun"
              , Block2Args (\(dset, rset) _ m (i,j) -> do
                    let th = theory m
                    toEither $ error_list (i,j) 
                        [   ( not (dset `member` types th)
                            , format "Carrier set {0} undefined" dset )
                        ,   ( not (rset `member` types th)
                            , format "Carrier set {0} undefined" rset )
                        ]
                    let dtype = USER_DEFINED (types th ! dset) []
                    let rtype = USER_DEFINED (types th ! rset) []
                    return m { theory = th {
                                extends = function_theory dtype rtype : extends th } } )
              )
            ]
            []

    -- Todo: detect when the same variable is declared twice
    -- in the same declaration block.
declarations :: [LatexDoc] -> Machine -> MEither Error Machine
declarations = visit_doc 
        [   (   "variable"
            ,   Block0Args (\() xs m (i,j) -> do
                        vs          <- get_variables (context m) xs
                        let inter = S.fromList (map fst vs) `S.intersection` keysSet (variables m)
                        toEither $ error_list (i,j) 
                            [ ( not $ S.null inter
                              , format "repeated declaration: {0}" (intercalate ", " $ S.toList inter ))
                            ]
                        return m { variables = fromList vs `union` variables m} )
            )
        ,   (   "indices"
            ,   Block1Args (\(evt,()) xs m (i,j) -> do
                        vs <- get_variables (context m) xs
                        toEither $ error_list (i,j)
                            [ ( not (label evt `member` events m) 
                              , format "event '{0}' is undeclared" evt )
                            ]
                        let old_event = events m ! label evt
                        let var_names = map fst vs
                        let inter = S.fromList var_names `S.intersection` keysSet (indices old_event)
                        toEither $ error_list (i,j)
                            [ ( not $ S.null inter
                              , format "repeated declaration: {0}" (intercalate ", " $ S.toList inter ) )
                            ]
                        let new_event = old_event { 
                            indices = fromList vs `union` indices old_event }
                        return m { events = insert (label evt) new_event $ events m } )
            )
        ,   (   "constant"
            ,   Block0Args (\() xs m (i,j) -> do
                        vs              <- get_variables (context m) xs
                        return m { theory = (theory m) { 
                                consts = merge 
                                    (fromListWith (error "repeated definition") vs) 
                                    (consts $ theory m) } } )
            )
        ,   (   "dummy"
            ,   Block0Args (\() xs m (i,j) -> do
                        vs              <- get_variables (context m) xs
                        return m { theory = (theory m) { 
                                dummies = merge 
                                    (fromListWith (error "repeated definition") vs) 
                                    (dummies $ theory m) } } )
            )
        ] 
        []

    -- Todo: report an error if we create two assignments (or other events elements)
    -- with the same name
    -- Todo: guard the `insert` statements with checks for name clashes
    -- Todo: check scopes
collect_expr :: [LatexDoc] -> Machine -> MEither Error Machine
collect_expr = visit_doc 
        [   (   "evassignment"
            ,   Block2Args (\(ev, lbl) xs m li@(i,j) -> do
                        toEither $ error_list (i,j)
                            [ ( not (label ev `member` events m)
                              , format "event '{0}' is undeclared" ev )
                            ]
                        toEither $ error_list (i,j)
                            [ ( label lbl `member` action (events m ! label ev)
                              , format "{0} is already used for another assignment" lbl )
                            ]
                        act <- get_expr m xs
                        let evt       = events m ! label ev
                        let new_event = evt { 
                                    action = insertWith 
                                        (error "name clash")  
                                        (label lbl) act
                                        (action evt) }
                        scope (context m) act (params evt `merge` indices evt) li
                        return m {          
                                events  = insert (label ev) new_event $ events m } ) 
            )
        ,   (   "invariant"
            ,   Block1Args (\(lbl,()) xs m (i,j) -> do
                        toEither $ error_list (i,j)
                            [ ( label lbl `member` inv (props m)
                              , format "{0} is already used for another invariant" lbl )
                            ]
                        invar         <- get_expr m xs
                        return m { 
                            props = (props m) { 
                                inv = insert (label lbl) invar $ inv $ props m } } )
            )
        ,   (   "assumption"
            ,   Block1Args (\(lbl,()) xs m (i,j) -> do
                        let th = theory m
                        toEither $ error_list (i,j)
                            [ ( label lbl `member` fact th
                              , format "{0} is already used for another assertion" lbl )
                            ]
                        axm <- get_expr m xs
                        return m { 
                            theory = th { fact = insert (label lbl) axm $ fact th } } ) 
            )
        ,   (   "initialization"
            ,   Block1Args (\(lbl,()) xs m _ -> do
                        initp         <- get_expr m xs
--                        toEither $ error_list (i,j)
--                            [ ( label lbl `member` inv (props m)
--                              , format "{0} is already used for another invariant" lbl
--                            ]
                        return m {
                                inits = initp : inits m } )
            )
        ,   (   "transient"      
            ,   Block2Args (\(ev, lbl) xs m (i,j) -> do
                        toEither $ error_list (i,j)
                            [ ( not (label ev `member` events m)
                              , format "event '{0}' is undeclared" ev )
                            ]
                        toEither $ error_list (i,j)
                            [   ( label lbl `member` program_prop (props m)
                                , format "{0} is already used for another program property" lbl )
                            ]
                        tr <- get_expr m xs
                        let prop = Transient (free_vars (context m) tr) tr $ label ev
                        let old_prog_prop = program_prop $ props m
                        let new_props     = insert (label lbl) prop $ old_prog_prop
                        return m {
                            props = (props m) {
                                program_prop = new_props } } )
            )
        ,   (   "cschedule"
            ,   Block2Args (\(evt, lbl) xs m li@(i,j) -> do
                        toEither $ error_list (i,j)
                            [ ( not (label evt `member` events m)
                                , format "event '{0}' is undeclared" evt )
                            ]
                        let sc = case c_sched (events m ! label evt) of
                                    Just x  -> x
                                    Nothing -> empty
                        toEither $ error_list (i,j)
                            [ ( label evt `member` sc
                                , format "{0} is already used for another coarse schedule" lbl )
                            ]
                        sched <- get_expr m xs
                        let old_event = events m ! label evt
                        let new_event = old_event { 
                                    c_sched =  
                                        fmap (insert (label lbl) sched) 
                                            ( c_sched old_event <|> Just empty ) }
                        scope (context m) sched (indices old_event) li
                        return m {          
                                events  = insert (label evt) new_event $ events m } )
            )
        ,   (   "fschedule"
            ,   Block2Args (\(evt, lbl) xs m li@(i,j) -> do
                        toEither $ error_list (i,j)
                            [ ( not (label evt `member` events m)
                              , format "event '{0}' is undeclared" evt )
                            ]
                        sched <- get_expr m xs
                        let event = (events m ! label evt) { 
                                    f_sched = Just sched }
                        scope (context m) sched (indices event) li
                        return m {          
                                events  = insert (label evt) event $ events m } )
            )
        ,   (   "constraint"
            ,   Block1Args (\(lbl,()) xs m (i,j) -> do
                        toEither $ error_list (i,j)
                            [ ( label lbl `member` program_prop (props m)
                              , format "{0} is already used for another invariant" lbl )
                            ]
                        pre             <- get_expr m xs
                        return m { 
                            props = (props m) { 
                                program_prop = insert (label lbl) (Co [] pre) 
                                    $ program_prop $ props m } } )
            )
        ] []
    where
        scope :: Context -> Expr -> Map String Var -> (Int,Int) -> Either [Error] ()
        scope ctx xp vs (i,j) = do
            let fv          = keysSet $ free_vars ctx xp
            let decl_v      = keysSet vs
            let undecl_v    = S.toList (fv `S.difference` decl_v)
            if fv `S.isSubsetOf` decl_v
            then return ()
            else Left [(format "Undeclared variables: {0}" (intercalate ", " undecl_v), i,j)]

collect_proofs :: [LatexDoc] -> Machine -> MEither Error Machine
collect_proofs xs m = visit_doc
        [   (   "proof"
            ,   Block1Args (\(po,()) xs m (i,j) -> do
                    mproofs     <- foldl g (Right []) xs
                    case mproofs of
                        [p] -> return m { 
                            props = (props m) { 
                                proofs = insert (composite_label 
                                    [ _name m, label po ]) p $ 
                                      proofs $ props m } }
                        _   -> Left [("expecting a single calculation",i,j)]         )
            )
        ] [] xs m
    where
        g mxs (Env n (i,j) c _)
            | n == "calculation"    = do
                xs <- mxs
                cc <- toEither $ calc c (i,j)
                case infer_goal cc of
                    Right cc_goal -> return (cc { goal = cc_goal }:xs)
                    Left msg      -> Left [(format "type error: {0}" msg,i,j)]
            | otherwise             = foldl g mxs c
        g xs x                      = fold_doc g xs x
        calc xs li = 
            case find_cmd_arg 2 ["\\hint"] xs of
                Just (a,t,[b,c],d)    -> do
                    xp <- fromEither ztrue $ get_expr m a
                    op <- fromEither Equal $ read_tokens 
                            (do eat_space ; x <- oper ; eat_space ; return x) 
                            (concatMap flatten_li b)
                    hyp <- fromEither [] (do
                        hs <- fmap (map (\(x,y) -> (label x,y))) $ hint c
                        mapM find hs)
                    r   <- calc d li
                    return r { 
                        first_step = xp,
                        following  = (op,first_step r,hyp,line_info t):following r }
                Nothing         -> do
                    xp <- fromEither ztrue $ get_expr m xs
                    return $ Calc (context m) ztrue xp [] li
            where
                f x = composite_label [_name m,label x]
        hint xs =
            case find_cmd_arg 1 ["\\ref","\\eqref"] xs of
                Just (a,_,[[Text [TextBlock b li]]],c)  -> do
                    xs <- hint c
                    return ((b,li):xs)
                Nothing         -> return []
        find :: (Label,(Int,Int)) -> Either [Error] Expr
        find (xs,(i,j)) = either Right Left (do
                err $ M.lookup xs $ inv p
                err $ M.lookup xs $ inv_thm p
                foldM f [err_msg] $ elems $ events m
                )
            where
                p = props m
                err (Just x) = Left x
                err Nothing  = Right [err_msg]
                err_msg      = ("reference to unknown predicate",i,j)
                f :: [Error] -> Event -> Either Expr [Error]
                f _ ev = do
                    err (do
                        x <- c_sched ev
                        M.lookup xs x)
                    err $ M.lookup xs $ guard ev
                    err $ M.lookup xs $ action ev
                                

get_expr :: Machine -> [LatexDoc] -> Either [Error] Expr
get_expr m xs =
        parse_expr (context m) (concatMap flatten_li xs)

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

--with_print_latex x = 
--    unsafePerformIO (do
--        putStrLn (tex_to_string x)
--        return x)

parse_machine :: FilePath -> IO (Either [Error] [Machine])
parse_machine fn = do
        ct <- readFile fn
        return $ list_machines ct
        