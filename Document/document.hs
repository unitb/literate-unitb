{-# LANGUAGE BangPatterns, ScopedTypeVariables #-}
module Document.Document where

import Control.Applicative hiding ( empty )
import Control.Monad hiding ( guard )

import Data.Char
import Data.Map hiding ( map, foldl )
import Data.Maybe
import Data.List as L hiding ( union, insert, inits )
import qualified Data.Map as M
import qualified Data.Set as S
--import Data.Set as S

import Document.Expression

import Latex.Scanner
import Latex.Parser

import System.IO
import System.IO.Unsafe

import Text.Printf

import UnitB.AST
import UnitB.PO
import UnitB.SetTheory
import UnitB.Calculation hiding ( context )

import Utilities.Format

-- import Text.LaTeX.Base.Syntax

import Z3.Z3 -- hiding ( context )

with_print_lbl txt x = unsafePerformIO (do
        putStrLn ("<< " ++ txt ++ ": " ++ show x ++ " >>")
        return x)

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

cmd_params :: Int -> [LatexDoc] -> Either Error ([[LatexDoc]], [LatexDoc])
cmd_params 0 xs     = Right ([], xs)
cmd_params n xs     = 
        case drop_blank_text xs of
            Bracket _ _ xs _ : ys -> do
                (ws, zs) <- cmd_params (n-1) ys
                Right (xs:ws, zs)
            x                 -> Left ("bad argument: " ++ show xs,-1,-1)

cmd_params_ n xs = fmap fst $ cmd_params n xs

pop_token :: [LatexDoc] -> [LatexDoc]
pop_token (Text (x1:x2:xs):ys) = Text xs:ys
pop_token ((Text [x1]):ys) = ys

all_machines :: [LatexDoc] -> Either Error (Map String Machine)
all_machines xs = do
        ms <- L.foldl gather (Right empty) xs
        ms <- L.foldl (f type_decl) (Right ms) xs
        ms <- L.foldl (f imports) (Right ms) xs
        ms <- L.foldl (f declarations) (Right ms) xs
        ms <- L.foldl (f build_machine) (Right ms) xs
        ms <- L.foldl (f collect_proofs) (Right ms) xs
        return ms
--        return ms1
    where
        first_pass cont m = declarations cont m
        sec_pass cont m   = build_machine cont m
        third_pass cont m = collect_proofs cont m
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
                    (name,cont) <- get_1_lbl c
                    m           <- pass cont (ms ! name)
                    return (insert name m ms)
                | otherwise         = L.foldl (f pass) em c
        f pass em x                 = fold_doc (f pass) em x

--merge_event :: Event -> Event -> Event
--merge_event e@(Event ind0 c0 f0 p0 g0 a0) (Event ind1 c1 f1 p1 g1 a1) = 
--        Event (ind0 `merge` ind1) c2 f2 (p0 `merge` p1) (g0`union`g1) (a0`union`a1)
--    where
--        c2 = case maybeToList c0 ++ maybeToList c1 of
--                [x,y] -> Just (x `union` y)
--                [x]   -> Just x
--                []    -> Nothing
--        f2 = case group (maybeToList f0 ++ maybeToList f1) of
--                [[x],[y]] -> Nothing
--                [x:_]     -> Just x
--                []        -> Nothing

context m = step_ctx m

data EnvBlock a = 
        Block0Args ([LatexDoc] -> a -> (Int,Int) -> Either Error a)
        | Block1Args (String -> [LatexDoc] -> a -> (Int,Int) -> Either Error a)
        | Block2Args (String -> String -> [LatexDoc] -> a -> (Int,Int) -> Either Error a)

data CmdBlock a =
        Cmd0Args (a -> (Int,Int) -> Either Error a)
        | Cmd1Args (String -> a -> (Int,Int) -> Either Error a)
        | Cmd2Args (String -> String -> a -> (Int,Int) -> Either Error a)

visit_doc :: [(String,EnvBlock a)] -> [(String,CmdBlock a)] -> [LatexDoc] -> a -> Either Error a
visit_doc blks cmds cs x = do
        x <- foldl (f blks) (Right x) cs
        g (Right x) cs
    where
        f ((name,c):cs) ex e@(Env s (i,j) xs _)
                | name == s = do
                        x <- ex
                        case c of
                            Block0Args g -> do
                                g xs x (i,j)
                            Block1Args g -> do
                                (arg,xs) <- get_1_lbl xs
                                g arg xs x (i,j)
                            Block2Args g -> do
                                (arg0,arg1,xs) <- get_2_lbl xs
                                g arg0 arg1 xs x (i,j)
                | otherwise = f cs ex e
        f _ ex (Bracket _ _ cs _)  = do
                x <- foldl (f blks) ex cs
                g (Right x) cs
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
                            x <- f x (i,j)
                            g (Right x) ts
                        Cmd1Args f -> do
                            (arg,ts) <- get_1_lbl ts
                            x <- f arg x (i,j)
                            g (Right x) ts
                        Cmd2Args f -> do
                            (arg0,arg1,ts) <- get_2_lbl ts
                            x <- f arg0 arg1 x (i,j)
                            g (Right x) ts
            | otherwise     = h cs ex cmd ts (i,j)
        h [] ex cmd ts (i,j) = g ex ts 

type_decl :: [LatexDoc] -> Machine -> Either Error Machine
type_decl = visit_doc []
            [  (  "\\newset"
               ,  Cmd2Args (\name tag m (i,j) -> do
                    let th = theory m
                    let new_sort = Sort tag name 0
                    let new_type = USER_DEFINED new_sort []
                    when (tag `member` types th) $
                        Left (format "a sort with name '{0}' is already declared" tag,i,j)
                    when (tag `member` consts th) $
                        Left (format "a constant with name '{0}' is already declared" tag,i,j)
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
               ,  Cmd1Args (\evt m (i,j) -> do 
                        let lbl = label evt
                        if lbl `member` events m
                            then Left (format "event '{0}' is already defined" evt, i, j)
                            else Right m { events = insert lbl (empty_event) $ events m } )
               )
            ]
--type_decl cs m = g (Right m) cs
--    where
--        f em e@(Env s _ xs _)       = g em xs
--        f em (Bracket _ _ xs _)     = g em xs
--        f em (Text _)               = em
--        g :: Either Error Machine -> [LatexDoc] -> Either Error Machine
--        g em xs = m2
--            where
--                m0 = foldl f em xs 
--                m1 = foldl h0 m0 (zip3 xs (drop 1 xs) $ drop 2 xs )
--                m2 = foldl h1 m1 (zip xs $ drop 1 xs)
--        h0 :: Either Error Machine
--             -> (LatexDoc,LatexDoc,LatexDoc) 
--             -> Either Error Machine
--        h0 em (
--                Text xs, 
--                Bracket _ _ [Text [TextBlock ys _]] _, 
--                Bracket _ _ [Text [zs]] _) =
--            case reverse $ trim_blanks xs of
--                Command "\\newset" (i,j):_ -> do
--                    m   <- em
--                    let th = theory m
--                    let hd = th { types = insert 
--                                    (lexeme zs) 
--                                    (Sort (lexeme zs) ys 0) 
--                                    (types th) }
--                    if ys `member` types th 
--                        then Left (format "set '{0}' is already defined" ys, i, j)
--                        else Right m { theory = hd }
--                _ -> em
--        h0 em _ = em
--
--        h1 :: Either Error Machine -> (LatexDoc,LatexDoc) -> Either Error Machine
--        h1 em (Text xs, Bracket _ _ [Text [TextBlock ys _]] _) =
--            case reverse $ trim_blanks xs of
--                Command "\\newevent" (i,j):_ -> do
--                    m   <- em
--                    let lbl = label ys
--                    if lbl `member` events m
--                        then Left ("event '" ++ ys ++ "' is already defined", i, j)
--                        else Right m { events = insert lbl (empty_event) $ events m }
--                _ -> em
--        h1 em _ = em

--ferror 

imports :: [LatexDoc] -> Machine -> Either Error Machine 
imports = visit_doc 
            [ ( "use:set"
              , Block1Args (\cset _ m (i,j) -> do
                    let th = theory m
                    case M.lookup cset $ types th of
                            Just s -> return m { theory = th {
                                extends = set_theory (USER_DEFINED s []) : extends th } }
                            Nothing -> Left (format "Carrier set {0} undefined" cset,i,j) )
              )
            ]
            []

--imports cs m = foldl f (Right $ m) cs
--    where
--        f em e@(Env s (i,j) xs _)
--                | s == "use:set"        = do
--                        m               <- em 
--                        (cset, _)       <- get_1_lbl xs
--                        let th = theory m
--                        case M.lookup cset $ types th of
--                            Just s -> return m { theory = th {
--                                extends = set_theory (USER_DEFINED s []) : extends th } }
--                            Nothing -> Left (format "Carrier set {0} undefined" cset,i,j)
--                | otherwise             = foldl f em xs
--        f em x     = fold_doc f em x
    


declarations :: [LatexDoc] -> Machine -> Either Error Machine
declarations = visit_doc 
        [   (   "variable"
            ,   Block0Args (\xs m (i,j) -> do
                        vs          <- get_variables (context m) xs
                        return m { variables = fromList vs `union` variables m} )
            )
        ,   (   "indices"
            ,   Block1Args (\evt xs m (i,j) -> do
                        vs          <- get_variables (context m) xs
                        unless (label evt `member` events m) (
                            Left ("event '" ++ evt ++ "' is undeclared",i,j))
                        let old_event = events m ! label evt
                        let new_event = old_event { 
                            indices = fromList vs `union` indices old_event }
                        return m { events = insert (label evt) new_event $ events m } )
            )
        ,   (   "constant"
            ,   Block0Args (\xs m (i,j) -> do
                        vs              <- get_variables (context m) xs
                        return m { theory = (theory m) { 
                                consts = merge 
                                    (fromListWith (error "repeated definition") vs) 
                                    (consts $ theory m) } } )
            )
        ,   (   "dummy"
            ,   Block0Args (\xs m (i,j) -> do
                        vs              <- get_variables (context m) xs
                        return m { theory = (theory m) { 
                                dummies = merge 
                                    (fromListWith (error "repeated definition") vs) 
                                    (dummies $ theory m) } } )
            )
        ] 
        []
--declarations cs m = g (Right m) cs
--    where
--        f em e@(Env s li@(i,j) xs _) 
--                | s == "variable"   = do
--                        m           <- em
--                        vs          <- get_variables (context m) xs
--                        return m { variables = fromList vs `union` variables m}
--                | s == "indices"   = do
--                        m           <- em
--                        (evt,rest)  <- get_1_lbl xs
--                        vs          <- get_variables (context m) rest
--                        unless (label evt `member` events m) (
--                            Left ("event '" ++ evt ++ "' is undeclared",i,j))
--                        let old_event = events m ! label evt
--                        let new_event = old_event { 
--                            indices = fromList vs `union` indices old_event }
--                        return m { events = insert (label evt) new_event $ events m }
--                | s == "dummy"          = do
--                        m               <- em
--                        vs              <- get_variables (context m) xs
--                        return m { theory = (theory m) { 
--                                dummies = merge 
--                                    (fromListWith (error "repeated definition") vs) 
--                                    (dummies $ theory m) } }
--                | otherwise         = foldl f em xs
--        f em (Bracket _ _ xs _)     = g em xs
--        f em (Text _)               = em
--        g :: Either Error Machine -> [LatexDoc] -> Either Error Machine
--        g em xs = foldl f em xs

        
    -- Todo: report an error if we create assignments (or other events elements)
    -- for events that are not declared.
build_machine :: [LatexDoc] -> Machine -> Either (String,Int,Int) Machine
build_machine = visit_doc 
        [   (   "evassignment"
            ,   Block2Args (\ev lbl xs m li@(i,j) -> do
                        act             <- get_expr m xs
                        unless (label ev `member` events m) (
                            Left (format "event '{0}' is undeclared" ev,i,j))
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
            ,   Block1Args (\lbl xs m (i,j) -> do
                        invar         <- get_expr m xs
                        return m { 
                            props = (props m) { 
                                inv = insert (label lbl) invar $ inv $ props m } } )
            )
        ,   (   "assumption"
            ,   Block1Args (\lbl xs m (i,j) -> do
                        axm             <- get_expr m xs
                        let th = theory m
                        when (label lbl `member` fact th) $ Left (format "{0} is already used for another assertion" lbl,i,j)
                        return m { 
                            theory = th { fact = insert (label lbl) axm $ fact th } } )
            )
        ,   (   "initialization"
            ,   Block1Args (\lbl xs m _ -> do
                        initp         <- get_expr m xs
                        return m {
                                inits = initp : inits m } )
            )
        ,   (   "transient"      
            ,   Block2Args (\ev lbl xs m (i,j) -> do
                        tr            <- get_expr m xs
                        unless (label ev `member` events m) (
                            Left (format "event '{0}' is undeclared" ev,i,j))
                        let prop = Transient (free_vars (context m) tr) tr $ label ev
                        let old_prog_prop = program_prop $ props m
                        let new_props     = insert (label lbl) prop $ old_prog_prop
                        return m {
                            props = (props m) {
                                program_prop = new_props } } )
            )
        ,   (   "cschedule"
            ,   Block2Args (\evt lbl xs m li@(i,j) -> do
                        sched          <- get_expr m xs
                        unless (label evt `member` events m) (
                            Left (format "event '{0}' is undeclared" evt,i,j))
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
            ,   Block2Args (\evt lbl xs m li@(i,j) -> do
                        sched          <- get_expr m xs
                        unless (label evt `member` events m) (
                            Left (format "event '{0}' is undeclared" evt,i,j))
                        let event = (events m ! label evt) { 
                                    f_sched = Just sched }
                        scope (context m) sched (indices event) li
                        return m {          
                                events  = insert (label evt) event $ events m } )
            )
        ,   (   "constraint"
            ,   Block1Args (\lbl xs m _ -> do
                        pre             <- get_expr m xs
                        return m { 
                            props = (props m) { 
                                program_prop = insert (label lbl) (Co [] pre) 
                                    $ program_prop $ props m } } )
            )
        ] []
--build_machine cs m = foldl f (Right $ m) cs
--    where
--        f em e@(Env s li@(i,j) xs _) 
--                | s == "evassignment"   = do
--                        m               <- em
--                        (ev,lbl,rest)   <- get_2_lbl xs
--                        act             <- get_expr m rest
----            return $ singleton (label a) $ empty_event { action = singleton (label b) 
----                        act           <- as_action (context m) xs
----                        return m { events = unionWith merge_event act
----                                        $ events m } 
--                        unless (label ev `member` events m) (
--                            Left ("event '" ++ ev ++ "' is undeclared",i,j))
--                        let evt       = events m ! label ev
--                        let new_event = evt { 
--                                    action = insertWith 
--                                        (error "name class")  
--                                        (label lbl) act
--                                        (action evt) }
----                                    c_sched =  
----                                        fmap ( c_sched evt <|> Just empty }
--                        scope (context m) act (params evt `merge` indices evt) li
--                        return m {          
--                                events  = insert (label ev) new_event $ events m }
--                | s == "invariant"      = do
--                        m             <- em
--                        (lbl,rest)    <- get_1_lbl xs
--                        invar         <- get_expr m rest
--                        return m { 
--                            props = (props m) { 
--                                inv = insert (label lbl) invar $ inv $ props m } }
--                | s == "initialization" = do
--                        m             <- em
--                        (lbl,rest)    <- get_1_lbl xs
--                        initp         <- get_expr m rest
--                        return m {
--                                inits = initp : inits m }
--                | s == "transient"      = do
--                        m             <- em
--                        (ev,lbl,rest) <- get_2_lbl xs
--                        tr            <- get_expr m rest
--                        unless (label ev `member` events m) (
--                            Left (format "event '{0}' is undeclared" ev,i,j))
--                        let prop = Transient (free_vars (context m) tr) tr $ label ev
--                        let old_prog_prop = program_prop $ props m
--                        let new_props     = insert (label lbl) prop $ old_prog_prop
--                        return m {
--                            props = (props m) {
--                                program_prop = new_props } }
--                | s == "cschedule"     = do
--                        m              <- em
--                        (evt,lbl,rest) <- get_2_lbl xs
--                        sched          <- get_expr m rest
--                        unless (label evt `member` events m) (
--                            Left (format "event '{0}' is undeclared" evt,i,j))
--                        let old_event = events m ! label evt
--                        let new_event = old_event { 
--                                    c_sched =  
--                                        fmap (insert (label lbl) sched) 
--                                            ( c_sched old_event <|> Just empty ) }
----                        let event = singleton (label evt) 
----                                (empty_event { 
----                                    c_sched = Just $ singleton (label lbl) sched })
----                        return m {          
----                                events  = unionWith merge_event event $ events m }
----                        let event = (events m ! label lbl) { 
----                                    c_sched = Just $ singleton (label lbl) sched }
--                        scope (context m) sched (indices old_event) li
--                        return m {          
--                                events  = insert (label evt) new_event $ events m }
--                | s == "fschedule"     = do
--                        m              <- em
--                        (evt,lbl,rest) <- get_2_lbl xs
--                        sched          <- get_expr m rest
--                        unless (label evt `member` events m) (
--                            Left (format "event '{0}' is undeclared" evt,i,j))
--                        let event = (events m ! label evt) { 
--                                    f_sched = Just sched }
--                        scope (context m) sched (indices event) li
--                        return m {          
--                                events  = insert (label evt) event $ events m }
--                | s == "constraint"     = do
--                        m               <- em
--                        (lbl,rest)      <- get_1_lbl xs
--                        pre             <- get_expr m rest
--                        return m { 
--                            props = (props m) { 
--                                program_prop = insert (label lbl) (Co [] pre) 
--                                    $ program_prop $ props m } }
--                | otherwise             = foldl f em xs
--        f em x     = fold_doc f em x
    where
        scope :: Context -> Expr -> Map String Var -> (Int,Int) -> Either Error ()
        scope ctx xp vs (i,j) = do
            let fv          = keysSet $ free_vars ctx xp
            let decl_v      = keysSet vs
            let undecl_v    = S.toList (fv `S.difference` decl_v)
            if fv `S.isSubsetOf` decl_v
            then return ()
            else Left (format "Undeclared variables: {0}" (intercalate ", " undecl_v), i,j)
        

get_expr :: Machine -> [LatexDoc] -> Either Error Expr
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
find_cmd_arg _ cmd []     = Nothing

collect_proofs :: [LatexDoc] -> Machine -> Either (String,Int,Int) Machine
collect_proofs xs m = visit_doc
        [   (   "proof"
            ,   Block1Args (\po xs m (i,j) -> do
                    mproofs     <- foldl g (Right []) xs
                    case mproofs of
                        [p] -> return m { 
                            props = (props m) { 
                                proofs = insert (composite_label 
                                    [ _name m, label po ]) p $ 
                                      proofs $ props m } }
                        _   -> Left ("expecting a single calculation",i,j)         )
            )
        ] [] xs m
    where
--collect_proofs cs m = foldl f (Right m) cs --  error "not implemented" 
--    where
--        f em (Env n (i,j) c _)
--            | n == "proof"  = do
--                    m           <- em
--                    (po,rest)   <- get_1_lbl c
--                    mproofs     <- foldl g (Right []) rest
--                    case mproofs of
--                        [p] -> return m { 
--                            props = (props m) { 
--                                proofs = insert (composite_label 
--                                    [ _name m, label po ]) p $ 
--                                      proofs $ props m } }
--                        _   -> Left ("expecting a single calculation",i,j)
--            | otherwise     = foldl f em c
--        f em x              = fold_doc f em x
        g mxs (Env n (i,j) c _)
            | n == "calculation"    = do
                xs <- mxs
                cc <- calc c (i,j)
                case infer_goal cc of
                    Just cc_goal -> return (cc { goal = cc_goal }:xs)
                    Nothing      -> Left ("type error",i,j)
            | otherwise             = foldl g mxs c
        g xs x                      = fold_doc g xs x
        calc xs li = 
            case find_cmd_arg 2 ["\\hint"] xs of
                Just (a,t,[b,c],d)    -> do
                    xp <- get_expr m a
                    op <- read_tokens 
                            (do eat_space ; x <- oper ; eat_space ; return x) 
                            (concatMap flatten_li b)
                    hs  <- fmap (map (\(x,y) -> (label x,y))) $ hint c
                    hyp <- mapM find hs
                    r   <- calc d li
                    return r { 
                        first_step = xp,
                        following  = (op,first_step r,hyp,line_info t):following r }
                Nothing         -> do
                    xp <- get_expr m xs
                    return $ Calc (context m) ztrue xp [] li
            where
                f x = composite_label [_name m,label x]
        hint xs =
            case find_cmd_arg 1 ["\\ref","\\eqref"] xs of
                Just (a,_,[[Text [TextBlock b li]]],c)  -> do
                    xs <- hint c
                    return ((b,li):xs)
                Nothing         -> return []
        find :: (Label,(Int,Int)) -> Either Error Expr
        find (xs,(i,j)) = either Right Left (do
                err $ M.lookup xs $ inv p
                err $ M.lookup xs $ inv_thm p
                foldM f err_msg $ elems $ events m
                )
            where
                p = props m
                err (Just x) = Left x
                err Nothing  = Right err_msg
                err_msg      = ("reference to unknown predicate",i,j)
                f :: Error -> Event -> Either Expr Error
                f _ ev = do
                    err (do
                        x <- c_sched ev
                        M.lookup xs x)
                    err $ M.lookup xs $ guard ev
                    err $ M.lookup xs $ action ev
                        

get_1_lbl :: [LatexDoc] -> Either Error (String, [LatexDoc])
get_1_lbl xs = do -- Right ("", xs)
        ([x],z) <- cmd_params 1 xs
        case trim_blank_text x of
            ([Text [TextBlock x _]]) 
                -> Right (x,z)
            ([Text [Command x _]]) 
                -> Right (x,z)
            _   -> err_msg (line_info xs)
    where
        err_msg (i,j) = Left  ("expecting a label",i,j)
        
get_2_lbl :: [LatexDoc] -> Either Error (String, String, [LatexDoc])
get_2_lbl xs = do
        (lbl0,xs) <- get_1_lbl xs
        (lbl1,xs) <- get_1_lbl xs
        return (lbl0,lbl1,xs)

with_print_latex x = 
    unsafePerformIO (do
        putStrLn (tex_to_string x)
        return x)

parse_machine :: FilePath -> IO (Either Error [Machine])
parse_machine fn = do
        ct <- readFile fn
        let r = do 
            xs <- latex_structure ct
            r <- all_machines xs
            return $ map snd $ toList $ r
        return r
        