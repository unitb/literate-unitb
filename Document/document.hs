module Document.Document where
{-# LANGUAGE BangPatterns #-}

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

import UnitB.AST
import UnitB.PO

import System.IO
import System.IO.Unsafe

-- import Text.LaTeX.Base.Syntax

import Z3.Z3 hiding ( context )
import Z3.Calculation hiding ( context )
import Z3.Const
import Z3.Def

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

--sections = [
--    "machine"]
--
--extract_structure ct = do
--        xs <- latex_structure ct
--        return (find_env sections xs)
--    where
--        open (Env _ _ c _) = c
--        cont (Text xs _) = xs

--get_name 

drop_blank_text :: [LatexDoc] -> [LatexDoc]
drop_blank_text ( Text [Blank _ _] : ys ) = drop_blank_text ys
drop_blank_text ( Text (Blank _ _ : xs) : ys ) = drop_blank_text ( Text xs : ys )
drop_blank_text xs = xs

trim_blank_text xs = reverse $ drop_blank_text $ reverse $ drop_blank_text xs

skip_blanks :: [LatexToken] -> [LatexToken]
skip_blanks (Blank _ _ : xs) = xs
skip_blanks xs = xs 

trim_blanks :: [LatexToken] -> [LatexToken]
trim_blanks xs = reverse $ skip_blanks $ reverse $ skip_blanks xs

event_lbl = "\\newevent"
var_env = "variable"
act_env = "ev:assignment"

cmds = [ event_lbl ]
envs = [ var_env, act_env ]

cmd_params :: Int -> [LatexDoc] -> Either Error ([[LatexDoc]], [LatexDoc])
cmd_params 0 xs     = Right ([], xs)
cmd_params n xs     = 
        case drop_blank_text xs of
            Bracket _ _ xs _ : ys -> do
                (ws, zs) <- cmd_params (n-1) ys
                Right (xs:ws, zs)
            x                 -> Left ("bad argument: " ++ show xs,-1,-1)

cmd_params_ n xs = fmap fst $ cmd_params n xs

--as_event :: [LatexDoc] -> (Label, Event)
--as_event xs = (label name, empty_event)
--    where
--        ys   = pop_token xs
--        name = case map trim_blank_text $ cmd_params_ 1 ys of
--                [ [Text [(TextBlock xs) _ _]] ] -> xs
--                _             -> error "bad name"

--with_print x = 
--        unsafePerformIO (do
--            print x
--            return x)

pop_token :: [LatexDoc] -> [LatexDoc]
pop_token (Text (x1:x2:xs):ys) = Text xs:ys
pop_token ((Text [x1]):ys) = ys

--oper :: Context -> Scanner Char ((Expr -> Expr -> Expr), Int)
--oper ctx = match_first [
--              ( match_string "+", \_ -> return (zplus, 1)),
--              ( match_string "=", \_ -> return (zeq, 2)) ]
--            (fail "invalid operator")

--as_action :: Context -> [LatexDoc] -> Either Error (Map Label Event) 
--as_action ctx c = do
--            (a,b,xs) <- get_2_lbl c
--            e        <- parse_expr ctx (concatMap flatten_li xs)
--            return $ singleton (label a) $ empty_event { action = singleton (label b) e }
--    where
--        get_labels = do
--            kk <- cmd_params 2 c
--            case kk of
--                ([  [Text [TextBlock a _]], 
--                    [Text [TextBlock b _]]],xs) -> 
--                    return (a,b,xs)
--                _                                        -> 
--                    Left ("invalid assignment names", -1, -1)

all_machines :: [LatexDoc] -> Either Error (Map String Machine)
all_machines xs = do
        ms <- L.foldl gather (Right empty) xs
        ms <- L.foldl (f type_decl) (Right ms) xs
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

merge_event :: Event -> Event -> Event
merge_event e@(Event ind0 c0 f0 p0 g0 a0) (Event ind1 c1 f1 p1 g1 a1) = 
        Event (ind0 `merge` ind1) c2 f2 (p0 `merge` p1) (g0`union`g1) (a0`union`a1)
    where
        c2 = case maybeToList c0 ++ maybeToList c1 of
                [x,y] -> Just (x `union` y)
                [x]   -> Just x
                []    -> Nothing
        f2 = case group (maybeToList f0 ++ maybeToList f1) of
                [[x],[y]] -> Nothing -- Just (x `zand` y)
                [x:_]     -> Just x
                []        -> Nothing

--merge_machine :: Machine -> Machine -> Machine
--merge_machine (Mch n t0 v0 i0 ev0 p0) (Mch _ t1 v1 i1 ev1 p1) =
--        Mch n (t0 ++ t1) 
--            (v0 `union` v1) (i0++i1) 
--            (unionWith merge_event ev0 ev1)
--            (p0 `ps_union` p1)

context m = step_ctx m -- Context (variables m) empty empty     

type_decl :: [LatexDoc] -> Machine -> Either Error Machine
type_decl cs m = g (Right m) cs
    where
        f em e@(Env s _ xs _)       = g em xs
        f em (Bracket _ _ xs _)     = g em xs
        f em (Text _)               = em
        g :: Either Error Machine -> [LatexDoc] -> Either Error Machine
        g em xs = m2
            where
                m0 = foldl f em xs 
                m1 = foldl h0 m0 (zip3 xs (drop 1 xs) $ drop 2 xs )
                m2 = foldl h1 m1 (zip xs $ drop 1 xs)
        h0 :: Either Error Machine
             -> (LatexDoc,LatexDoc,LatexDoc) 
             -> Either Error Machine
        h0 em (
                Text xs, 
                Bracket _ _ [Text [TextBlock ys _]] _, 
                Bracket _ _ [Text [zs]] _) =
            case reverse $ trim_blanks xs of
                Command "\\newset" (i,j):_ -> do
                    m   <- em
                    let th = theory m
                    let hd = th { types = insert 
                                    (lexeme zs) 
                                    (Sort (lexeme zs) ys) 
                                    (types th) }
                    if ys `member` types th 
                        then Left ("set '" ++ ys ++ "' is already defined", i, j)
                        else Right m { theory = hd }
                _ -> em
        h0 em _ = em

        h1 :: Either Error Machine -> (LatexDoc,LatexDoc) -> Either Error Machine
        h1 em (Text xs, Bracket _ _ [Text [TextBlock ys _]] _) =
            case reverse $ trim_blanks xs of
                Command "\\newevent" (i,j):_ -> do
                    m   <- em
                    let lbl = label ys
                    if lbl `member` events m
                        then Left ("event '" ++ ys ++ "' is already defined", i, j)
                        else Right m { events = insert lbl (empty_event) $ events m }
                _ -> em
        h1 em _ = em


declarations :: [LatexDoc] -> Machine -> Either Error Machine
declarations cs m = g (Right m) cs
    where
        f em e@(Env s _ xs _) 
                | s == "variable"   = do
                        m           <- em
                        vs          <- get_variables (context m) xs
                        return m { variables = fromList vs `union` variables m}
                | s == "indices"   = do
                        m           <- em
                        (evt,rest)  <- get_1_lbl xs
                        vs          <- get_variables (context m) rest
                        let old_event = events m ! label evt
                        let new_event = old_event { 
                            indices = fromList vs `union` indices old_event }
                        return m { events = insert (label evt) new_event $ events m }
                | s == "dummy"          = do
                        m               <- em
                        vs              <- get_variables (context m) xs
                        return m { theory = (theory m) { 
                                dummies = merge 
                                    (fromListWith (error "repeated definition") vs) 
                                    (dummies $ theory m) } }
                | otherwise         = foldl f em xs
        f em (Bracket _ _ xs _)     = g em xs
        f em (Text _)               = em
        g :: Either Error Machine -> [LatexDoc] -> Either Error Machine
        g em xs = foldl f em xs

        
    -- Todo: report an error if we create assignments (or other events elements)
    -- for events that are not declared.
build_machine :: [LatexDoc] -> Machine -> Either (String,Int,Int) Machine
build_machine cs m = foldl f (Right $ m) cs
    where
        f em e@(Env s li xs _) 
                | s == "evassignment"   = do
                        m               <- em
                        (ev,lbl,rest)   <- get_2_lbl xs
                        act             <- get_expr m rest
--            return $ singleton (label a) $ empty_event { action = singleton (label b) 
--                        act           <- as_action (context m) xs
--                        return m { events = unionWith merge_event act
--                                        $ events m } 
                        let evt       = events m ! label ev
                        let new_event = evt { 
                                    action = insertWith 
                                        (error "name class")  
                                        (label lbl) act
                                        (action evt) }
--                                    c_sched =  
--                                        fmap ( c_sched evt <|> Just empty }
                        scope (context m) act (params evt `merge` indices evt) li
                        return m {          
                                events  = insert (label ev) new_event $ events m }
                | s == "invariant"      = do
                        m             <- em
                        (lbl,rest)    <- get_1_lbl xs
                        invar         <- get_expr m rest
                        return m { 
                            props = (props m) { 
                                inv = insert (label lbl) invar $ inv $ props m } }
                | s == "initialization" = do
                        m             <- em
                        (lbl,rest)    <- get_1_lbl xs
                        initp         <- get_expr m rest
                        return m {
                                inits = initp : inits m }
                | s == "transient"      = do
                        m             <- em
                        (ev,lbl,rest) <- get_2_lbl xs
                        tr            <- get_expr m rest
                        let prop = Transient (free_vars (context m) tr) tr $ label ev
                        let old_prog_prop = program_prop $ props m
                        let new_props     = insert (label lbl) prop $ old_prog_prop
                        return m {
                            props = (props m) {
                                program_prop = new_props } }
                | s == "cschedule"     = do
                        m              <- em
                        (evt,lbl,rest) <- get_2_lbl xs
                        sched          <- get_expr m rest
                        let old_event = events m ! label evt
                        let new_event = old_event { 
                                    c_sched =  
                                        fmap (insert (label lbl) sched) 
                                            ( c_sched old_event <|> Just empty ) }
--                        let event = singleton (label evt) 
--                                (empty_event { 
--                                    c_sched = Just $ singleton (label lbl) sched })
--                        return m {          
--                                events  = unionWith merge_event event $ events m }
--                        let event = (events m ! label lbl) { 
--                                    c_sched = Just $ singleton (label lbl) sched }
                        scope (context m) sched (indices old_event) li
                        return m {          
                                events  = insert (label evt) new_event $ events m }
                | s == "fschedule"     = do
                        m              <- em
                        (evt,lbl,rest) <- get_2_lbl xs
                        sched          <- get_expr m rest
                        let event = (events m ! label evt) { 
                                    f_sched = Just sched }
                        scope (context m) sched (indices event) li
                        return m {          
                                events  = insert (label evt) event $ events m }
                | s == "constraint"     = do
                        m               <- em
                        (lbl,rest)      <- get_1_lbl xs
                        pre             <- get_expr m rest
                        return m { 
                            props = (props m) { 
                                program_prop = insert (label lbl) (Co [] pre) 
                                    $ program_prop $ props m } }
                | otherwise             = foldl f em xs
        f em x     = fold_doc f em x
        scope :: Context -> Expr -> Map String Var -> (Int,Int) -> Either Error ()
        scope ctx xp vs (i,j) = do
            let fv          = keysSet $ free_vars ctx xp
            let decl_v      = keysSet vs
            let undecl_v    = S.toList (fv `S.difference` decl_v)
            if fv `S.isSubsetOf` decl_v
            then return ()
            else Left ("Undeclared variables: " ++ intercalate ", " undecl_v, i,j)
        

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
collect_proofs cs m = foldl f (Right m) cs --  error "not implemented" 
    where
        f em (Env n (i,j) c _)
            | n == "proof"  = do
                    m           <- em
                    (po,rest)   <- get_1_lbl c
                    mproofs     <- foldl g (Right []) rest
                    case mproofs of
                        [p] -> return m { 
                            props = (props m) { 
                                proofs = insert (composite_label 
                                    [ _name m, label po ]) p $ 
                                      proofs $ props m } }
                        _   -> Left ("expecting a single calculation",i,j)
            | otherwise     = foldl f em c
        f em x              = fold_doc f em x
        g mxs (Env n (i,j) c _)
            | n == "calculation"    = do
                xs <- mxs
                cc <- calc c (i,j)
                return (cc { goal = infer_goal cc }:xs)
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
                        

--get_1_param :: [LatexDoc] -> Either Error ([LatexDoc], [LatexDoc])

get_1_lbl :: [LatexDoc] -> Either Error (String, [LatexDoc])
get_1_lbl xs = do -- Right ("", xs)
        ([x],z) <- cmd_params 1 xs
        case (trim_blank_text x) of
            ([Text [TextBlock x _]]) 
                -> Right (x,z)
            _   -> err_msg
    where
        err_msg = Left  ("expecting a label",-1,-1)
get_2_lbl :: [LatexDoc] -> Either Error (String, String, [LatexDoc])
get_2_lbl xs = do
        (lbl0,xs) <- get_1_lbl xs
        (lbl1,xs) <- get_1_lbl xs
        return (lbl0,lbl1,xs)

with_print_latex x = 
    unsafePerformIO (do
        putStrLn (tex_to_string x)
        return x)

parse_machine :: FilePath -> IO (Either String [Machine])
parse_machine fn = do
        ct <- readFile fn
        let r = do 
            xs <- latex_structure ct
            r <- all_machines xs
            return $ map snd $ toList $ r
        let x = case r of
                    Left xs -> Left $ show xs
                    Right r -> Right r
        return x
--    where
--        open (Env _ _ c _) = c
--        cont (Text xs) = xs
        