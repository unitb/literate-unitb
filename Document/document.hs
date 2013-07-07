module Document.Document where

import Data.Char
import Data.Map hiding ( map, foldl )
import Data.Maybe
import Data.List as L hiding ( union, insert, inits )
import qualified Data.Map as M

import Latex.Scanner
import Latex.Parser

import UnitB.AST

import System.IO
import System.IO.Unsafe

-- import Text.LaTeX.Base.Syntax

import Z3.Z3 hiding ( context )
import Z3.Const
import Z3.Def

fold_doc f x (Env s _ c _)     = L.foldl f x c
fold_doc f x (Bracket _ _ c _) = L.foldl f x c
fold_doc f x (Text _)          = x

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
                    Text xs             -> lines $ concatMap f $ concatMap (lexeme . item) xs)
            where
                indent xs = map (margin ++) xs
                margin  = "|  |"
                begin s = ["begin{" ++ s ++ "}"]
                end s   = ["end{" ++ s ++ "}"]
                f '\n'  = "\\n\n"
                f '\t'  = "\\t"
                f x     = [x]

sections = [
    "machine"]

extract_structure ct = do
        xs <- latex_structure ct
        return (find_env sections xs)
    where
        open (Env _ _ c _) = c
        cont (Text xs) = map item xs

--get_name 

drop_blank_text :: [LatexDoc] -> [LatexDoc]
drop_blank_text ( Text [Cell (Blank _) _ _] : ys ) = drop_blank_text ys
drop_blank_text ( Text (Cell (Blank _) _ _ : xs) : ys ) = drop_blank_text ( Text xs : ys )
drop_blank_text xs = xs

trim_blank_text xs = reverse $ drop_blank_text $ reverse $ drop_blank_text xs

skip_blanks :: [LatexToken] -> [LatexToken]
skip_blanks (Blank _ : xs) = xs
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
--                [ [Text [Cell (TextBlock xs) _ _]] ] -> xs
--                _             -> error "bad name"

--with_print x = 
--        unsafePerformIO (do
--            print x
--            return x)

eat_space :: Scanner Char ()
eat_space = do
        b <- is_eof
        if b
        then return ()
        else do
            x:_ <- peek
            if isSpace x
            then do
                read_char
                eat_space
            else return ()

isWord x = isAlphaNum x || x == '_'

word0 :: Scanner Char String
word0 = do
        read_if isWord 
            (\x -> do
                xs <- word0
                return (x:xs))
            (return [])

word = do
        read_if isAlpha
            (\x -> do
                xs <- word0
                return (x:xs))
            (fail "expecting non-empty word")

comma = do
        eat_space
        read_if (',' ==) 
            (\_ -> eat_space)
            (fail "expecting comma (',')")

colon :: Scanner Char ()
colon = do
        eat_space
        read_if (':' ==) 
            (\_ -> eat_space)
            (fail "expecting colon (':')")
            
type_t :: Scanner Char String
type_t = do
        read_if (== '\\')
            (\_ -> do
                xs <- word
                return ('\\':xs))
            word

type_of x = M.lookup x m
    where
        m = fromList [("\\Int", INT)]

vars :: Scanner Char [(String,Type)]
vars = do
        eat_space
        vs <- sep1 word comma
        colon
        t <- type_t
        eat_space
        case type_of t of
            Just t -> return (map (\x -> (x,t)) vs)
            Nothing -> fail "Invalid type"
            

as_variables :: LatexDoc -> Either Error [(String, Var)]
as_variables (Env s _ c _) = do
        xs <- read_tokens vars m
        return $ map (\(x,y) -> (x,Var x y)) xs
    where
        m = concatMap flatten_li c

pop_token :: [LatexDoc] -> [LatexDoc]
pop_token (Text (x1:x2:xs):ys) = Text xs:ys
pop_token ((Text [x1]):ys) = ys

--oper :: Context -> Scanner Char ((Expr -> Expr -> Expr), Int)
--oper ctx = match_first [
--              ( match_string "+", \_ -> return (zplus, 1)),
--              ( match_string "=", \_ -> return (zeq, 2)) ]
--            (fail "invalid operator")

plus = do
        x <- match $ match_string "+"
        case x of
            Just _ -> return ()
            Nothing -> fail "expecting plus (+)"

leq = do
        x <- match $ match_string "\\le"
        case x of
            Just _ -> return ()
            Nothing -> fail "expecting less of equal (\\le)"

times = do
        x <- match $ match_string "\\cdot"
        case x of
            Just _ -> return ()
            Nothing -> fail "expecting times (\\cdot)"

implication = do
        x <- match $ match_string "\\implies"
        case x of
            Just _  -> return ()
            Nothing -> fail "expecting implication (\\implies)"

oper = do
        try plus 
            (\_ -> return Plus) $
            try times
                (\_ -> return Mult) $
                try implication
                    (\_ -> return Implies) $
                    try leq
                        (\_ -> return Leq) $
                        (do equal ; return Equal)

equal = do
        x <- match $ match_string "="
        case x of
            Just _  -> return ()
            Nothing -> fail "expecting equal (=)"

term :: Context -> Scanner Char (Expr)
term ctx = do
        eat_space
        try word
            (\xs -> do
                (ys,zs) <- read_if (== '\'') 
                    (\x -> return (xs ++ "\'", xs ++ "_prime"))
                    (return (xs,xs))
                eat_space
                case var_decl xs ctx of
                    Just (Var _ t) -> return (Word $ Var zs t)
                    Nothing -> fail ("undeclared variable: " ++ xs))
            (do 
                xs <- number
                eat_space
                return (Number xs))

number = do
        xs <- match f
        case xs of
            Just n  -> return $ read n
            Nothing -> fail "expecting a number"
    where
        f x
                | n == 0    = Nothing
                | 0 < n     = Just n
            where
                n = length $ takeWhile isDigit x

type Oper = ((Expr -> Expr -> Expr), Int)

data Assoc = LeftAssoc | RightAssoc | Ambiguous
    deriving Show

data Operator = Plus | Mult | Equal | Leq | Implies
    deriving (Eq,Ord,Show,Enum)

mk_expr Plus x y    = x `zplus` y
mk_expr Mult x y    = x `ztimes` y
mk_expr Equal x y   = x `zeq` y
mk_expr Leq x y     = x `zle` y
mk_expr Implies x y = x `zimplies` y 

associativity = [
        ([Mult],LeftAssoc),
        ([Plus],LeftAssoc),
        ([Equal,Leq],Ambiguous),
        ([Implies],Ambiguous) ]

prod (xs,z) = [ ((x,y),z) | x <- xs, y <- xs ]

pairs = fromList (concat (do
            ((x,_),xs) <- zip a $ tail $ tails a
            (y,_)      <- xs
            a          <- x
            b          <- y
            return [
                ((a,b),LeftAssoc),
                ((b,a),RightAssoc) ])
        ++ concatMap prod a    )
    where
        a = associativity

assoc x y = pairs ! (x,y)

--assoc Equal Equal = Ambiguous
--assoc Equal Leq   = Ambiguous
--assoc Leq Equal   = Ambiguous
--assoc Leq Leq     = Ambiguous
--assoc Equal _     = RightAssoc
--assoc _ Equal     = LeftAssoc
--assoc Leq _       = RightAssoc
--assoc _ Leq       = LeftAssoc
--assoc Plus Mult   = RightAssoc
--assoc _ _         = LeftAssoc

open_brack  = do 
        x <- match $ match_string "("
        case x of
            Just _ -> return ()
            Nothing -> fail "expecting a bracket '('"

close_brack = do 
        x <- match $ match_string ")" 
        case x of
            Just _ -> return ()
            Nothing -> fail "expecting a bracket ')'"

expr :: Context -> Scanner Char Expr
expr ctx = do
        r <- read_term []
        return r
    where
        read_term :: [(Expr, Operator)] -> Scanner Char Expr
        read_term xs = do
            s <- peek
            eat_space
            try open_brack
                (\() -> do
                        r <- expr ctx
                        close_brack
                        eat_space
                        read_op xs r
                    ) $ (do
                        t <- term ctx
                        read_op xs t)
        read_op :: [(Expr, Operator)] -> Expr -> Scanner Char Expr
        read_op xs e0 = do
            b1 <- is_eof
            b2 <- look_ahead close_brack
            if b1 || b2
            then do
                reduce_all xs e0
            else do
                op <- oper
                reduce xs e0 op
        reduce :: [(Expr, Operator)] -> Expr -> Operator -> Scanner Char Expr
        reduce [] e0 op0                 = read_term [(e0,op0)]
        reduce xs@( (e0,op0):ys ) e1 op1 = do
            case assoc op0 op1 of
                LeftAssoc ->  
                    reduce ys (mk_expr op0 e0 e1) op1
                RightAssoc -> read_term ((e1,op1):xs)
                Ambiguous ->  fail ("ambiguous expression: use parentheses")
        reduce_all [] e               = return e
        reduce_all xs@( (e0,op0):ys ) e1 = do
                reduce_all ys (mk_expr op0 e0 e1)

parse_expr :: Context -> [(Char, (Int,Int))] -> Either (String, Int, Int) Expr
parse_expr ctx c = read_tokens (expr ctx) c

type Error = (String,Int,Int)

as_action :: Context -> [LatexDoc] -> Either Error (Map Label Event) 
as_action ctx c = do
            (a,b,xs) <- get_labels
            e        <- parse_expr ctx (concatMap flatten_li xs)
            return $ singleton (label a) $ empty_event { action = singleton (label b) e }
    where
        get_labels = do
            kk <- cmd_params 2 c
            case kk of
                ([  [Text [Cell (TextBlock a) _ _]], 
                    [Text [Cell (TextBlock b) _ _]]],xs) -> 
                    return (a,b,xs)
                _                                        -> 
                    Left ("invalid assignment names", -1, -1)

--as_machine :: LatexDoc -> Machine
--as_machine (Env n _ c _) = 
--        (empty_machine name) { events = evts, variables = vars }
--    where
--        evts  = mapMaybeWithKey set_act $ 
--            fromList $ map (as_event) (find_cmd cmds rest ! event_lbl)
--        acts  :: Map Label (Map Label Expr)
--        acts  = M.map (fromList) $ fromListWith (++) $ map (as_action ctx) $ with_print (env ! act_env) 
--        vars  = fromList $ concatMap (as_variables) (env ! var_env)
--        ctx   = Context vars empty empty
--        set_act n e = do
--            a <- M.lookup n acts 
--            return (e { action = a })
--        env   = with_print $ find_env envs rest
--        (name, rest) = 
--            case drop_blank_text c of 
--                Bracket True _ [Text xs] _ : ys ->
--                    case trim_blanks $ map item xs of
--                        [TextBlock xs] -> (xs, ys)
--                        _ -> error "wrong"
--                            -- (Nothing, ys)
--                _ -> error "expecting only a string as a machine name"
--                    -- (Nothing, [])
--as_machine _ = error "only an environment construct can be a machine"



all_machines :: [LatexDoc] -> Either Error (Map String Machine)
all_machines xs =
        let ms = L.foldl (f first_pass) (Right empty) xs in
                 L.foldl (f sec_pass) ms xs
--                 M.map _ ms
    where
        first_pass name cont ms = declarations name cont
        sec_pass name cont ms   = build_machine name cont (ms ! name)
        f pass em (Env n _ c _)     
                | n == "machine"    = do
                    ms          <- em
                    (name,cont) <- get_name c
                    m           <- pass name cont ms
                    return (insertWith merge_machine name m ms)
                | otherwise         = L.foldl (f pass) em c
        f pass em x                 = fold_doc (f pass) em x
        get_name :: [LatexDoc] -> Either (String, Int, Int) (String,[LatexDoc])
        get_name c = do
            ([name], rest) <- cmd_params 1 c
            case trim_blank_text name of
                [ Text [Cell (TextBlock xs) _ _] ] -> Right (xs,rest)
                _                                  -> Left ("invalid machine name",-1,-1)

merge_event :: Event -> Event -> Event
merge_event e@(Event ind0 c0 f0 p0 g0 a0) (Event ind1 c1 f1 p1 g1 a1) = 
        Event (ind0++ind1) c2 f2 (p0++p1) (g0`union`g1) (a0`union`a1)
    where
        c2 = case maybeToList c0 ++ maybeToList c1 of
                [x,y] -> Just (x `union` y)
                [x]   -> Just x
                []    -> Nothing
        f2 = case maybeToList f0 ++ maybeToList f1 of
                [x,y] -> Just (x `zand` y)
                [x]   -> Just x
                []    -> Nothing

--combine :: 

merge_machine :: Machine -> Machine -> Machine
merge_machine (Mch n t0 v0 i0 ev0 p0) (Mch _ t1 v1 i1 ev1 p1) =
        Mch n (t0 ++ t1) 
            (v0 `union` v1) (i0++i1) 
            (unionWith merge_event ev0 ev1)
            (p0 `ps_union` p1)

context m = Context (variables m) empty empty

declarations :: String -> [LatexDoc] -> Either (String,Int,Int) Machine
declarations name cs = foldl f (Right $ empty_machine name) cs
    where
        f em e@(Env s _ xs _) 
                | s == "variable"   = do
                    m  <- em
                    vs <- as_variables e
                    return (m { variables = fromList vs `union` variables m})
                | otherwise         = foldl f em xs
        f em e                      = fold_doc f em e
        
    -- Todo: report an error if we create assignments (or other events elements)
    -- for events that are not declared.
build_machine :: String -> [LatexDoc] -> Machine -> Either (String,Int,Int) Machine
build_machine name cs m = foldl f (Right m) cs
    where
        f em e@(Env s _ xs _) 
                | s == "evassignment"   = do
                        m             <- em
                        (ev,lbl,rest) <- get_assign
                        act           <- as_action (context m) xs
                        return m { events = unionWith merge_event act
                                        $ events m } 
                | s == "invariant"      = do
                        m             <- em
                        (lbl,rest)    <- get_2_lbl xs
                        invar         <- get_expr m rest
                        return m { 
                            props = (props m) { 
                                inv = insert (label lbl) invar $ inv $ props m } }
                | s == "initialization" = do
                        m             <- em
                        (lbl,rest)    <- get_2_lbl xs
                        initp         <- get_expr m rest
                        return m {
                                inits = initp : inits m }
                | s == "transient"      = do
                        m             <- em
                        (ev,lbl,rest) <- get_3_lbl xs
                        tr            <- get_expr m rest
--                        let !x = with_print ("transient: " ++ show tr)
                        m <- return m {
                            props = (props m) {
                                program_prop = insert (label lbl) (Transient [] tr $ label ev)
                                    $ program_prop $ props m } }
--                        let !x = with_print m
                        return m
                | s == "cschedule"     = do
                        m              <- em
                        (evt,lbl,rest) <- get_3_lbl xs
                        sched          <- get_expr m rest
                        let event = singleton (label evt) 
                                (empty_event { 
                                    c_sched = Just $ singleton (label lbl) sched })
                        return m {          
                                events  = unionWith merge_event event $ events m }
                | s == "fschedule"     = do
                        m              <- em
                        (evt,lbl,rest) <- get_3_lbl xs
                        sched          <- get_expr m rest
                        let event = singleton (label evt) 
                                (empty_event { 
                                    f_sched = Just sched })
                        return m {          
                                events  = unionWith merge_event event $ events m }
                | s == "constraint"     = do
                        m               <- em
                        (lbl,rest)      <- get_2_lbl xs
                        pre             <- get_expr m rest
                        return m { 
                            props = (props m) { 
                                program_prop = insert (label lbl) (Co [] pre) 
                                    $ program_prop $ props m } }
                | otherwise             = foldl f em xs
            where
                get_2_lbl :: [LatexDoc] -> Either Error (String, [LatexDoc])
                get_2_lbl xs = do -- Right ("", xs)
                        ([x],z) <- cmd_params 1 xs
                        case (trim_blank_text x) of
                            ([Text [Cell (TextBlock x) _ _]]) 
                                -> Right (x,z)
                            _   -> err_msg
                    where
                        err_msg = Left  ("badly formed invariant label",-1,-1)
                get_3_lbl :: [LatexDoc] -> Either Error (String, String, [LatexDoc])
                get_3_lbl xs = do
                        (lbl0,xs) <- get_2_lbl xs
                        (lbl1,xs) <- get_2_lbl xs
                        return (lbl0,lbl1,xs)
                get_expr :: Machine -> [LatexDoc] -> Either Error Expr
                get_expr m xs =
                        parse_expr (context m) (concatMap flatten_li xs)
                get_assign :: Either (String,Int,Int) (String, String, [LatexDoc])
                get_assign = do 
                        ([x,y],z) <- cmd_params 2 xs
                        case (trim_blank_text x, trim_blank_text y) of
                            ([Text [Cell (TextBlock x) _ _]],
                                [Text [Cell (TextBlock y) _ _]]) 
                                -> Right (x,y,z)
                            _   -> err_msg
                    where
                        err_msg = Left  ("badly formed assignment",-1,-1)
        f em e                      = fold_doc f em e
        
with_print_latex x = 
    unsafePerformIO (do
        putStrLn (tex_to_string x)
        return x)

parse_machine :: FilePath -> IO (Either String [Machine])
parse_machine fn = do
        ct <- readFile fn
        let r = do 
            xs <- latex_structure ct
--            let r = find_env sections $ with_print $ drop 1 $ open (xs !! 16)
--            return $ (map as_machine (r ! "machine"), r ! "machine")
            r <- all_machines xs
            return $ map snd $ toList $ r
        x <- case r of
            Left xs -> return $ Left $ show xs
--            Right (r,xs) -> do
            Right r -> 
                return $ Right r
        return x
    where
        open (Env _ _ c _) = c
        cont (Text xs) = map item xs
        