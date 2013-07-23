{-# LANGUAGE BangPatterns #-}
module Document.Expression where

import Data.Char
import Data.List as L
import Data.Map as M hiding ( map )
import qualified Data.Map as M ( map )

import Latex.Scanner
import Latex.Parser

import System.IO.Unsafe

import UnitB.Operator
import UnitB.SetTheory
import UnitB.FunctionTheory

import Utilities.Format

import Z3.Const
import Z3.Def
import Z3.Z3

eat_space :: Scanner Char ()
eat_space = do
--        choice [
--            try eof (\() -> fail "") (return ()),
--            read_if isSpace (\_ -> return ()) (fail "")
----            space_cmd
--            ] (return ())
--              (\() -> eat_space)
        b <- is_eof
        if b
        then return ()
        else read_if isSpace (
                \_ -> eat_space)
                (return ())
--            x:_ <- peek
--            if isSpace x
--            then do
--                read_char
--                eat_space
----            else do
----                b <- look_ahead space_cmd
----                if b
----                then do
----                    space_cmd
----                    eat_space
--            else return ()

space_cmd :: Scanner a ()
space_cmd = return ()

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
            
read_list :: (Eq a,Show a) => [a] -> Scanner a [a]
read_list xs = do
        x <- match (match_string xs) 
        case x of
            Just x -> return x
            Nothing -> fail ("expecting: " ++ show xs)
            
word_or_command =
    read_if (== '\\')
            (\_ -> do
                xs <- word
                return ('\\':xs))
            word

type_t :: Context -> Scanner Char Type
type_t ctx@(Context ts _ _ _ _) = do
        t <- word_or_command
        eat_space
        b1 <- look_ahead $ read_list "["
        ts <- if b1
            then do
                read_list "["
                eat_space
                ts <- sep1 (type_t ctx) comma
                eat_space
                read_list "]"
                eat_space
                return ts
            else return []
        t <- case get_type ctx t of
            Just s -> return $ USER_DEFINED s ts
            Nothing -> fail ("Invalid sort: '" ++ t ++ "'")
        b2 <- look_ahead $ read_list "\\pfun"
        if b2 
        then do
            read_list "\\pfun"
            eat_space
            t2 <- type_t ctx
            t <- return $ fun_type t t2
--            let !() = unsafePerformIO (putStrLn $ format "parsed a type {0}" t)
            return t
        else return t

get_type :: Context -> String -> Maybe Sort
get_type (Context ts _ _ _ _) x = M.lookup x m
    where
        m = fromList ( 
                   [("\\Int", IntSort), ("\\Real", RealSort), ("\\Bool", BoolSort)])
            `M.union` ts
--                ++ zip (keys ts) (map USER_DEFINED $ map z3_type $ elems ts) )
        z3_type s@(Sort _ x _) = USER_DEFINED s

vars :: Context -> Scanner Char [(String,Type)]
vars ctx = do
        eat_space
        vs <- sep1 word comma
        colon
        t <- type_t ctx
        eat_space       
        return (map (\x -> (x,t)) vs)     

get_variables :: Context -> [LatexDoc] -> Either [Error] [(String, Var)]
get_variables ctx cs = do
        xs <- read_tokens (vars ctx) m
        return $ map (\(x,y) -> (x,Var x y)) xs
    where
        m = concatMap flatten_li cs

--as_variables :: Context -> LatexDoc -> Either Error [(String, Var)]
--as_variables ctx (Env s _ c _) = do
--        xs <- read_tokens (vars ctx) m
--        return $ map (\(x,y) -> (x,Var x y)) xs
--    where
--        m = concatMap flatten_li c

plus = do
        x <- match $ match_string "+"
        case x of
            Just _ -> return ()
            Nothing -> fail "expecting plus (+)"

fun_app = do
        x <- match $ match_string "."
        case x of
            Just _ -> return ()
            Nothing -> fail "expecting function application (.)"

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

conjunction = do
        x <- match $ match_string "\\land"
        case x of
            Just _  -> return ()
            Nothing -> fail "expecting conjunction (\\land)"

power = do
        x <- match $ match_string "^"
        case x of
            Just _  -> return ()
            Nothing -> fail "expecting exponential (^)"

tfun = read_list "\\tfun"

membership = 
        read_list "\\in"
--        case x of
--            Just _  -> return ()
--            Nothing -> fail "expecting set membership (\\in)"

set_diff = read_list "\\setminus"

oper = do
        choice [
                (plus >> return Plus),
                (times >> return Mult),
                (implication >> return Implies),
                (conjunction >> return And),
                (leq >> return Leq),
                (power >> return Power),
                (membership >> return Membership),
                (equal >> return Equal),
                (set_diff >> return SetDiff),
                (tfun >> return TotalFunction),
                (fun_app >> return Apply) ]
            (fail "expecting an operator")            
            return

equal = do
        x <- match $ match_string "="
        case x of
            Just _  -> return ()
            Nothing -> fail "expecting equal (=)"

term :: Context -> Scanner Char (Expr)
term ctx = do
        eat_space
        try word_or_command
            (\xs -> do
                (ys,zs) <- read_if (== '\'') 
                    (\x -> return (\x -> x ++ "\'", \x -> x ++ "@prime"))
                    (return (id,id))
                eat_space
                case xs `L.lookup` [("\\true",ztrue), ("\\false",zfalse)] of
                    Just e  -> return e 
                    Nothing ->
                        case var_decl xs ctx of
                            Just (Var v t) -> return (Word $ Var (zs v) t) 
                            Nothing -> fail ("undeclared variable: " ++ xs))
            (do 
                xs <- number
                eat_space
                return (Const xs INT))

number :: Scanner Char String
number = do
        xs <- match f
        case xs of
            Just n  -> return n
            Nothing -> fail "expecting a number"
    where
        f x
                | n == 0    = Nothing
                | 0 < n     = Just n
            where
                n = length $ takeWhile isDigit x

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


open_curly = read_list "\\{"

close_curly = read_list "\\}"

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
                (\_ -> do
                        r <- expr ctx
                        close_brack
                        eat_space
                        read_op xs r
                    ) $ (try open_curly 
                             (\_ -> do
                                rs <- sep1 (expr ctx) comma
                                close_curly
                                eat_space
                                case zset_enum $ map Right rs of
                                    Right rs -> read_op xs rs 
                                    Left xs -> fail (format "type error: {0}" xs)
                            ) $ (do
                                t <- term ctx
                                read_op xs t))
        read_op :: [(Expr, Operator)] -> Expr -> Scanner Char Expr
        read_op xs e0 = do
            b1 <- is_eof
            b2 <- look_ahead close_brack
            b3 <- look_ahead close_curly
            b4 <- look_ahead comma
            if b1 || b2 || b3 || b4
            then do
                reduce_all xs e0
            else do
                op <- oper
                reduce xs e0 op
        reduce :: [(Expr, Operator)] -> Expr -> Operator -> Scanner Char Expr
        reduce [] e0 op0                 = read_term [(e0,op0)]
        reduce xs@( (e0,op0):ys ) e1 op1 = do
            case assoc op0 op1 of
                LeftAssoc ->  do
                    e2 <- apply_op op0 e0 e1
                    reduce ys e2 op1
                RightAssoc -> read_term ((e1,op1):xs)
                Ambiguous ->  fail ("ambiguous expression: use parentheses")
        reduce_all [] e               = return e
        reduce_all xs@( (e0,op0):ys ) e1 = do
                e2 <- apply_op op0 e0 e1
                reduce_all ys e2

apply_op op x0 x1 = do
--    let !() = unsafePerformIO (putStrLn $ format "types {0},{1} and {2}" op (x0) (x1))
--    let !() = unsafePerformIO (putStrLn $ format "types {0} and {1}" (type_of x0) (type_of x1))
    case mk_expr op x0 x1 of
        Right x2 -> return x2
        Left xs -> 
--            let !() = unsafePerformIO (putStrLn $ format "type error") in
            fail (format "type error: {0}" xs)

parse_expr :: Context -> [(Char, (Int,Int))] -> Either [Error] Expr
parse_expr ctx c = read_tokens (expr ctx) c 
