module Document.Expression where

import Data.Char
import Data.List
import Data.Map as M hiding ( map )

import Latex.Scanner
import Latex.Parser

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
            
type_t :: Context -> Scanner Char Type
type_t ctx@(Context ts _ _ _) = do
        t <- read_if (== '\\')
            (\_ -> do
                xs <- word
                return ('\\':xs))
            word
        if t == "\\set"
        then do
            eat_space
            read_list "["
            eat_space
            t <- type_t ctx
            eat_space
            read_list "]"
            eat_space
            return (SET t)
        else case type_of ctx t of
                Just t -> return t
                Nothing -> fail ("Invalid type, '" ++ t ++ "' not found, " ++ show ts)

type_of (Context ts _ _ _) x = M.lookup x m
    where
        m = fromList ( 
                   [("\\Int", INT), ("\\Real", REAL), ("\\Bool", BOOL)]
                ++ zip ts (map USER_DEFINED ts) )

vars :: Context -> Scanner Char [(String,Type)]
vars ctx = do
        eat_space
        vs <- sep1 word comma
        colon
        t <- type_t ctx
        eat_space       
        return (map (\x -> (x,t)) vs)     

as_variables :: Context -> LatexDoc -> Either Error [(String, Var)]
as_variables ctx (Env s _ c _) = do
        xs <- read_tokens (vars ctx) m
        return $ map (\(x,y) -> (x,Var x y)) xs
    where
        m = concatMap flatten_li c

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

oper = do
        try plus 
            (\_ -> return Plus) $
            try times
                (\_ -> return Mult) $
                try implication
                    (\_ -> return Implies) $
                    try conjunction
                        (\_ -> return And) $
                        try leq
                            (\_ -> return Leq) $
                            try power
                                (\_ -> return Power) $
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

data Assoc = LeftAssoc | RightAssoc | Ambiguous
    deriving Show

associativity :: [([Operator],Assoc)]
associativity = [
        ([Power],Ambiguous),
        ([Mult],LeftAssoc),
        ([Plus],LeftAssoc),
        ([Equal,Leq],Ambiguous),
        ([And],LeftAssoc),
        ([Implies,Follows],Ambiguous) ]

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
