{-# LANGUAGE BangPatterns, FlexibleContexts #-}
module Document.Expression 
    ( parse_expr, oper, eat_space, get_variables )
where

    -- Modules
import Latex.Scanner
import Latex.Parser

import Logic.Const
import Logic.Expr
import Logic.ExpressionStore as ES
import Logic.Genericity hiding (unsafePerformIO)
import Logic.Operator

import Theories.SetTheory
import Theories.FunctionTheory
import Theories.Notation

import Utilities.Syntactic

import Z3.Z3

    -- Libraries
import Control.Monad.Reader.Class
import Control.Monad.State.Class
import Control.Monad.Trans
import Control.Monad.Trans.Either

import Data.Char
import Data.Either
import Data.List as L
import Data.Map as M hiding ( map )

import Utilities.Format

match_char p = read_if p (\_ -> return ()) (fail "") >> return ()

eat_space :: Scanner Char ()
eat_space = do
        b <- is_eof
        if b
        then return ()
        else choice 
                [ match_char isSpace 
                , read_list "\\\\" >> return ()
                , read_list "~" >> return ()
                , read_list "&" >> return ()
                , read_list "\\," >> return ()
                , read_list "\\:" >> return ()
                , read_list "\\;" >> return ()
                , read_list "\\!" >> return ()
                , read_list "\\quad" >> return ()
                , read_list "\\qquad" >> return ()
                , read_list "\\" >> match_char isDigit 
                ] (return ())
                (\_ -> eat_space)

--space_cmd :: Scanner a ()
--space_cmd = return ()

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
type_t ctx@(Context _ _ _ _ _) = do
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
            return t
        else return t

get_type :: Context -> String -> Maybe Sort
get_type (Context ts _ _ _ _) x = M.lookup x m
    where
        m = fromList 
                   [ ("\\Int", IntSort)
                   , ("\\Real", RealSort)
                   , ("\\Bool", BoolSort)]
            `M.union` ts
--        z3_type s@(Sort _ x _) = USER_DEFINED s

vars :: Context -> Scanner Char [(String,Type)]
vars ctx = do
        eat_space
        vs <- sep1 word comma
        colon
        t <- type_t ctx
        eat_space       
        return (map (\x -> (x,t)) vs)     

get_variables :: (Monad m, MonadReader LineInfo m)
              => Context -> [LatexDoc] -> EitherT [Error] m [(String, Var)]
get_variables ctx cs = do
        LI fn i j <- lift $ ask
        xs <- hoistEither $ read_tokens (vars ctx) fn m (i,j)
        return $ map (\(x,y) -> (x,Var x y)) xs
    where
        m = concatMap flatten_li cs

--plus = do
--        x <- match $ match_string "+"
--        case x of
--            Just _ -> return ()
--            Nothing -> fail "expecting plus (+)"
--
--fun_app = do
--        x <- match $ match_string "."
--        case x of
--            Just _ -> return ()
--            Nothing -> fail "expecting function application (.)"
--
--leq = read_list "\\le"
--
--lt = read_list "<"
--
--geq = read_list "\\ge"
--
--gt = read_list ">"
--
--times = do
--        x <- match $ match_string "\\cdot"
--        case x of
--            Just _ -> return ()
--            Nothing -> fail "expecting times (\\cdot)"
--
--implication = read_list "\\implies"
--
--follows     = read_list "\\follows"
--
--conjunction = read_list "\\land"
--
--disjunction = read_list "\\lor"
--
--equivalence = read_list "\\equiv"
--
--power  = read_list "^"
--
--tfun   = read_list "\\tfun"
--
--bunion = read_list "\\bunion"
--
--overload = read_list "|"
--
--dom_sub  = read_list "\\domsub"
--
--dom_rest = read_list "\\domres"
--
--membership = 
--        read_list "\\in"
--
--set_diff = read_list "\\setminus"
--
--negation = read_list "\\neg"

unary :: Scanner Char UnaryOperator
unary = do
        choice 
            (map f $ lefts $ new_ops notations)
--            [  negation >> return Negation
--            ]
            (fail "expecting an unary operator")            
            return
    where
        f op@(UnaryOperator _ tok _) = do
            read_list tok
            return op

oper = do
        choice 
            (concatMap f $ rights $ new_ops notations)
--        choice [
--                (plus  >> return Plus),
--                (times >> return Mult),
--                (power >> return Power),
--                (implication >> return Implies),
--                (follows     >> return Follows),
--                (conjunction >> return And),
--                (disjunction >> return Or),
--                (equivalence >> return Equiv),
--                (leq >> return Leq),
--                (lt >> return Less),
--                (geq >> return Geq),
--                (gt >> return Greater),
--                (equal >> return Equal),
--                (membership >> return Membership),
--                (bunion >> return Union),
--                (set_diff >> return SetDiff),
--                (overload >> return Overload),
--                (dom_sub >> return DomSubt),
--                (dom_rest >> return DomRest),
--                (tfun >> return MkFunction), -- TotalFunction),
--                (fun_app >> return Apply) ]
            (fail "expecting a binary operator")            
            return
    where
        f op@(BinOperator _ tok _) = [do
            read_list tok
            return op]
--        f op@(Operator Unary _ _)    = []

--equal = do
--        x <- match $ match_string "="
--        case x of
--            Just _  -> return ()
--            Nothing -> fail "expecting equal (=)"

data FunOperator = Domain | Range
    deriving Show

apply_fun_op :: FunOperator -> Expr -> Scanner Char Term
apply_fun_op fop x = 
        case f fop $ Right x of
            Right e -> return $ Right e
            Left xs -> fail $ format "type error: {0}" xs
    where
        f Domain = zdom
        f Range  = zran

type Term = Either FunOperator Expr

term :: Context -> Scanner Char Term
term ctx = do
        eat_space
        try word_or_command
            (\xs -> do
                (_,zs) <- read_if (== '\'') 
                    (const $ return (\x -> x ++ "\'", \x -> x ++ "@prime"))
                    (return (id,id))
                eat_space
                case xs `L.lookup` 
                        [ ("\\true",Right ztrue)
                        , ("\\false",Right zfalse)
                        , ("\\emptyset", Right zempty_set)
                        , ("\\emptyfun", Right zempty_fun) 
                        , ("\\dom", Left Domain)
                        , ("\\ran", Left Range) ] of
                    Just e  -> return e 
                    Nothing ->
--                        if xs == "\\dom"
--                        then do
--                            read_list "."
--                            eat_space
--                            x <- pick 
--                                [ (term ctx, return)
--                                , (read_list "(" >> return ztrue, \_ -> do
--                                        eat_space
--                                        e <- expr ctx
--                                        eat_space
--                                        read_list ")"
--                                        eat_space
--                                        return e)
--                                , (read_list "{" >> return ztrue, \_ -> do
--                                        eat_space
--                                        e <- expr ctx
--                                        eat_space
--                                        read_list "}"
--                                        eat_space
--                                        return e)
--                                ] (fail "invalid argument for 'dom'") 
--                            either (\(x) -> fail x) return (zdom $ Right x)
--                        else 
                        if xs `elem` 
                            [ "\\qforall"
                            , "\\qexists"
                            , "\\qfun"
                            , "\\qset" ]
                        then do
                            eat_space

                            read_list "{"
                            eat_space
                            vs <- sep1 word comma :: Scanner Char [String]
                            eat_space
                            read_list "}"
                            eat_space

                            read_list "{"
                            eat_space
                            r <- try (read_list "}") 
                                (\_ -> return ztrue)
                                (do r <- expr ctx
                                    read_list "}"
                                    return r)
                            eat_space
                            
                            read_list "{"
                            eat_space
                            t <- expr ctx
                            eat_space
                            read_list "}"
                            eat_space
                            let { quant = fromList 
                                [ ("\\qforall",Binder Forall)
                                , ("\\qexists",Binder Exists)
                                , ("\\qfun",Binder Lambda) 
                                , ("\\qset", \x y z -> fromJust $ zset (Right $ Binder Lambda x y z) ) ] ! xs }
                            case dummy_types vs ctx of
                                Just vs -> return $ Right (quant vs r t)
                                Nothing -> fail ("bound variables are not typed")
                        else if xs == "\\oftype"
                        then do
                            eat_space
                            read_list "{"
                            eat_space
                            e <- expr ctx
                            eat_space
                            read_list "}"
                            eat_space
                            read_list "{"
                            eat_space
                            t <- type_t ctx
                            eat_space
                            read_list "}"
                            eat_space
                            case zcast t (Right e) of
                                Right new_e -> return $ Right new_e
                                Left msg -> fail msg
                        else case var_decl xs ctx of
                            Just (Var v t) -> return $ Right (Word $ Var (zs v) t) 
                            Nothing -> fail ("undeclared variable: " ++ xs))
            (do 
                xs <- number
                eat_space
                return $ Right (Const [] xs $ USER_DEFINED IntSort []))

dummy_types vs (Context _ _ _ _ dums) = mapM f vs
    where
        f x = M.lookup x dums

number :: Scanner Char String
number = do
        xs <- match f
        case xs of
            Just n  -> return n
            Nothing -> fail "expecting a number"
    where
        f x
                | 0 < n     = Just n
                | otherwise = Nothing
            where
                n = length $ takeWhile isDigit x

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
        case r of
            Right e -> return e
            Left op -> fail $ format "unused functional operator: {0}" op
    where
        read_term :: [([UnaryOperator], Term, BinOperator)] 
                  -> Scanner Char Term
        read_term xs = do
            us <- many (eat_space >> unary)
            eat_space
            try open_brack
                (\_ -> do
                        e <- expr ctx
                        close_brack
                        eat_space
                        read_op xs us (Right e)
                    ) $ (try open_curly 
                             (\_ -> do
                                rs <- sep1 (expr ctx) comma
                                close_curly
                                eat_space
                                case zset_enum $ map Right rs of
                                    Right e -> read_op xs us $ Right e 
                                    Left xs -> fail (format "type error: {0}" xs)
                            ) $ (do
                                t <- term ctx
                                read_op xs us t))
        read_op :: [([UnaryOperator], Term, BinOperator)] 
                -> [UnaryOperator] 
                -> Term 
                -> Scanner Char Term
        read_op xs us e0 = do
            b1 <- is_eof
            b2 <- look_ahead close_brack
            b3 <- look_ahead close_curly
            b4 <- look_ahead comma
            b5 <- look_ahead (read_list "}")
            if b1 || b2 || b3 || b4 || b5
            then do
                reduce_all xs us e0
            else do
                op <- oper
                reduce xs us e0 op
        reduce :: [([UnaryOperator], Term, BinOperator)] 
               -> [UnaryOperator]
               -> Term 
               -> BinOperator 
               -> Scanner Char Term
        reduce [] [] e0 op0                 = read_term [([],e0,op0)]
        reduce xs@( (vs,e0,op0):ys ) [] e1 op1 = do
            case assoc op0 op1 of
                LeftAssoc ->  do
                    e2 <- apply_op op0 e0 e1
                    reduce ys vs e2 op1
                RightAssoc -> read_term (([],e1,op1):xs)
                Ambiguous ->  fail $ format "ambiguous expression: {0} and {1} are not associative" op0 op1
        reduce xs (u:us) e0 op0             =
            case binds u op0 of
                LeftAssoc   -> do
                    e1 <- apply_unary u e0
                    reduce xs us e1 op0
                RightAssoc  -> read_term ((u:us,e0,op0):xs)
                Ambiguous   -> fail ("ambiguous expression: use parentheses")
        reduce_all :: [([UnaryOperator], Term, BinOperator)] 
                   -> [UnaryOperator] 
                   -> Term 
                   -> Scanner Char Term
        reduce_all [] [] e             = return e
        reduce_all ( (us,e0,op0):ys ) [] e1 = do
                e2 <- apply_op op0 e0 e1
                reduce_all ys us e2
        reduce_all xs (u:us) e0        = do
                e1 <- apply_unary u e0
                reduce_all xs us e1
                    

apply_unary :: UnaryOperator -> Term -> Scanner Char Term
apply_unary op e = do
        case e of 
            Right e ->
                case mk_unary op e of
                    Right x2 -> return $ Right x2
                    Left xs -> 
                        fail (format "type error: {0}" xs)
            Left oper -> fail $ format 
                    err_msg oper op
    where
        err_msg = "functional operator cannot be the operand of any unary operator: {0}, {1}"
        
apply_op :: BinOperator -> Term -> Term -> Scanner Char Term
apply_op op x0 x1 = do
        case x1 of
            Right e1 -> do
                case x0 of
                    Right e0 ->
                        case mk_expr op e0 e1 of
                            (Right e2) -> return $ Right e2
                            Left xs  -> 
                                fail (format "type error: {0}" xs)
                    Left oper ->
                        if op == apply then
                            apply_fun_op oper e1
                        else fail $ format err_msg oper op
            Left e1 -> 
                fail $ format err_msg e1 op
    where
        err_msg = "functional operator cannot be the operand of any binary operator: {0}, {1}"

parse_expr :: ( Monad m
              , MonadReader LineInfo m
              , MonadState ExprStore m) 
           => Context -> [(Char, LineInfo)] 
           -> EitherT [Error] m Expr
parse_expr ctx c = do
        li <- lift $ ask
        !e <- hoistEither $ read_tokens 
            (expr ctx) 
            (file_name li) 
            c (line li, column li)
        ES.insert e (map fst c)
        return e
