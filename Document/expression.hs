{-# LANGUAGE BangPatterns, FlexibleContexts #-}
module Document.Expression 
    ( parse_expr, oper
    , get_variables, parse_oper )
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
import           Control.Monad.Reader.Class
import           Control.Monad.State.Class
import           Control.Monad.Trans
import           Control.Monad.Trans.Either
import qualified Control.Monad.Trans.Reader as R

import Data.Char
import Data.Either
import Data.List as L
import Data.Map as M hiding ( map )

import Utilities.Format

data Parser a = Parser { fromParser :: (R.ReaderT (Context, Notation) (Scanner Char) a) }

instance Monad Parser where
    Parser m0 >>= f = Parser $ m0 >>= (fromParser . f)
    return x = Parser $ return x
    fail x   = Parser $ fail x

runParser :: Context -> Notation -> Parser a -> Scanner Char a
runParser x y m = R.runReaderT (fromParser m) (x,y)

get_context :: Parser Context 
get_context = Parser $ R.asks fst

get_notation :: Parser Notation
get_notation = Parser $ R.asks snd

liftP :: Scanner Char a -> Parser a
liftP = Parser . lift

liftHOF :: (Scanner Char a -> Scanner Char b) -> Parser a -> Parser b
liftHOF f m = do
        x <- get_context
        y <- get_notation
        liftP $ f $ runParser x y m

match_char p = read_if p (\_ -> return ()) (fail "") >> return ()

eat_spaceP :: Parser ()
eat_spaceP = liftP $ eat_space

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

read_ifP :: (Char -> Bool) -> (Char -> Parser a) -> Parser a -> Parser a 
read_ifP p m0 m1 = do
        x <- get_context
        y <- get_notation
        liftP $ read_if p 
            (runParser x y . m0)
            (runParser x y m1)

word0 :: Parser String
word0 = read_ifP isWord 
            (\x -> do
                xs <- word0
                return (x:xs))
            (return [])

word :: Parser String
word = do
        read_ifP isAlpha
            (\x -> do
                xs <- word0
                return (x:xs))
            (fail "expecting non-empty word")

comma :: Parser ()
comma = do
        eat_spaceP
        read_ifP (',' ==) 
            (\_ -> eat_spaceP)
            (fail "expecting comma (',')")

colon :: Parser ()
colon = do
        eat_spaceP
        read_ifP (':' ==) 
            (\_ -> eat_spaceP)
            (fail "expecting colon (':')")

read_listP :: String -> Parser String
read_listP xs = liftP $ read_list xs
            
read_list :: (Show a, Eq a) => [a] -> Scanner a [a]
read_list xs = do
        x <- match (match_string xs) 
        case x of
            Just x -> return x
            Nothing -> fail ("expecting: " ++ show xs)
            
word_or_command = 
    read_ifP (== '\\')
            (\_ -> do
                xs <- word
                return ('\\':xs))
            word

type_t :: Parser Type
type_t = do
        t <- word_or_command
        eat_spaceP
        b1 <- liftHOF look_ahead $ read_listP "["
        ts <- if b1
            then do
                read_listP "["
                eat_spaceP
                ts <- sep1P type_t comma
                eat_spaceP
                read_listP "]"
                eat_spaceP
                return ts
            else return []
        ctx <- get_context
        t <- case get_type ctx t of
            Just s -> return $ USER_DEFINED s ts
            Nothing -> fail ("Invalid sort: '" ++ t ++ "'")
        b2 <- liftHOF look_ahead $ read_listP "\\pfun"
        if b2 
        then do
            read_listP "\\pfun"
            eat_spaceP
            t2 <- type_t
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

vars :: Parser [(String,Type)]
vars = do
        eat_spaceP
        vs <- sep1P word comma
        colon
        t <- type_t
        eat_spaceP       
        return (map (\x -> (x,t)) vs)     

get_variables :: (Monad m, MonadReader LineInfo m)
              => Context -> [LatexDoc] 
              -> EitherT [Error] m [(String, Var)]
get_variables ctx cs = do
        LI fn i j <- lift $ ask
        xs <- hoistEither $ read_tokens 
            (runParser ctx notations vars) 
            fn m (i,j)
        return $ map (\(x,y) -> (x,Var x y)) xs
    where
        m = concatMap flatten_li cs

unary :: Parser UnaryOperator
unary = choiceP
            (map f $ lefts $ new_ops notations)
            (fail "expecting an unary operator")            
            return
    where
        f op@(UnaryOperator _ tok _) = do
            read_listP tok
            return op

choiceP :: [Parser a] -> Parser a -> (a -> Parser a) -> Parser a
choiceP xs x final = do
        y <- get_context
        z <- get_notation
        liftP $ choice 
            (map (runParser y z) xs)
            (runParser y z x)
            (runParser y z . final)

oper :: Parser BinOperator
oper = do
        notations <- get_notation
        choiceP
            (map f $ rights $ new_ops notations)
            (fail "expecting a binary operator")            
            return
    where
        f op@(BinOperator _ tok _) = do
            read_listP tok
            return op

data FunOperator = Domain | Range
    deriving Show

apply_fun_op :: FunOperator -> Expr -> Parser Term
apply_fun_op fop x = liftP $
        case f fop $ Right x of
            Right e -> return $ Right e
            Left xs -> fail $ format "type error: {0}" xs
    where
        f Domain = zdom
        f Range  = zran

type Term = Either FunOperator Expr

term :: Parser Term
term = do
        eat_spaceP
        tryP word_or_command
            (\xs -> do
                (_,zs) <- liftP $ read_if (== '\'') 
                    (const $ return (\x -> x ++ "\'", \x -> x ++ "@prime"))
                    (return (id,id))
                eat_spaceP
                case xs `L.lookup` 
                        [ ("\\true",Right ztrue)
                        , ("\\false",Right zfalse)
                        , ("\\emptyset", Right zempty_set)
                        , ("\\emptyfun", Right zempty_fun) 
                        , ("\\dom", Left Domain)
                        , ("\\ran", Left Range) ] of
                    Just e  -> return e 
                    Nothing ->
                        if xs `elem` 
                            [ "\\qforall"
                            , "\\qexists"
                            , "\\qfun"
                            , "\\qset" ]
                        then do
                            eat_spaceP

                            read_listP "{"
                            eat_spaceP
                            vs <- sep1P word comma
                            eat_spaceP
                            read_listP "}"
                            eat_spaceP

                            read_listP "{"
                            eat_spaceP
                            r <- tryP (read_listP "}") 
                                (\_ -> return ztrue)
                                (do r <- expr
                                    read_listP "}"
                                    return r)
                            eat_spaceP
                            
                            read_listP "{"
                            eat_spaceP
                            t <- expr
                            eat_spaceP
                            read_listP "}"
                            eat_spaceP
                            let { quant = fromList 
                                [ ("\\qforall",Binder Forall)
                                , ("\\qexists",Binder Exists)
                                , ("\\qfun",Binder Lambda) 
                                , ("\\qset", \x y z -> fromJust $ zset (Right $ Binder Lambda x y z) ) ] ! xs }
                            ctx <- get_context
                            case dummy_types vs ctx of
                                Just vs -> return $ Right (quant vs r t)
                                Nothing -> fail ("bound variables are not typed")
                        else if xs == "\\oftype"
                        then do
                            eat_spaceP
                            read_listP "{"
                            eat_spaceP
                            e <- expr
                            eat_spaceP
                            read_listP "}"
                            eat_spaceP
                            read_listP "{"
                            eat_spaceP
                            t <- type_t
                            eat_spaceP
                            read_listP "}"
                            eat_spaceP
                            case zcast t (Right e) of
                                Right new_e -> return $ Right new_e
                                Left msg -> fail msg
                        else do
                            ctx <- get_context
                            case var_decl xs ctx of
                                Just (Var v t) -> return $ Right (Word $ Var (zs v) t) 
                                Nothing -> fail ("undeclared variable: " ++ xs))
            (do 
                xs <- number
                eat_spaceP
                return $ Right (Const [] xs $ USER_DEFINED IntSort []))

dummy_types vs (Context _ _ _ _ dums) = mapM f vs
    where
        f x = M.lookup x dums

number :: Parser String
number = liftP $ do
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

open_brack :: Parser String
open_brack  = read_listP "("

close_brack :: Parser String
close_brack = read_listP ")" 

open_curly :: Parser String
open_curly = read_listP "\\{"

close_curly :: Parser String
close_curly = read_listP "\\}"

tryP :: Parser a -> (a -> Parser b) -> Parser b -> Parser b
tryP m0 m1 m2 = do
        x <- get_context
        y <- get_notation
        liftP $ try 
            (runParser x y m0)
            (\z -> runParser x y (m1 z))
            (runParser x y m2)

sep1P :: Parser a -> Parser b -> Parser [a]
sep1P m0 m1 = do
        x <- get_context
        y <- get_notation
        liftP $ sep1 
            (runParser x y m0)
            (runParser x y m1)

expr :: Parser Expr
expr = do
        r <- read_term []
        case r of
            Right e -> return e
            Left op -> fail $ format "unused functional operator: {0}" op
    where
        read_term :: [([UnaryOperator], Term, BinOperator)] 
                  -> Parser Term
        read_term xs = do
            us <- liftHOF many (eat_spaceP >> unary)
            eat_spaceP
            tryP open_brack
                (\_ -> do
                        e <- expr
                        close_brack
                        eat_spaceP
                        read_op xs us (Right e)
                    ) $ (tryP open_curly 
                             (\_ -> do
                                rs <- sep1P expr comma
                                close_curly
                                eat_spaceP
                                case zset_enum $ map Right rs of
                                    Right e -> read_op xs us $ Right e 
                                    Left xs -> fail (format "type error: {0}" xs)
                            ) $ (do
                                t <- term
                                read_op xs us t))
        read_op :: [([UnaryOperator], Term, BinOperator)] 
                -> [UnaryOperator] 
                -> Term 
                -> Parser Term
        read_op xs us e0 = do
            b1 <- liftP $ is_eof
            b2 <- liftHOF look_ahead close_brack
            b3 <- liftHOF look_ahead close_curly
            b4 <- liftHOF look_ahead comma
            b5 <- liftHOF look_ahead (read_listP "}")
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
               -> Parser Term
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
                   -> Parser Term
        reduce_all [] [] e             = return e
        reduce_all ( (us,e0,op0):ys ) [] e1 = do
                e2 <- apply_op op0 e0 e1
                reduce_all ys us e2
        reduce_all xs (u:us) e0        = do
                e1 <- apply_unary u e0
                reduce_all xs us e1
                    

apply_unary :: UnaryOperator -> Term -> Parser Term
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
        
apply_op :: BinOperator -> Term -> Term -> Parser Term
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
           => Context 
           -> [(Char, LineInfo)] 
           -> EitherT [Error] m Expr
parse_expr ctx c = do
        li <- lift $ ask
        !e <- hoistEither $ read_tokens 
            (runParser ctx notations expr) 
            (file_name li) 
            c (line li, column li)
        ES.insert e (map fst c)
        return e

parse_oper :: ( Monad m
              , MonadReader LineInfo m) 
           => Context 
           -> [(Char, LineInfo)] 
           -> EitherT [Error] m BinOperator
parse_oper ctx c = do
        li <- lift $ ask
        !e <- hoistEither $ read_tokens 
            (runParser ctx notations 
                $ do eat_spaceP ; x <- oper ; eat_spaceP ; return x) 
            (file_name li) 
            c (line li, column li)
        return e
