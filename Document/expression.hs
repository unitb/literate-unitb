{-# LANGUAGE BangPatterns, FlexibleContexts, RecordWildCards #-}
module Document.Expression 
    ( parse_expr, oper
    , get_variables, parse_oper )
where

    -- Modules
import Latex.Scanner
import Latex.Parser hiding (Close,Open)

import Logic.Const
import Logic.Expr
import Logic.ExpressionStore as ES
import Logic.Genericity hiding ( variables )
import Logic.Operator
import Logic.Type

import UnitB.AST ( System ( .. ) )

import Theories.SetTheory
import Theories.FunctionTheory

import Utilities.Syntactic

    -- Libraries
import           Control.Monad
import           Control.Monad.Reader.Class
import           Control.Monad.State.Class
import           Control.Monad.Trans
import           Control.Monad.Trans.Either
import qualified Control.Monad.Trans.Reader as R

import Data.Char
import Data.Either
import Data.List as L
import Data.Map as M hiding ( map )
import Data.Monoid

import Utilities.Format
import Utilities.Graph as G ( (!) )

data Param = Param 
    { context :: Context
    , notation :: Notation
    , variables :: Map String Var
    }

data Parser a = Parser { fromParser :: (R.ReaderT Param (Scanner ExprToken) a) }

data Bracket = Curly | QuotedCurly | Round | Square
    deriving (Eq, Show)

data ExprToken = 
        Open Bracket 
        | Close Bracket 
        | Ident String 
        | Number String
        | Operator String
        | Comma | Colon
    deriving (Show, Eq)

instance Monad Parser where
    Parser m0 >>= f = Parser $ m0 >>= (fromParser . f)
    return x = Parser $ return x
    fail x   = Parser $ fail x

runParser :: Context -> Notation 
          -> Map String Var
          -> Parser a 
          -> Scanner ExprToken a
runParser x y w m = R.runReaderT (fromParser m) (Param x y w)

runParserWith :: Param -> Parser a -> Scanner ExprToken a
runParserWith x m = R.runReaderT (fromParser m) x

get_context :: Parser Context 
get_context = Parser $ R.asks context

get_notation :: Parser Notation
get_notation = Parser $ R.asks notation

get_table :: Parser (Matrix Operator Assoc)
get_table = Parser $ R.asks (struct . notation)

get_vars :: Parser (Map String Var)
get_vars = Parser $ R.asks variables

with_vars :: [(String, Var)] -> Parser b -> Parser b
with_vars vs cmd = do
        x <- get_params
        liftP $ runParserWith (f x) $ do
                cmd
    where
        f s@(Param { .. }) =
                s { variables = fromList vs `M.union` variables }

get_params :: Parser Param
get_params = Parser R.ask

liftP :: Scanner ExprToken a -> Parser a
liftP = Parser . lift

liftHOF :: (Scanner ExprToken a -> Scanner ExprToken b) -> Parser a -> Parser b
liftHOF f m = do
        x <- get_params
        liftP $ f $ runParserWith x m

match_char :: (a -> Bool) -> Scanner a a
match_char p = read_if p return (fail "")

-- eat_spaceP :: Parser ()
-- eat_spaceP = liftP $ eat_space

eat_space :: Scanner Char ()
eat_space = do
        b <- is_eof
        if b
        then return ()
        else choice 
                [ match_char isSpace >> return ()
                , read_list "\\\\" >> return ()
                , read_list "~" >> return ()
                , read_list "&" >> return ()
                , read_list "\\," >> return ()
                , read_list "\\:" >> return ()
                , read_list "\\;" >> return ()
                , read_list "\\!" >> return ()
                , read_list "\\quad" >> return ()
                , read_list "\\qquad" >> return ()
                , read_list "\\" >> match_char isDigit >> return ()
                ] (return ())
                (\_ -> eat_space)

isWord :: Char -> Bool
isWord x = isAlphaNum x || x == '_'

comma :: Parser ()
comma = read_listP [Comma] >> return ()

colon :: Parser ()
colon = read_listP [Colon] >> return ()

read_listP :: [ExprToken] -> Parser [ExprToken]
read_listP xs = liftP $ read_list xs

read_list :: (Show a, Eq a) => [a] -> Scanner a [a]
read_list xs = do
        x <- match (match_string xs) 
        case x of
            Just x -> return x
            Nothing -> fail ("expecting: " ++ show xs)

brackets :: Bracket -> Parser a -> Parser a
brackets b cmd = do
        read_listP [Open b]
        x <- cmd
        read_listP [Close b]
        return x

word_or_command :: Parser String            
word_or_command = do
    x <- liftP read_char
    case x of
        Ident xs -> return xs
        _ -> fail "expecting an identifier"

type_t :: Parser Type
type_t = do
        t  <- word_or_command
        b1 <- liftHOF look_ahead $ read_listP [Open Square]
        ts <- if b1
            then do
                read_listP [Open Square]
                ts <- sep1P type_t comma
                read_listP [Close Square]
                return ts
            else return []
        ctx <- get_context
        t <- case get_type ctx t of
            Just s -> return $ Gen (USER_DEFINED s ts)
            Nothing -> fail ("Invalid sort: '" ++ t ++ "'")
        b2 <- liftHOF look_ahead $ read_listP [ Ident "\\pfun" ]               
        if b2 
        then do
            maybe 
                (fail $ "Invalid sort: '\\pfun'")
                return
                $ get_type ctx "\\pfun"
            read_listP [Ident "\\pfun"]
            t2 <- type_t
            t  <- return $ fun_type t t2
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
        vs <- sep1P word_or_command comma
        colon
        t <- type_t
        return (map (\x -> (x,t)) vs)     

get_variables :: (Monad m, MonadReader LineInfo m)
              => Context -> Notation
              -> [LatexDoc] 
              -> EitherT [Error] m [(String, Var)]
get_variables ctx n cs = do
        LI fn i j <- lift $ ask
        toks <- hoistEither $ read_tokens 
            (scan_expr n) fn m (i,j)
        xs   <- hoistEither $ read_tokens 
            (runParser ctx n M.empty vars) 
            fn toks (i,j)
        return $ map (\(x,y) -> (x,Var x y)) xs
    where
        m = concatMap flatten_li cs

unary :: Parser UnaryOperator
unary = do
        n <- get_notation
        choiceP
            (map f $ lefts $ new_ops n)
            (fail "expecting an unary operator")            
            return
    where
        f op@(UnaryOperator _ tok _) = do
            read_listP [Operator tok]
            return op

choiceP :: [Parser a] -> Parser a -> (a -> Parser a) -> Parser a
choiceP xs x final = do
        y <- get_params
        liftP $ choice 
            (map (runParserWith y) xs)
            (runParserWith y x)
            (runParserWith y . final)

oper :: Parser BinOperator
oper = do
        n <- get_notation
        choiceP
            (map f $ rights $ new_ops n)
            (do
                xs <- liftP peek
                fail $ "expecting a binary operator, read: " ++ show (take 1 xs))            
            return
    where
        f op@(BinOperator _ tok _) = do
            read_listP [Operator tok]
            return op

data FunOperator = Domain | Range
    deriving Show

check_types :: ExprP -> Parser Expr
check_types e = 
        case e of
            Right e -> return e
            Left xs -> fail $ format "type error: {0}" xs

apply_fun_op :: FunOperator -> Expr -> Parser Term
apply_fun_op fop x = do
        e <- check_types $ f fop $ Right x
        return $ Right e
    where
        f Domain = zdom
        f Range  = zran

type Term = Either FunOperator Expr

primed :: String -> Bool
primed xs = drop (length xs - 1) xs == "'"

unprimed :: String -> String
unprimed xs
    | primed xs = take (length xs - 1) xs
    | otherwise = xs

term :: Parser Term
term = do
        tryP word_or_command
            (\xs' -> add_context xs' $ do 
                let xs = unprimed xs'
                prime <- if primed xs' then 
                    return "@prime"
                else
                    return ""
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
                            ns <- brackets Curly
                                $ sep1P word_or_command comma

                            ctx <- get_context
                            vs  <- case dummy_types ns ctx of
                                Just vs -> return vs
                                Nothing -> fail ("bound variables are not typed")
                            with_vars (zip ns vs) $ do
                                read_listP [Open Curly]
                                r <- tryP (read_listP [Close Curly]) 
                                    (\_ -> return ztrue)
                                    (do r <- expr
                                        read_listP [Close Curly]
                                        return r)
                                
                                t <- brackets Curly 
                                    expr
                                let { quant = fromList 
                                    [ ("\\qforall",Binder Forall)
                                    , ("\\qexists",Binder Exists)
                                    , ("\\qfun",Binder Lambda) 
                                    , ("\\qset", \x y z -> fromJust $ zset (Right $ Binder Lambda x y z) ) ] M.! xs }
                                return $ Right (quant vs r t)
                        else if xs == "\\ew"
                        then do
                            e <- brackets Curly expr
                            e <- check_types $ zeverywhere $ Right e
                            return $ Right e
                        else if xs == "\\oftype"
                        then do
                            e <- brackets Curly expr
                            t <- brackets Curly type_t
                            case zcast t (Right e) of
                                Right new_e -> return $ Right new_e
                                Left msg -> fail msg
                        else do
                            vs <- get_vars
                            case M.lookup xs vs of
                                Just (Var v t) -> return $ Right (Word $ Var (v ++ prime) t) 
                                Nothing -> fail ("undeclared variable: " ++ xs))
            (do 
                xs <- number
                return $ Right (Const [] xs int))

dummy_types :: [String] -> Context -> Maybe [Var]
dummy_types vs (Context _ _ _ _ dums) = mapM f vs
    where
        f x = M.lookup x dums

number :: Parser String
number = liftP $ do
            x <- read_char 
            case x of
                Number xs -> return xs
                _ -> fail "expecting a number"
                
open_brack :: Parser [ExprToken]
open_brack  = read_listP [Open Round]

close_brack :: Parser [ExprToken]
close_brack = read_listP [Close Round]

open_curly :: Parser [ExprToken]
open_curly = read_listP [Open QuotedCurly]

close_curly :: Parser [ExprToken]
close_curly = read_listP [Close QuotedCurly]

tryP :: Parser a -> (a -> Parser b) -> Parser b -> Parser b
tryP m0 m1 m2 = do
        x <- get_params
        liftP $ try 
            (runParserWith x m0)
            (\k -> runParserWith x (m1 k))
            (runParserWith x m2)

sep1P :: Parser a -> Parser b -> Parser [a]
sep1P m0 m1 = do
        x <- get_params
        liftP $ sep1 
            (runParserWith x m0)
            (runParserWith x m1)

choose_la :: [(Parser b, Parser a)] -> Parser a -> Parser a
choose_la ((x,y):xs) cmd = do
        tryP x (const y) $ choose_la xs cmd
choose_la [] cmd = cmd

add_context :: String -> Parser a -> Parser a
-- add_context msg cmd = do
    -- li <- liftP $ get_line_info
    -- let e = Error msg li
    -- liftHOF (change_errors (e:)) cmd
add_context _ cmd = cmd
            
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
            us <- liftHOF many unary
            choose_la 
                [ (     open_brack
                  , do  e <- expr
                        close_brack
                        add_context "parsing (" $
                            read_op xs us (Right e) )
                , (     open_curly
                  , do  rs <- sep1P expr comma
                        close_curly
                        e <- check_types $ zset_enum $ map Right rs
                        add_context "parsing \\{" $
                            read_op xs us $ Right e ) ]
                (   add_context ("ready for <term>: " ++ show xs) $
                    do  t <- term
                        add_context ("parsed <term>: " ++ show t) $
                            read_op xs us t)
        read_op :: [([UnaryOperator], Term, BinOperator)] 
                -> [UnaryOperator] 
                -> Term 
                -> Parser Term
        read_op xs us e0 = do
            b1 <- liftP $ is_eof
            b2 <- liftHOF look_ahead close_brack
            b3 <- liftHOF look_ahead close_curly
            b4 <- liftHOF look_ahead comma
            b5 <- liftHOF look_ahead (read_listP [Close Curly])
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
            r <- assoc op0 op1
            case r of
                LeftAssoc ->  do
                    e2 <- apply_op op0 e0 e1
                    reduce ys vs e2 op1
                RightAssoc -> read_term (([],e1,op1):xs)
                Ambiguous ->  fail $ format "ambiguous expression: '{0}' and '{1}' are not associative" op0 op1
        reduce xs (u:us) e0 op0             = do
            r <- binds u op0
            case r of
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
                    
assoc :: BinOperator -> BinOperator -> Parser Assoc
assoc x0 x1 = do
        tb <- get_table
        return $ tb G.! (Right x0, Right x1)

binds :: UnaryOperator -> BinOperator -> Parser Assoc
binds x0 x1 = do
        tb <- get_table
        return $ tb G.! (Left x0, Right x1)

apply_unary :: UnaryOperator -> Term -> Parser Term
apply_unary op e = do
        case e of 
            Right e -> do
                x2 <- check_types $ mk_unary op e
                return $ Right x2
            Left oper -> fail $ format 
                    err_msg oper op
    where
        err_msg = "functional operator cannot be the operand of any unary operator: {0}, {1}"
        
apply_op :: BinOperator -> Term -> Term -> Parser Term
apply_op op x0 x1 = do
        case x1 of
            Right e1 -> do
                case x0 of
                    Right e0 -> do
                        e2 <- check_types $ mk_expr op e0 e1
                        return $ Right e2
                    Left oper ->
                        if op == apply then
                            apply_fun_op oper e1
                        else fail $ format err_msg oper op
            Left e1 -> 
                fail $ format err_msg e1 op
    where
        err_msg = "functional operator cannot be the operand of any binary operator: {0}, {1}"

option :: Monoid b => Scanner a b -> Scanner a b
option cmd = do
        try cmd
            return
            (return mempty)
        
scan_expr :: Notation -> Scanner Char [(ExprToken,LineInfo)] 
scan_expr n = do
        eat_space
        b <- is_eof
        if not b then do
            li <- get_line_info
            x  <- choice 
                [ read_list "{" >> return (Open Curly)
                , read_list "[" >> return (Open Square)
                , read_list "(" >> return (Open Round)
                , read_list "\\{" >> return (Open QuotedCurly)
                , read_list "}" >> return (Close Curly)
                , read_list "]" >> return (Close Square)
                , read_list ")" >> return (Close Round)
                , read_list "\\}" >> return (Close QuotedCurly)
                , read_list ":" >> return Colon
                , read_list "," >> return Comma
                , match_char (`elem` ['.',';']) >>= \x -> return $ Operator [x]
                , match_char isSymbol >>= \x -> return $ Operator [x]
                , do
                    ws <- option $ read_list "\\"
                    x  <- match_char isAlpha
                    xs <- many $ match_char isWord
                    ys <- option $ read_list "\'"
                    let zs = ws ++ x : xs ++ ys
                    if zs `elem` map f (new_ops n)
                        then return $ Operator zs
                        else return $ Ident zs
                , do
                    x  <- match_char isDigit
                    xs <- many $ match_char isDigit
                    ys <- peek
                    when (any isWord $ take 1 ys) $ 
                        fail ""
                        -- return ()
                    return $ Number $ x : xs ]
                (do 
                    cs <- peek
                    fail $ "invalid token: '" ++ take 5 cs ++ "'")
                return
            xs <- scan_expr n
            return $ (x,li) : xs
        else return []
    where
        f (Right (BinOperator _ tok _)) = tok
        f (Left (UnaryOperator _ tok _)) = tok

    -- Too many arguments
parse_expr :: ( Monad m
              , MonadReader LineInfo m
              , MonadState System m) 
           => Context 
           -> Notation
           -> [(Char, LineInfo)] 
           -> EitherT [Error] m Expr
parse_expr ctx@(Context _ vars _ _ _)  n input = do
        li <- lift $ ask
        toks <- hoistEither $ read_tokens (scan_expr n)
            (file_name li) 
            input (line li, column li)
        !e <- hoistEither $ read_tokens 
            (runParser ctx n vars expr) 
            (file_name li) 
            toks 
            (line li, column li)
        es <- gets expr_store
        modify $ \s -> s 
            { expr_store = ES.insert e (map fst input) es }
        return e

parse_oper :: ( Monad m
              , MonadReader LineInfo m) 
           => Notation
           -> [(Char, LineInfo)] 
           -> EitherT [Error] m BinOperator
parse_oper n c = do
        li   <- lift $ ask
        toks <- hoistEither $ read_tokens (scan_expr n)
            (file_name li) 
            c (line li, column li)
        !e   <- hoistEither $ read_tokens 
            (runParser empty_ctx n M.empty
                oper) 
            (file_name li) 
            toks (line li, column li)
        return e
