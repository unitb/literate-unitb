{-# LANGUAGE BangPatterns, FlexibleContexts         #-}
{-# LANGUAGE RecordWildCards, FlexibleInstances     #-}
{-# LANGUAGE OverlappingInstances, TemplateHaskell  #-}
module Document.Expression 
    ( parse_expr, parse_expr' , oper, run_test
    , get_variables, get_variables', parse_oper )
where

    -- Modules
import Latex.Scanner -- hiding (many)
import Latex.Parser  hiding (Close,Open,Command)

import Logic.Expr
import Logic.ExpressionStore as ES
import Logic.Operator

import UnitB.AST ( System ( .. ) )

import Theories.SetTheory
import Theories.FunctionTheory

import Utilities.Error
import Utilities.Syntactic
--import Utilities.Trace

    -- Libraries
import qualified Control.Applicative as A 

import           Control.Monad
import           Control.Monad.Reader.Class
import           Control.Monad.State.Class
import           Control.Monad.Trans
import           Control.Monad.Trans.Either
import           Control.Monad.Trans.Maybe
import qualified Control.Monad.Trans.Reader as R

import           Data.Char
import           Data.Either
import           Data.List as L
import           Data.Map as M hiding ( map )
import qualified Data.Map as M
import           Data.Monoid
import qualified Data.Set as S

import Utilities.Format
import Utilities.Graph as G ( (!) )
import Utilities.EditDistance

data Param = Param 
    { context :: Context
    , notation :: Notation
    , variables :: Map String Expr
    }

data Parser a = Parser { fromParser :: MaybeT (R.ReaderT Param (Scanner ExprToken)) a }

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

instance Functor Parser where
    fmap = liftM

instance A.Applicative Parser where
    f <*> x = f `ap` x
    pure = return

instance A.Alternative Parser where
    m0 <|> m1 = m0 `mplus` m1
    empty     = mzero

instance Monad Parser where
    Parser m0 >>= f = Parser $ m0 >>= (fromParser . f)
    return x = Parser $ return x
    fail x   = Parser $ lift $ fail x

instance MonadPlus Parser where
    Parser m0 `mplus` Parser m1 = Parser $ m0 `mplus` m1
    mzero = Parser mzero
    
runParser :: Context -> Notation 
          -> Map String Expr
          -> Parser a 
          -> Scanner ExprToken a
runParser x y w m = runParserWith (Param x y w) m

runParserWith :: Param -> Parser a -> Scanner ExprToken a
runParserWith x m = do
        x <- R.runReaderT (runMaybeT $ fromParser m) x
        maybe (fail "runParserWith: unmatched lookahead") return x

get_context :: Parser Context 
get_context = context `liftM` get_params

get_notation :: Parser Notation
get_notation = notation `liftM` get_params

get_table :: Parser (Matrix Operator Assoc)
get_table = (struct . notation) `liftM` get_params

get_vars :: Parser (Map String Expr)
get_vars = variables `liftM` get_params

with_vars :: [(String, Var)] -> Parser b -> Parser b
with_vars vs cmd = do
        x <- get_params
        liftP $ runParserWith (f x) $ do
                cmd
    where
        f s@(Param { .. }) =
                s { variables = M.map Word (fromList vs) `M.union` variables }

get_params :: Parser Param
get_params = Parser $ lift R.ask

look_aheadP :: Parser a -> Parser Bool
look_aheadP = liftHOF look_ahead

liftP :: Scanner ExprToken a -> Parser a
liftP = Parser . lift . lift

-- many :: Parser a -> Parser [a]
-- many m = do

liftHOF :: (   Scanner ExprToken a
            -> Scanner ExprToken b )
        -> Parser a -> Parser b
liftHOF f m = do
        x <- get_params
        liftP $ f $ runParserWith x m

tryP :: Parser a -> (a -> Parser b) -> Parser b -> Parser b
tryP m0 m1 m2 = do
        x <- get_params
        let run m = R.runReaderT (runMaybeT $ fromParser m) x
        Parser $ MaybeT $ R.ReaderT $ const $ try 
            (run m0) 
            (\k -> case k of
                    Just x  -> run $ m1 x
                    Nothing -> run m2)
            (run m2)

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
        b1 <- look_aheadP $ read_listP [Open Square]
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
        b2 <- look_aheadP $ read_listP [ Ident "\\pfun" ]               
        if b2 
        then do
            maybe 
                (fail $ "Invalid sort: '\\pfun'")
                return
                $ get_type ctx "\\pfun"
            read_listP [Ident "\\pfun"]
            t2 <- type_t
            return $ fun_type t t2
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
        t  <- type_t
        return (map (\x -> (x,t)) vs)     

get_variables' :: (Monad m, MonadReader LineInfo m)
               => Map String Sort
               -> [LatexDoc] 
               -> EitherT [Error] m [(String, Var)]
get_variables' types cs = 
        get_variables 
            (Context types M.empty 
                M.empty M.empty M.empty)
            cs

get_variables :: (Monad m, MonadReader LineInfo m)
              => Context
              -> [LatexDoc] 
              -> EitherT [Error] m [(String, Var)]
get_variables ctx cs = do
        LI fn i j <- lift $ ask
        toks <- hoistEither $ read_tokens 
            (scan_expr Nothing) fn m (i,j)
        xs   <- hoistEither $ read_tokens 
            (runParser ctx
                ($myError) M.empty vars) 
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
                fail $ "expecting a binary operator, read: " 
                    ++ show (take 1 xs))            
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
            Left xs -> fail $ format "type error: {0}" $ intercalate "\n" xs

apply_fun_op :: Command -> Expr -> Parser Term
apply_fun_op (Command _ _ _ fop) x = do
        e <- check_types $ fop [Right x]
        return $ Right e

suggestion :: String -> Map String String -> [String]
suggestion xs m = map (\(x,y) -> x ++ " (" ++ y ++ ")") $ toList ws
  where
    xs' = map toLower xs
    p ys _ = 2 * dist xs' ys' <= (length xs' `max` length ys') + 1
      where
        ys' = map toLower ys
    ws = M.filterWithKey p m

type Term = Either Command Expr

term :: Parser Term
term = do
    n <- get_notation
    let cmds = zip (map token (commands n)) (commands n)
        quants = [ ("\\qforall",Binder Forall)
                 , ("\\qexists",Binder Exists)
                 , ("\\qfun",Binder Lambda) 
                 , ("\\qset", \x y z -> fromJust $ zset (Right $ Binder Lambda x y z) ) ]
        oftype = [("\\oftype",())]
    choose_la 
        [ do    c@(Command _ _ n f) <- from cmds
                if n == 1 then do
                    tryP (read_listP [Open Curly])
                        (\_ -> do
                            e <- expr
                            read_listP [Close Curly]
                            e <- check_types $ f [Right e]
                            return $ Right e)
                        (return $ Left c)
                else do
                    args <-replicateM n $
                        brackets Curly expr
                    e <- check_types $ f $ map Right args
                    return $ Right e
        , do    quant <- from quants 
                ns <- brackets Curly
                    $ sep1P word_or_command comma
                ctx <- get_context
                let vs = dummy_types ns ctx
                with_vars (zip ns vs) $ do
                    read_listP [Open Curly]
                    r <- tryP (read_listP [Close Curly]) 
                        (\_ -> return ztrue)
                        (do r <- expr
                            read_listP [Close Curly]
                            return r)
                    t <- brackets Curly expr
                    let vars = used_var r `S.union` used_var t
                        v_type = id -- L.filter ((1 <) . S.size . snd) 
                                    $ zip3 ns vs
                                    $ map f ns 
                        f = (`S.filter` vars) . (. name) . (==)
                    ts <- forM v_type $ \(x,(Var _ t),xs) -> do
                        let ys = L.map (type_of . Word) $ S.toList xs
                        t' <- maybe 
                            (fail $ format "Inconsistent type for {0}: {1}" 
                                    x
                                    $ intercalate "," $ map show ys)
                            return
                            $ foldM common gA ys
                        t' <- if t' == gA 
                            then return t
                            else return t'
                        return (x, Var x t')
                    let ts' = M.map Word $ fromList ts
                        r' = substitute ts' r
                        t' = substitute ts' t
                        vs' = map snd ts
                    return $ Right (quant vs' r' t')
        , do    from oftype
                e <- brackets Curly expr
                t <- brackets Curly type_t
                case zcast t (Right e) of
                    Right new_e -> return $ Right new_e
                    Left msg -> fail $ unlines msg
        , attempt $ do    
                xs' <- word_or_command
                vs <- get_vars
                case M.lookup xs' vs of
                    Just e -> return $ Right e
                    Nothing -> fail ""
        , do    xs <- attempt word_or_command
                vs <- get_vars
                let oftype' = M.map (const "keyword")  $ fromList oftype
                    quants' = M.map (const "quantifier") $ fromList quants
                    cmd'    = M.map (const "command")  $ fromList cmds
                    vars'   = M.map (const "variable") $ vs
                    sug     = suggestion xs $ M.unions 
                            [ cmd', quants'
                            , oftype', vars' ]
                fail (   "unrecognized term: "
                      ++ xs ++ if not $ L.null sug then
                            "\nPerhaps you meant:\n"
                      ++ unlines sug else "")
        , do    xs <- number
                return $ Right $ zint $ read xs
        ]

dummy_types :: [String] -> Context -> [Var]
dummy_types vs (Context _ _ _ _ dums) = map f vs
    where
        f x = maybe (Var x gA) id $ M.lookup x dums

number :: Parser String
number = liftP $ do
            x <- read_char 
            case x of
                Number xs -> return xs
                _ -> fail $ "expecting a number: " ++ show x
                
open_brack :: Parser [ExprToken]
open_brack  = read_listP [Open Round]

close_brack :: Parser [ExprToken]
close_brack = read_listP [Close Round]

open_curly :: Parser [ExprToken]
open_curly = read_listP [Open QuotedCurly]

close_curly :: Parser [ExprToken]
close_curly = read_listP [Close QuotedCurly]

sep1P :: Parser a -> Parser b -> Parser [a]
sep1P m0 m1 = do
        x <- get_params
        liftP $ sep1 
            (runParserWith x m0)
            (runParserWith x m1)

choose_la :: [Parser a] -> Parser a
choose_la (x:xs) = do
        x `mplus` choose_la xs
choose_la [] = mzero

add_context :: String -> Parser a -> Parser a
--add_context msg cmd = do       
--    li <- liftP $ get_line_info
--    let e = Error msg li
--    liftHOF (change_errors (e:)) cmd
add_context _ cmd = cmd

from :: [(String,a)] -> Parser a
from m = attempt $ do
        x <- word_or_command
        case x `L.lookup` m of
                Nothing -> fail ""
                Just x  -> return x

attempt :: Parser a -> Parser a
attempt cmd = do
        tryP cmd 
            return 
            (Parser $ fail (error "Expression.attempt: shouldn't be evaluated"))
            
expr :: Parser Expr
expr = do
        r <- read_term []
        case r of
            Right e -> return e
            Left op -> fail $ format "unapplied functional operator: {0}" op
    where
        read_term :: [([UnaryOperator], Term, BinOperator)] 
                  -> Parser Term
        read_term xs = do
            us <- liftHOF many unary
            choose_la 
                [ do    attempt open_brack
                        e <- expr
                        close_brack
                        add_context "parsing (" $
                            read_op xs us (Right e) 
                , do    attempt open_curly
                        rs <- sep1P expr comma
                        close_curly
                        e <- check_types $ zset_enum $ map Right rs
                        add_context "parsing \\{" $
                            read_op xs us $ Right e 
                ,   add_context ("ready for <term>: " ++ show xs) $
                        do  t <- term
                            add_context ("parsed <term>: " ++ show t) $
                                read_op xs us t
                ]
        read_op :: [([UnaryOperator], Term, BinOperator)] 
                -> [UnaryOperator] 
                -> Term 
                -> Parser Term
        read_op xs us e0 = do
            b1 <- liftP $ is_eof
            b2 <- look_aheadP close_brack
            b3 <- look_aheadP close_curly
            b4 <- look_aheadP comma
            b5 <- look_aheadP (read_listP [Close Curly])
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
        
scan_expr :: Maybe Notation -> Scanner Char [(ExprToken,LineInfo)] 
scan_expr n = do
        eat_space
        ys <- peek
        b  <- is_eof
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
                , do
                    ws <- option $ read_list "\\"
                    x  <- match_char isAlpha
                    xs <- many $ match_char isWord
                    ys <- option $ read_list "\'"
                    let zs = ws ++ x : xs ++ ys
                    if isOper n zs
                        then return $ Operator zs
                        else return $ Ident zs
                , match_char isSymbol >>= \x -> return $ Operator [x]
                , match_char isPunctuation >>= \x -> return $ Operator [x]
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
                    let b  = take 5 ys == take 5 cs 
                        zs
                            | b         = ""
                            | otherwise = format " '{0}'" (take 5 ys)
                    fail $ format "invalid token: '{0}'{1}" (take 5 cs) zs)
                return
            xs <- scan_expr n
            return $ (x,li) : xs
        else return []
    where
        isOper (Just n) zs = zs `elem` map f (new_ops n)
        isOper Nothing _ = False
        f (Right (BinOperator _ tok _)) = tok
        f (Left (UnaryOperator _ tok _)) = tok

parse_expr' :: ( Monad m
               , MonadReader LineInfo m ) 
            => Context 
            -> Notation
            -> [(Char, LineInfo)] 
            -> EitherT [Error] m Expr
parse_expr' ctx@(Context _ vars _ defs _)  n input = do
        let vars' = M.map Word vars `M.union` M.mapMaybe f defs
            f (Def xs n args t _e) = do
                    guard (L.null args)
                    Just $ FunApp (Fun xs n [] t) []
        li   <- lift $ ask
        toks <- hoistEither $ read_tokens (scan_expr $ Just n)
            (file_name li) 
            input (line li, column li)
        !e   <- hoistEither $ read_tokens 
            (runParser ctx n vars' expr) 
            (file_name li) 
            toks 
            (line li, column li)
        return e

    -- Too many arguments
parse_expr :: ( Monad m
              , MonadReader LineInfo m
              , MonadState System m) 
           => Context 
           -> Notation
           -> [(Char, LineInfo)] 
           -> EitherT [Error] m Expr
parse_expr ctx n input = do
        e  <- parse_expr' ctx n input
        es <- lift $ gets expr_store
        lift $ modify $ \s -> s 
            { expr_store = ES.insert e (map fst input) es }
        return e

parse_oper :: ( Monad m
              , MonadReader LineInfo m) 
           => Notation
           -> [(Char, LineInfo)] 
           -> EitherT [Error] m BinOperator
parse_oper n c = do
        li   <- lift $ ask
        toks <- hoistEither $ read_tokens (scan_expr $ Just n)
            (file_name li) 
            c (line li, column li)
        !e   <- hoistEither $ read_tokens 
            (runParser empty_ctx n M.empty
                oper) 
            (file_name li) 
            toks (line li, column li)
        return e
