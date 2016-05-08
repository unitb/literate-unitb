{-# LANGUAGE BangPatterns         #-}
{-# LANGUAGE RecordWildCards      #-}
module Logic.Expr.Parser.Internal.Parser where

    -- Modules
import Latex.Scanner -- hiding (many)
import Latex.Parser  hiding (Close,Open,BracketType(..),Command,Parser,Bracket,token)

import Logic.Expr
import Logic.Expr.Parser.Internal.Setting hiding (with_vars)
import Logic.Expr.Printable
import Logic.Operator


import Logic.Theories.SetTheory

import Utilities.Error
import Utilities.Syntactic

    -- Libraries
import qualified Control.Applicative as A 
import Control.Lens hiding (Context,from)

import           Control.Monad
import           Control.Monad.Trans
import           Control.Monad.Trans.Either
import           Control.Monad.Trans.Maybe
import qualified Control.Monad.Trans.Reader as R

import           Data.Char
import           Data.Either
import           Data.Either.Combinators
import           Data.List as L
import           Data.Map.Class as M hiding ( map, (!) )
import qualified Data.Map.Class as M
import qualified Data.Set as S

import Text.Printf.TH

import Utilities.EditDistance
import Utilities.Graph as G ((!))
import Utilities.Table

data Param = Param 
    { context   :: Context
    , notation  :: Notation
    , variables :: Table Name Expr
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
    
instance IsBracket Bracket String where
    bracketPair Curly  = ("{","}")
    bracketPair QuotedCurly = ("\\{","\\}")
    bracketPair Round  = ("(",")")
    bracketPair Square = ("[","]")

instance Token ExprToken where
    lexeme (Open b)   = openBracket b
    lexeme (Close b)  = closeBracket b
    lexeme (Ident n)  = n
    lexeme (Number n) = n
    lexeme (Operator op) = op
    lexeme Comma      = ","
    lexeme Colon      = ":"

runParser :: Context -> Notation 
          -> Table Name Expr
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
get_table = (view struct . notation) <$> get_params

get_vars :: Parser (Table Name Expr)
get_vars = variables `liftM` get_params

with_vars :: [(Name, Var)] -> Parser b -> Parser b
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

match_char :: Token a => (a -> Bool) -> Scanner a a
match_char p = read_if p return (fail "")

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

read_list :: (Token a, Show a, Eq a) => [a] -> Scanner a [a]
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

operator :: Parser Name
operator = do
    x <- liftP read_char
    case x of
        Operator n -> return $ fromString'' n
        _ -> fail "expecting an operator"

word_or_command :: Parser Name
word_or_command = do
    x <- liftP read_char
    case x of
        Ident xs -> return $ fromString'' xs
        _ -> fail "expecting an identifier"

type_t :: Parser Type
type_t = do
        t  <- choiceP 
            [ word_or_command
            , operator ]
            (fail "expecting word or command") 
            return
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
            Just s -> do
                unless (length ts == typeParams s)
                    $ fail $ [printf|Parameter mismatch. Expecting %d type parameters, received %d.|] 
                        (typeParams s) 
                        (length ts)
                return $ Gen s ts
            Nothing -> fail ("Invalid sort: '" ++ render t ++ "'")
        b2 <- look_aheadP $ read_listP [ Ident "\\pfun" ]               
        if b2 
        then do
            maybe 
                (fail $ "Invalid sort: '\\pfun'")
                return
                $ get_type ctx $ fromString'' "\\pfun"
            read_listP [Ident "\\pfun"]
            t2 <- type_t
            return $ fun_type t t2
        else return t

get_type :: Context -> Name -> Maybe Sort
get_type (Context ts _ _ _ _) x = M.lookup x m
    where
        m = fromList 
                   [ ([tex|\Int|], IntSort)
                   , ([tex|\Real|], RealSort)
                   , ([tex|\Bool|], BoolSort)]
            `M.union` ts
--        z3_type s@(Sort _ x _) = USER_DEFINED s

vars :: Parser [(Name,Type)]
vars = do
        vs <- sep1P word_or_command comma
        colon
        t  <- type_t
        return (map (\x -> (x,t)) vs)     

get_variables' :: Table Name Sort
               -> LatexDoc
               -> LineInfo
               -> Either [Error] [(Name, Var)]
get_variables' types cs = 
        get_variables 
            (Context types M.empty 
                M.empty M.empty M.empty)
            cs

get_variables :: Context
              -> LatexDoc
              -> LineInfo
              -> Either [Error] [(Name, Var)]
get_variables ctx = get_variables'' ctx . flatten_li'

get_variables'' :: Context
                -> StringLi
                -> LineInfo
                -> Either [Error] [(Name, Var)]
get_variables'' ctx m (LI fn i j) = do
        toks <- read_tokens 
            (scan_expr Nothing) fn (getString m) (i,j)
        xs   <- read_tokens 
            (runParser ctx
                ($myError "") M.empty vars) 
            fn toks (i,j)
        return $ map (\(x,y) -> (x,Var x y)) xs

unary :: Parser UnaryOperator
unary = do
        n <- get_notation
        choiceP
            (map f $ lefts $ n^.new_ops)
            (fail "expecting an unary operator")            
            return
    where
        f op@(UnaryOperator _ tok _) = do
            read_listP [Operator $ render tok]
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
            (map f $ rights $ n^.new_ops)
            (do
                xs <- liftP peek
                fail $ "expecting a binary operator, read: " 
                    ++ show (take 1 xs))            
            return
    where
        f op@(BinOperator _ tok _ _) = do
            read_listP [Operator $ render tok]
            return op

data FunOperator = Domain | Range
    deriving Show

check_types :: ExprP -> Parser Expr
check_types e = 
        case e of
            Right e -> return e
            Left xs -> fail $ [printf|type error: %s|] $ intercalate "\n" xs

apply_fun_op :: Command -> Expr -> Parser Term
apply_fun_op (Command _ _ _ fop) x = do
        e <- check_types $ typ_fun1 fop (Right x)
        return $ Right e

suggestion :: Name -> Table Name String -> [String]
suggestion xs m = map (\(x,y) -> render x ++ " (" ++ y ++ ")") $ toAscList ws
  where
    xs' = map toLower $ render xs
    p ys _ = 2 * dist xs' ys' <= (length xs' `max` length ys') + 1
      where
        ys' = map toLower $ render ys
    ws = M.filterWithKey p m

type Term = Either Command Expr

term :: Parser Term
term = do
    n <- get_notation
    let cmds = zip (map token (n^.commands)) (n^.commands)
        quants = n^.quantifiers
        oftype = [([tex|\oftype|],())]
    choose_la 
        [ do    c@(Command _ _ n f) <- from cmds
                if n == 1 then do
                    tryP (read_listP [Open Curly])
                        (\_ -> do
                            e <- expr
                            read_listP [Close Curly]
                            e <- check_types $ typ_fun1 f (Right e)
                            return $ Right e)
                        (return $ Left c)
                else do
                    args <- replicateM n $
                        brackets Curly expr
                    e <- check_types $ check_type f (map Right args)
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
                        f = (`S.filter` vars) . (. view name) . (==)
                    ts <- forM v_type $ \(x,(Var x' t),xs) -> do
                        let ys = L.map var_type $ S.toList xs
                        t' <- maybe 
                            (fail $ [printf|Inconsistent type for %s: %s|] 
                                    (render x)
                                    $ intercalate "," $ map show ys)
                            return
                            $ foldM common gA ys
                        t' <- if t' == gA 
                            then return t
                            else return t'
                        return (x, Var x' t')
                    let ts' = M.map Word $ fromList ts
                        r' = substitute ts' r
                        t' = substitute ts' t
                        vs' = map snd ts
                    Right <$> check_types (zquantifier quant vs' (Right r') (Right t'))
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
                let oftype' = "keyword"  <$ fromList oftype
                    quants' = "quantifier" <$ fromList quants
                    cmd'    = "command"  <$ fromList cmds
                    vars'   = "variable" <$ vs
                    sug     = suggestion xs $ M.unions 
                            [ cmd', quants'
                            , oftype', vars' ]
                fail (   "unrecognized term: "
                      ++ render xs ++ if not $ L.null sug then
                            "\nPerhaps you meant:\n"
                      ++ unlines sug else "")
        , do    xs <- number
                return $ Right $ zint $ read xs
        ]

dummy_types :: [Name] -> Context -> [Var]
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
add_context _ cmd = cmd

from :: [(Name,a)] -> Parser a
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
            Left op -> fail $ [printf|unapplied functional operator: %s|] (pretty op)
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
                NoAssoc ->  fail $ [printf|ambiguous expression: '%s' and '%s' are not associative|] (pretty op0) (pretty op1)
        reduce xs (u:us) e0 op0 = do
            r <- binds u op0
            case r of
                LeftAssoc   -> do
                    e1 <- apply_unary u e0
                    reduce xs us e1 op0
                RightAssoc  -> read_term ((u:us,e0,op0):xs)
                NoAssoc   -> fail ("ambiguous expression: use parentheses")
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
            Left oper -> fail $ err_msg (pretty oper) (pretty op)
    where
        err_msg = [printf|functional operator cannot be the operand of any unary operator: %s, %s|]
        
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
                        else fail $ err_msg (pretty oper) (pretty op)
            Left e1 -> 
                fail $ err_msg (pretty e1) (pretty op)
    where
        err_msg = [printf|functional operator cannot be the operand of any binary operator: %s, %s|]

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
                    let zs = fromString'' $ ws ++ x : xs ++ ys
                        zs :: Name
                    if isOper n zs
                        then return $ Operator $ render zs
                        else return $ Ident $ render zs
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
                            | otherwise = [printf| '%s'|] (take 5 ys)
                    fail $ [printf|invalid token: '%s'%s|] (take 5 cs) zs)
                return
            xs <- scan_expr n
            return $ (x,li) : xs
        else return []
    where
        isOper (Just n) zs = zs `elem` map token (n^.new_ops)
        isOper Nothing _ = False

parse_expression :: Context 
           -> Notation
           -> StringLi
           -> Either [Error] Expr
parse_expression ctx@(Context _ vars _ defs _)  n i@(StringLi input _) = do
        let vars' = M.map Word vars `M.union` M.mapMaybe f defs
            f (Def xs n args t _e) = do
                    guard (L.null args)
                    Just $ FunApp (mk_fun xs n [] t) []
            li = line_info i
        toks <- read_tokens (scan_expr $ Just n)
            (li^.filename) 
            input (li^.line, li^.column)
        e   <- read_tokens 
            (runParser ctx n vars' expr) 
            (li^.filename) 
            toks 
            (li^.line, li^.column)
        return $ normalize_generics $ flattenConnectors e

parse_oper :: Monad m 
           => Notation
           -> StringLi
           -> EitherT [Error] m BinOperator
parse_oper n s@(StringLi c _) = do
        let li = line_info s
        toks <- hoistEither $ read_tokens (scan_expr $ Just n)
            (li^.filename) 
            c (li^.line, li^.column)
        !e   <- hoistEither $ read_tokens 
            (runParser empty_ctx n M.empty
                oper) 
            (li^.filename) 
            toks (li^.line, li^.column)
        return e

parse_expr' :: ParserSetting
            -> LatexDoc
            -> Either [Error] DispExpr
parse_expr' p = parse_expr p . flatten_li' . drop_blank_text'

contextOf :: ParserSetting -> Context
contextOf set = Context (set^.sorts) (unions [set^.decls, ctx0, ctx1]) M.empty M.empty (set^.dum_ctx)
    where
        ctx0
            | set^.is_step = primeAll $ set^.primed_vars
            | otherwise    = M.empty
        ctx1 
            | set^.free_dummies = set^.dum_ctx
            | otherwise         = M.empty
            
parse_expr :: ParserSetting
           -> StringLi
           -> Either [Error] DispExpr
parse_expr set xs = do
        let ctx = contextOf set
            li  = line_info xs
        x  <- parse_expression ctx
                (set^.language)
                xs
        typed_x  <- case set^.expected_type of
            Just t -> mapBoth 
                (\xs -> map (`Error` li) xs) 
                (normalize_generics) $ zcast t $ Right x
            Nothing -> return x
        let x = normalize_generics typed_x
        unless (L.null $ ambiguities x) $ Left 
            $ map (\x -> Error (msg (pretty x) (pretty $ type_of x)) li)
                $ ambiguities x
        return $ DispExpr (flatten xs) x
    where
        msg   = [printf|type of %s is ill-defined: %s|]
