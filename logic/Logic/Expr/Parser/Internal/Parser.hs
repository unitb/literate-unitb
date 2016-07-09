{-# LANGUAGE BangPatterns
        ,RecordWildCards
        ,PatternSynonyms      #-}
module Logic.Expr.Parser.Internal.Parser where

    -- Modules
import Latex.Scanner 
import Latex.Parser  hiding (Close,Open,BracketType(..),Command,Parser,Bracket,token)

import Logic.Expr hiding (recordFields)
import Logic.Expr.Parser.Internal.Monad 
import Logic.Expr.Parser.Internal.Scanner
import Logic.Expr.Parser.Internal.Setting hiding (with_vars)
import Logic.Expr.Printable
import Logic.Operator

import Logic.Theories.SetTheory

import Utilities.Syntactic

    -- Libraries
import Control.Lens hiding (Context,from)

import           Control.Monad
import           Control.Monad.Loops
import           Control.Monad.Trans.Either
import           Control.Precondition

import           Data.Char
import           Data.Either
import           Data.Either.Combinators
import           Data.List as L
import qualified Data.List.NonEmpty as NE
import           Data.Map.Class as M hiding ( map )
import qualified Data.Map.Class as M
import           Data.Semigroup hiding (option)
import qualified Data.Set as S
import           Data.Either.Validation

import Text.Printf.TH

import Utilities.EditDistance
import Utilities.Graph as G ((!))
import Utilities.Table

get_context :: Parser Context 
get_context = context `liftM` get_params

get_notation :: Parser Notation
get_notation = notation `liftM` get_params

get_table :: Parser (Matrix Operator Assoc)
get_table = (view struct . notation) <$> get_params

get_vars :: Parser (Table Name UntypedExpr)
get_vars = variables `liftM` get_params

with_vars :: [(Name, UntypedVar)] -> Parser b -> Parser b
with_vars vs cmd = do
        x <- get_params
        liftP $ runParserWith (f x) $ do
                cmd
    where
        f s@(Param { .. }) =
                s { variables = M.map Word (fromList vs) `M.union` variables }

comma :: Parser ()
comma = read_listP [Comma] >> return ()

colon :: Parser ()
colon = read_listP [Colon] >> return ()

read_listP :: [ExprToken] -> Parser [ExprToken]
read_listP xs = liftP $ read_list xs

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

from :: [(Name,a)] -> Parser a
from m = attempt $ do
        x <- word_or_command
        case x `L.lookup` m of
                Nothing -> fail ""
                Just x  -> return x

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
get_variables'' ctx m li = do
        toks <- read_tokens 
            (scan_expr Nothing) (getString m) li
        xs   <- read_tokens 
            (runParser ctx
                undefined' M.empty vars) 
            toks li
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

apply_fun_op :: Command -> UntypedExpr -> Parser Term
apply_fun_op (Command _ _ _ fop) x = do
        return $ UE $ fun1 fop x

suggestion :: Name -> Table Name String -> [String]
suggestion xs m = map (\(x,y) -> render x ++ " (" ++ y ++ ")") $ toAscList ws
  where
    xs' = map toLower $ render xs
    p ys _ = 2 * dist xs' ys' <= (length xs' `max` length ys') + 1
      where
        ys' = map toLower $ render ys
    ws = M.filterWithKey p m

nameLit :: Parser Name
nameLit = getToken (_Literal._NameLit) "name literal"

assignTok :: Parser (a -> b -> (a,b))
assignTok = getToken _Assign ":=" >> pure (,)

colonTok :: Parser (a -> b -> (a,b))
colonTok = getToken _Colon ":" >> pure (,)


binding :: Parser (UntypedExpr -> LineInfo -> a) -> Parser (Name,a)
binding tok = do
    li <- liftP get_line_info
    liftM2 (,) nameLit (tok <*> expr <*> pure li)

data Term = 
        Cmd Command 
        | Field Name
        -- | E Expr
        | UE UntypedExpr
    deriving (Show)

instance PrettyPrintable Term where
    pretty (Cmd c)   = [printf|Command: %s|] (pretty c)
    pretty (UE ue)   = [printf|UntypedExpr:  %s|] (pretty ue)
    pretty (Field n) = [printf|Field: %s|] (pretty n)

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
                            ue <- expr
                            read_listP [Close Curly]
                            ue <- return $ fun1 f ue
                            return $ UE ue)
                        (return $ Cmd c)
                else do
                    args <- replicateM n $
                        brackets Curly expr
                    return $ UE $ FunApp f args
        , UE <$> recordSetOrLit
        , do    quant <- from quants 
                ns <- brackets Curly
                    $ sep1P word_or_command comma
                _ctx <- get_context
                let vs :: [UntypedVar]
                    vs = Var <$> ns <*> pure ()
                with_vars (zip ns vs) $ do
                    read_listP [Open Curly]
                    r <- tryP (read_listP [Close Curly]) 
                        (\_ -> return ztrue)
                        (do r <- expr
                            read_listP [Close Curly]
                            return r)
                    t <- brackets Curly expr
                    let _vars = used_var r `S.union` used_var t
                        ts :: [(Name, UntypedVar)]
                        ts = zip ns vs
                        _f = (`S.filter` _vars) . (. view name) . (==)
                    let ts' :: Table Name UntypedExpr
                        ts' = M.map Word $ fromList ts
                        r' :: UntypedExpr
                        t' :: UntypedExpr
                        r' = substitute' ts' r
                        t' = substitute' ts' t
                        vs' = map snd ts
                    UE <$> return (Binder quant vs' r' t' ())
        , do    from oftype
                e <- brackets Curly expr
                t <- brackets Curly type_t
                return $ UE $ Cast Parse e t
        , attempt $ do    
                xs' <- word_or_command
                vs <- get_vars
                case M.lookup xs' vs of
                    Just ue -> return $ UE ue
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
        , do    xs <- attempt number
                return $ UE $ zint $ read xs
        , do    Field <$> nameLit
        ]

recordSetOrLit :: Parser UntypedExpr
recordSetOrLit = do
        attempt open_square
        choose_la
            [ attempt close_square >> return (Record $ RecLit M.empty)
            , do li  <- liftP get_line_info
                 n   <- nameLit
                 sep <- choose_la [True <$ attempt assignTok, False <$ attempt colonTok]
                 ue  <- expr
                 if sep
                    then rec_lit =<< ((n,(ue,li)):) <$> parseTail lit
                    else rec_set =<< ((n,(ue,li)):) <$> parseTail set
            ]
    where
        set = binding colonTok
        lit = binding assignTok
        rec_lit m = (Record . RecLit) <$> validateFields m
        rec_set m = zrecord_set' <$> validateFields m
        parseTail field = choose_la 
            [ attempt close_square >> return []
            , do getToken _Comma ","
                 xs <- sep1P field comma
                 close_square
                 return xs
            ]

validateFields :: [(Name, (expr,LineInfo))] -> Parser (Table Name expr)
validateFields xs = raiseErrors $ traverseWithKey f xs'
    where
        xs' = fromListWith (<>) $ xs & mapped._2 %~ pure
        f _ ((x,_):|[]) = Success x
        f k xs = Failure [MLError (msg $ render k) $ NE.toList xs & mapped._1 .~ " - "]
        msg = [printf|Multiple record entry with label '%s'|]
        raiseErrors :: Validation [Error] a -> Parser a
        raiseErrors = either (liftP . Scanner . const . Left) 
                             return . validationToEither

recordFields :: Parser (Name,(a,LineInfo)) -> Parser (Table Name a)
recordFields field = do
        attempt open_square
        xs <- choose_la 
            [ attempt close_square >> return []
            , do xs <- sep1P field comma
                 close_square
                 return xs
            ]
        validateFields xs

        -- | \dummy{ x : \Int }
        -- | \qforall{y}{}{f.y}
        -- | \qforall{f,x}{f.x \le 3}
dummy_types :: [Name] -> Context -> [Var]
dummy_types vs (Context _ _ _ _ dums) = map f vs
    where
        f x = fromMaybe (Var x gA) $ M.lookup x dums

number :: Parser String
number = getToken (_Literal._NumLit) "number"
                
open_square :: Parser [ExprToken]
open_square = read_listP [Open Square]

close_square :: Parser [ExprToken]
close_square = read_listP [Close Square]

open_brack :: Parser [ExprToken]
open_brack  = read_listP [Open Round]

close_brack :: Parser [ExprToken]
close_brack = read_listP [Close Round]

open_curly :: Parser [ExprToken]
open_curly = read_listP [Open QuotedCurly]

close_curly :: Parser [ExprToken]
close_curly = read_listP [Close QuotedCurly]

applyRecUpdate :: [Map Name UntypedExpr] -> Term -> Parser Term
applyRecUpdate rUpd (UE ue) = return $ UE $ foldl (fmap Record . RecUpdate) ue rUpd
applyRecUpdate xs e@(Cmd op)
        | L.null xs = return e
        | otherwise = fail $ "Cannot apply a record update to an operator: " ++ pretty op
applyRecUpdate xs e@(Field op)
        | L.null xs = return e
        | otherwise = fail $ "Cannot apply a record update to a record field: " ++ pretty op

expr :: Parser UntypedExpr
expr = do
        r <- read_term []
        case r of
            UE ue -> return ue
            Cmd op -> fail $ [printf|unapplied functional operator: %s|] (pretty op)
            Field n -> fail $ [printf|record field out of context: %s|] (pretty n)
    where
        read_term :: [([UnaryOperator], Term, BinOperator)] 
                  -> Parser Term
        read_term xs = do
            us <- liftHOF many unary
            choose_la 
                [ do    attempt open_brack
                        ue <- expr
                        close_brack
                        add_context "parsing (" $
                            read_op xs us (UE ue)
                , do    attempt open_curly
                        rs <- sep1P expr comma
                        close_curly
                        ue <- return $ zset_enum' rs
                        add_context "parsing \\{" $
                            read_op xs us $ UE ue
                ,   add_context ("ready for <term>: " ++ show xs) $
                        do  t  <- term
                            rUpd <- manyP (recordFields $ binding assignTok)
                            add_context ("parsed <term>: " ++ pretty t) $
                                read_op xs us =<< applyRecUpdate rUpd t
                ]
        read_op :: [([UnaryOperator], Term, BinOperator)] 
                -> [UnaryOperator] 
                -> Term 
                -> Parser Term
        read_op xs us e0 = do
            end <- orM 
                [ liftP $ is_eof
                , look_aheadP close_brack
                , look_aheadP close_curly
                , look_aheadP close_square
                , look_aheadP comma
                , look_aheadP (read_listP [Close Curly]) ]
            if end
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
            UE ue -> do
                x2 <- return $ mk_unary' op ue
                return $ UE x2
            Cmd oper -> fail $ err_msg (pretty oper) (pretty op)
            Field n  -> fail $ err_msg_2 (pretty n) (pretty op)
    where
        err_msg   = [printf|functional operator cannot be the operand of any unary operator: %s, %s|]
        err_msg_2 = [printf|field names cannot be the operand of any unary operator: %s, %s|]
        
apply_op :: BinOperator -> Term -> Term -> Parser Term
apply_op op x0 x1 = do
        case x1 of
            UE ue1 -> do
                case x0 of
                    UE ue0 -> do
                        ue2 <- return $ mk_expr' op ue0 ue1
                        return $ UE ue2
                    Cmd oper ->
                        if op == apply then
                            apply_fun_op oper ue1
                        else fail $ err_msg (pretty oper) (pretty op)
                    Field n -> fail $ err_msg_2 (pretty n) (pretty op)
            Cmd e1  -> 
                fail $ err_msg (pretty e1) (pretty op)
            Field n 
                | op == apply -> case x0 of
                    UE ue0 -> UE <$> return (Record $ FieldLookup ue0 n)
                    Field n -> fail $ err_msg_2 (pretty n) (pretty op)
                    Cmd cmd -> fail $ err_msg (pretty cmd) (pretty op)
                | otherwise   -> fail $ err_msg_2 (pretty n) (pretty op)
    where
        err_msg = [printf|functional operator cannot be the operand of any binary operator: %s, %s|]
        err_msg_2 = [printf|field name is not a valid operand: %s, %s|]

parse_expression :: ParserSetting
                 -> StringLi
                 -> Either [Error] UntypedExpr
parse_expression set i@(StringLi input _) = do
        let n = set^.language
            li = line_info i
        toks <- read_tokens (scan_expr $ Just n)
            input li
        ue  <- read_tokens
            (runParser' set expr) 
            toks li
        return ue

parse_oper :: Monad m 
           => Notation
           -> StringLi
           -> EitherT [Error] m BinOperator
parse_oper n s@(StringLi c _) = do
        let li = line_info s
        toks <- hoistEither $ read_tokens 
            (scan_expr $ Just n)
            c li
        !e   <- hoistEither $ read_tokens 
            (runParser empty_ctx n M.empty
                oper) 
            toks li
        return e

parse_expr' :: ParserSetting
            -> LatexDoc
            -> Either [Error] DispExpr
parse_expr' p = parse_expr p . flatten_li' . drop_blank_text'
            
parse_expr :: ParserSetting
           -> StringLi
           -> Either [Error] DispExpr
parse_expr set xs = do
        let li  = line_info xs
        x  <- parse_expression set xs
        e  <- type_check x
        typed_x  <- case set^.expected_type of
            Just _ -> mapLeft
                (\xs -> map (`Error` li) xs) $ Right e
            Nothing -> return e
        let x = normalize_generics typed_x
        unless (L.null $ ambiguities x) $ Left 
            $ map (\x -> Error (msg (pretty x) (pretty $ type_of x)) li)
                $ ambiguities x
        return $ DispExpr (flatten xs) x
    where
        msg   = [printf|type of %s is ill-defined: %s|]

type_check :: UntypedExpr -> Either [Error] Expr
type_check = undefined'
