{-# LANGUAGE PatternSynonyms #-}
module Logic.Expr.Parser.Internal.Scanner where

    -- Modules
import Latex.Scanner 

import Logic.Expr
import Logic.Operator

import Utilities.Syntactic

    -- Libraries
import Control.Lens hiding (Context,from)

import           Control.Monad

import           Data.Char

import Text.Printf.TH

pattern Number x = Literal (NumLit x)

data Bracket = Curly | QuotedCurly | Round | Square
    deriving (Eq, Show)

data ExprToken = 
        Open Bracket 
        | Close Bracket 
        | Ident String 
        | Assign
        | Literal ExprLit 
        | Operator String
        | Comma | Colon
    deriving (Show, Eq)

data ExprLit = NumLit String | NameLit Name
    deriving (Show, Eq)

makePrisms ''ExprToken
makePrisms ''ExprLit

instance IsBracket Bracket String where
    bracketPair Curly  = ("{","}")
    bracketPair QuotedCurly = ("\\{","\\}")
    bracketPair Round  = ("(", ")")
    bracketPair Square = ("[", "]")

instance Token ExprToken where
    lexeme (Open b)   = openBracket b
    lexeme (Close b)  = closeBracket b
    lexeme (Ident n)  = n
    lexeme (Literal (NumLit n)) = n
    lexeme (Literal (NameLit n)) = '\'' : render n
    lexeme (Operator op) = op
    lexeme Assign     = ":="
    lexeme Comma      = ","
    lexeme Colon      = ":"

option :: Monoid b => Scanner a b -> Scanner a b
option cmd = do
        try cmd
            return
            (return mempty)

identString :: Scanner Char String
identString = do
        ws <- option $ read_list "\\"
        x  <- match_char isAlpha
        xs <- many $ match_char isWord
        ys <- option $ read_list "\'"
        return $ ws ++ [x] ++ xs ++ ys

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
                , read_list ":=" >> return Assign
                , read_list "(" >> return (Open Round)
                , read_list "\\{" >> return (Open QuotedCurly)
                , read_list "}" >> return (Close Curly)
                , read_list "]" >> return (Close Square)
                , read_list ")" >> return (Close Round)
                , read_list "\\}" >> return (Close QuotedCurly)
                , read_list ":" >> return Colon
                , read_list "," >> return Comma
                , do
                    read_list "'"
                    Literal . NameLit . fromString'' <$> identString
                , match_char (`elem` ['.',';']) >>= \x -> return $ Operator [x]
                , do
                    zs <- fromString'' <$> identString
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

match_char :: Token a => (a -> Bool) -> Scanner a a
match_char p = read_if p return (fail "")

eat_space :: Scanner Char ()
eat_space = do
        b <- is_eof
        if b
        then return ()
        else choice 
                [ match_char isSpace >> return ()
                , do read_list "\\begin{array}{" 
                     many (match_char (/= '}')) 
                     read_list "}"
                     return ()
                , read_list "\\end{array}" >> return ()
                , read_list "\\left" >> return ()
                , read_list "\\right" >> return ()
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

read_list :: (Token a, Show a, Eq a) => [a] -> Scanner a [a]
read_list xs = do
        x <- match (match_string xs) 
        case x of
            Just x -> return x
            Nothing -> fail ("expecting: " ++ show xs)
