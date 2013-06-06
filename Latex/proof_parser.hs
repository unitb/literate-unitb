module Latex.Proof_Parser where


import Data.Char
import Data.Map hiding ( map )

import Text.ParserCombinators.ReadP as P
-- import Text.ParserCombinators.ReadPrec

import UnitB.AST

import Z3.Const

data ExprTree = 
    Word 
    | Binary Unary [(String, Unary)]
    | Bracket ExprTree
    | Quant String [String] (Maybe ExprTree) ExprTree
type Unary     = ([String], ExprTree)
type ProofTree = () 

proof :: ReadP ProofTree
proof = do
    e0 <- expr
    s <- many step
    skipSpaces
    eof
    return () -- (Calculation empty ztrue e0 s)

step = do
    h <- hint
    e <- expr
    return (h, e)

hint = do
    token "\\hint"
    P.between (token "{") (token "}") operator
    P.between (token "{") (token "}") comment

comment = nested_comment +++ regular_comment

nested_comment = between (token "{") (token "}") comment

regular_comment = do satisfy (not . ('{' ==)) ; comment

expr = op_expr <++ bracket_expr <++ quant_expr

bracket_expr = do
    token "("
    e <- expr
    token ")"
    return e

--readPrec_to_P expression minPrec

--expression = unary +++ binary +++ quant

unary = do
        op <- many operator
        e  <- expr
        return (op, e)        

op_expr = do
        e1 <- unary
        es <- many (do
            op <- operator
            e2 <- unary
            return (op, e2))
        return (Binary e1 es)

quant_expr :: ReadP ExprTree
quant_expr = existential <++ universal

token s = do spaces ; x <- P.string s ; spaces ; return x

spaces = sepBy skipSpaces spacingCommand

spacingCommand = choice $ map string [
        "\\,","\\.","\\;","\\:",
        "~","\\!","\\\\", "&" ]

operator = choice $ map string [
        "+", "\\cdot", "-", ";","=",".",
        "\\land", "\\lor", "\\implies",
        "\\equiv", "\\neg" ]

quantifier :: String -> ReadP ExprTree
quantifier kw = do
        q <- token kw
        ids <- P.between (token "{") (token "}") ident_list
        r <- P.between (token "{") (token "}") $ P.option Nothing (do
            e <- expr
            return $ Just e)
        t <- P.between (token "{") (token "}") expr
        return $ Quant q ids r t

existential :: ReadP ExprTree
existential = quantifier "\\qexists"

universal :: ReadP ExprTree
universal = quantifier "\\qforall"
        
ident_list :: ReadP [String]
ident_list = P.sepBy1 identifier (token ",")

identifier :: ReadP String
identifier = do
        x <- P.satisfy isAlpha
        xs <- P.munch isAlphaNum
        return (x:xs)