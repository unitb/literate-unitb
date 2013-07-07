module UnitB_Parser where

data Token op = 
    Keyword String
    | Constant
    | Operator op
    | Open | Close
    | Comma
    | Colon
    | Ident

data Associativity = Left | Right | Ambiguous

-- token :: a -> Token
-- assoc :: op -> op -> Associativity
