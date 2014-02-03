module Theories.Theory where

import Logic.Expr
import Logic.Label
import Logic.Operator

    -- Libraries
import Data.Map hiding ( map )

data Theory = Theory 
        { extends   :: [Theory]
        , gen_param :: Maybe Type
        , types     :: Map String Sort
        , funs      :: Map String Fun
        , consts    :: Map String Var
        , fact      :: Map Label Expr
        , dummies   :: Map String Var 
        , notation  :: Notation }
    deriving (Eq, Show)


basic_theory :: Theory
basic_theory = Theory [] Nothing
    (symbol_table [BoolSort]) 
    empty empty empty 
    empty empty_notation

empty_theory :: Theory
empty_theory = Theory [] Nothing
    empty empty empty empty 
    empty empty_notation

