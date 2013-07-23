module UnitB.Theory where

import Data.Map hiding ( map )

import Z3.Def
import Z3.Z3

data Label = Lbl String
    deriving (Ord, Eq)

instance Show Label where
    show (Lbl s) = s

label s = Lbl s

data Theory = Theory {
        extends :: [Theory],
--        t_param :: Set String,
        types   :: Map String Sort,
        funs    :: Map String Fun,
        consts  :: Map String Var,
        fact    :: Map Label Expr,
        dummies :: Map String Var }
    deriving Show

symbol_table :: Named a => [a] -> Map String a
symbol_table xs = fromList $ map as_pair xs

class Named n where
    name    :: n -> String
    as_pair :: n -> (String, n)
    as_pair n = (name n, n)

instance Named Fun where
    name (Fun x _ _) = x

instance Named Var where
    name (Var x _) = x

instance Named Sort where
    name (Sort x _ _) = x
    name (DefSort x _ _ _) = x
--        BoolSort | IntSort | RealSort 
--        | Sort String String Int --[String]

--
--data TheoryInstance = TI {
--        generator :: Theory,
--        functions :: Map String [Fun],
--        constants :: Map String [Var],
--        fact_inst :: Map Label [Expr],
--        dummies   :: Map String [Var] }
--
--instantiate :: Map String Var -> Theory 