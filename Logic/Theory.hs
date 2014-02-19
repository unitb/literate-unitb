module Logic.Theory where

import Logic.Expr
import Logic.Label
import Logic.Operator

    -- Libraries
import Data.Map hiding ( map )

    -- the use of gen_param is tricky. Be careful
    -- generic functions should have type variables in them
    -- to match those type variables, we use the generic 
    -- parameter that features corresponding /generic/
    -- types. We unify the generic parameter with all 
    -- the types of all the variables and functions
    -- and use the resulting mapping to instantiate 
    -- the type variables. The generic type (rather than
    -- the type variable) is also used in function types.
data Theory = Theory 
        { extends   :: Map String Theory
        , gen_param :: Maybe Type
        , types     :: Map String Sort
        , funs      :: Map String Fun
        , consts    :: Map String Var
        , fact      :: Map Label Expr
        , dummies   :: Map String Var 
        , notation  :: Notation }
    deriving (Eq, Show)

basic_theory :: Theory
basic_theory = empty_theory 
        { types = symbol_table [BoolSort]
--        , gen_param = Just gT
--        , funs  = symbol_table [Fun [gT] "eq" [gT,gT] bool]
--        , fact  = fromList 
--            [ (label "@basic@@_0", axm0) ]
        , notation = functions }
--    where
--        t  = VARIABLE "t"
--        gT = GENERIC "t"
--        (x,x_decl) = var "x" t
--        (y,y_decl) = var "y" t
--        axm0 = fromJust $ mzforall [x_decl,y_decl] mztrue $
--                mzeq x y `mzeq` mzeq_symb x y

empty_theory :: Theory
empty_theory = Theory empty Nothing
    empty empty empty empty 
    empty empty_notation

