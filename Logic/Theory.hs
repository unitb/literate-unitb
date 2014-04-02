{-# LANGUAGE ExistentialQuantification, DeriveDataTypeable #-}
module Logic.Theory where

--import Logic.Const
import Logic.Expr
import Logic.Label
import Logic.Operator
import Logic.Sequent
import Logic.Type

    -- Libraries
import Data.List as L
import Data.Map as M hiding ( map )
import Data.Typeable

import Utilities.Syntactic
import Utilities.HeterogenousEquality


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
        { extends    :: Map String Theory
        , gen_param  :: Maybe Type
        , types      :: Map String Sort
        , funs       :: Map String Fun
        , consts     :: Map String Var
        , fact       :: Map Label Expr
        , dummies    :: Map String Var 
        , theorems   :: Map Label (Maybe Proof)
        , thm_depend :: [ (Label,Label) ]
        , notation   :: Notation }
    deriving (Eq, Show)

basic_theory :: Theory
basic_theory = empty_theory 
        { types = symbol_table [BoolSort, pair_sort]
--        , funs = symbol_table [everywhere_fun]
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
empty_theory = Theory M.empty Nothing
    M.empty M.empty M.empty M.empty 
    M.empty M.empty [] empty_notation

data Proof = forall a. ProofRule a => Proof a
    deriving Typeable

instance Eq Proof where
    Proof x == Proof y = x `h_equal` y

class (Syntactic a, Typeable a, Eq a) => ProofRule a where
    proof_po :: Theory -> a -> Label -> Sequent -> Either [Error] [(Label,Sequent)]

instance Show Proof where
    show _ = "[..]"

th_notation :: Theory -> Notation
th_notation th = res
    where
        ths = th : elems (extends th)
        res = flip precede logic
            $ L.foldl combine empty_notation 
            $ map notation ths
