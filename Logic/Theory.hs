{-# LANGUAGE ExistentialQuantification, DeriveDataTypeable #-}
module Logic.Theory where

    -- Modules
import Logic.Expr
import Logic.Operator
import Logic.Proof

    -- Libraries
import           Data.List as L
import           Data.Map as M hiding ( map )

    -- Obsolete doc:
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
        , types      :: Map String Sort
        , funs       :: Map String Fun
        , defs       :: Map String Def
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
empty_theory = Theory M.empty 
    M.empty M.empty M.empty M.empty 
    M.empty M.empty M.empty [] 
    (with_assoc empty_notation)

th_notation :: Theory -> Notation
th_notation th = res
    where
        ths = th : elems (extends th)
        res = flip precede logic
            $ L.foldl combine empty_notation 
            $ map notation ths

theory_ctx :: Theory -> Context
theory_ctx th = 
        merge_all_ctx $
            (Context ts c new_fun (defs th) dums) : L.map theory_ctx (M.elems d)
    where
        d      = extends th
        ts     = types th
        fun    = funs th
        c      = consts th
        dums   = dummies th
        new_fun = fun

    -- todo: prefix name of theorems of a z3_decoration
theory_facts :: Theory -> Map Label Expr
theory_facts th = 
        merge_all (new_fact : L.map theory_facts (M.elems d))
    where
        d      = extends th
        facts  = fact th
        new_fact = facts
