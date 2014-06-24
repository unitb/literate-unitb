module Z3.Test where

    -- Modules
import Z3.Z3 as Z

import Logic.Expr
import Logic.Lambda
import Logic.Operator hiding ( Command )
import Logic.Proof hiding ( assert )
import Logic.Theory

import Theories.SetTheory

import UnitB.PO

    -- Libraries
import qualified Data.Map as M
import qualified Data.Maybe as M
import qualified Data.Set as S

import Utilities.Syntactic

import Tests.UnitTest

test :: IO Bool
test = test_cases 
        [ case0, case1
        , case2, case3
        , case4
        , Case "canonical lambdas" case5 result5
        , Case "canonical lambdas with quantifier" case6 result6
        , Case "conversion to first order typing (no type variables)" case7 result7
        , Case "conversion to first order typing" case8 result8
        , Case "instantiating type variables by matching some generic types" case9 result9 ]

test_case :: ([Char], IO Bool, Bool)
test_case = ("Z3 test", test, True)

case0 :: TestCase
case0 = Case "sample_quant" (verify sample_quant 2) $ Right Sat
case1 :: TestCase
case1 = Case "sample_quant2" (verify sample_quant2 2) $ Right Sat
case2 :: TestCase
case2 = Case "sample_quant3" (verify sample_quant3 2) $ Right Unsat
case3 :: TestCase
case3 = Case "sample proof" (discharge sample_proof) Valid
case4 :: TestCase
case4 = Case "check sample calc" (check sample_calc) (Right [])

sample :: String
sample = unlines [
    "(declare-const a Int)",
    "(declare-fun f (Int Bool) Int)",
    "",
    "(assert (> a 10))",
    "(assert (< (f a true) 100))",
    "(check-sat)",
    "(assert (< a 10))",
    "(check-sat)",
    "(get-model)"]

a :: Expr
x :: Either a Expr
x' :: Var
ff :: Fun

a        = Word (Var "a" int)
(x,x')   = var "x" int
ff       = Fun [] "f" [int, bool] int

sample_ast :: [Command]
sample_ast = [
        Decl (ConstDecl "a" int),
        Decl (FunDecl [] "f" [int, bool] int),
        assert $ M.fromJust $ strip_generics (a `zgreater` zint 10),
        assert $ M.fromJust $ strip_generics (f a ztrue `zless` zint 10),
        CheckSat ]
    where
        f       = fun2 ff

sample_quant :: [Command]
sample_quant = [
        Decl (FunDecl [] "f" [int] int),
        assert $ M.fromJust $ strip_generics $ fromJust (mzforall [x'] mztrue (f x `mzless` mzint 10)),
        assert $ M.fromJust $ strip_generics $ fromJust $ mznot (mzforall [x'] mztrue (f x `mzless` mzint 9)),
        CheckSat ]
    where
        ff          = Fun [] "f" [int] int
        f           = maybe1 $ (\x -> FunApp ff [x])

sample_proof :: Sequent
sample_proof = Sequent
        ( mk_context [FunDecl [] "f" [int] int] )
        [fromJust $ mzforall [x'] mztrue (f x `mzless` mzint 10)]
        M.empty
        (fromJust $ mzforall [x'] mztrue (f x `mzless` mzint 12))
    where
        f           = maybe1 $ fun1 ff

sample_quant2 :: [Command]
sample_quant2 = [
        Decl (FunDecl [] "f" [int] int),
        assert $ M.fromJust $ strip_generics $ fromJust (mzforall [x'] mztrue (f x `mzless` mzint 10)),
        assert $ M.fromJust $ strip_generics $ fromJust (mzforall [x'] mztrue (f x `mzless` mzint 11)),
        CheckSat]
    where
        f           = maybe1 $ fun1 $ Fun [] "f" [int] int

sample_quant3 :: [Command]
sample_quant3 = [
        Decl (FunDecl [] "f" [int] int),
        assert $ M.fromJust $ strip_generics $ fromJust (mzforall [x'] mztrue (f x `mzless` mzint 10)),
        assert $ M.fromJust $ strip_generics $ fromJust $ mznot (mzforall [x'] mztrue (f x `mzless` mzint 11)),
        CheckSat] 
    where
        f           = maybe1 $ fun1 $ Fun [] "f" [int] int
        
assert :: FOExpr -> Command
assert x = Assert x Nothing

sample_calc :: Calculation
sample_calc = (Calc  
        ctx
        (  fromJust  ( (x `mzimplies` y) `mzimplies` (f x `mzimplies` f y) )  )
                   ( fromJust (f x `mzimplies` f y) )
        [ (equal,    fromJust (f x `mzeq` (f x `mzand` f y)),  [], li)
        , (equal,    fromJust ( f x `mzeq` f (x `mzand` y) ),  [hyp], li)
        , (follows,  fromJust ( x `mzeq` (x `mzand` y) ), [], li)
        , (equal,    fromJust ( x `mzimplies` y ),        [], li) 
        ]
        li )
    where
        ctx = mk_context [ FunDecl [] "f" [bool] bool,
                  FunDef [] "follows" [x',y'] 
                    bool (fromJust (y `mzimplies` x)),
                  ConstDecl "x" bool,
                  ConstDecl "y" bool ]
        hyp         = fromJust $ mzforall 
            [x',y'] mztrue 
            ( (f (x `mzand` y) `mzeq` (f x `mzand` f y)) )
        (x,x')      = var "x" bool
        (y,y')      = var "y" bool
        f           = maybe1 $ fun1 $ Fun [] "f" [bool] bool
        li          = LI "" (-1) (-1)

indent :: String -> String
indent xs = unlines (map (">  " ++) (lines xs))

type Result = (Either String Satisfiability, Either String Satisfiability, Validity, [(Validity, Int)])

result5 :: (CanonicalLambda, [Expr])
result5 = ( CL 
                [fv0_decl,fv1_decl,fv2_decl] [x_decl] 
                (x `zle` fv0) ( (x `zplus` fv1) `zle` fv2 ) 
                bool
            , [y,z `zplus` y,z `zplus` y])
    where
        (x,x_decl) = var' "@@bv@@_0" int
        (fv0,fv0_decl) = var' "@@fv@@_0" int
        (fv1,fv1_decl) = var' "@@fv@@_1" int
        (fv2,fv2_decl) = var' "@@fv@@_2" int
        (y,_) = var' "y" int
        (z,_) = var' "z" int

case5 :: IO (CanonicalLambda, [Expr])
case5 = do
        return (canonical [x_decl] (x `zle` y) ( (x `zplus` (z `zplus` y)) `zle` (z `zplus` y) ))
    where
        (x,x_decl) = var' "x" int
        (y,_) = var' "y" int
        (z,_) = var' "z" int

result6 :: (CanonicalLambda, [Expr])
result6 = ( CL 
                [fv0_decl,fv1_decl,fv2_decl,fv3_decl] 
                [x_decl] 
                (x `zle` fv0) 
                ( (zforall [lv0_decl] 
                    (x `zle` fv1)
                    ((x `zplus` (lv0 `zplus` fv2)) `zle` (lv0 `zplus` fv3) )) ) 
                bool
            , [y,zplus (zint 3) y,y,y])
    where
        (x,x_decl) = var' "@@bv@@_0" int
        (fv0,fv0_decl) = var' "@@fv@@_0" int
        (fv1,fv1_decl) = var' "@@fv@@_1" int
        (fv2,fv2_decl) = var' "@@fv@@_2" int
        (fv3,fv3_decl) = var' "@@fv@@_3" int
        (lv0,lv0_decl) = var' "@@lv@@_0" int
        (y,_) = var' "y" int
--        (Right z,z_decl) = var "z" int

var' :: String -> Type -> (Expr, Var)
var' x t = (Word (Var x t), Var x t)

case6 :: IO (CanonicalLambda, [Expr])
case6 = do
        return (canonical [x_decl] (x `zle` y) (zforall [z_decl] 
            (x `zle` zplus (zint 3) y)
            ((x `zplus` (z `zplus` y)) `zle` (z `zplus` y) )))
    where
        x_decl = Var "x" int
        x = Word x_decl
        y = Word (Var "y" int)
        z_decl = Var "z" int
        z = Word z_decl

case7 :: IO (Maybe FOContext)
case7 = return $ Just $ to_fol_ctx S.empty ctx
    where
        fun = M.map (instantiate m . substitute_type_vars m) $ funs set_theory
        ctx = Context M.empty M.empty fun M.empty M.empty
        t = Gen (USER_DEFINED (Sort "G0" "G0" 0) [])
        m = M.singleton "t" t

result7 :: Maybe FOContext
result7 = ctx_strip_generics $ Context M.empty M.empty fun M.empty M.empty
    where 
        fun = decorated_table $ M.elems $ M.map f $ funs set_theory
        f = instantiate m . substitute_type_vars m
        t = Gen (USER_DEFINED (Sort "G0" "G0" 0) [])
        m = M.singleton "t" t

fun :: Fun
pat :: [Type]
xs  :: [M.Map String GenericType]
ts  :: S.Set FOType

fun = head $ M.elems (funs set_theory)
pat    = patterns fun
xs     = map (M.map as_generic) 
                            $ match_all pat (S.elems ts)
ts  = S.fromList $ M.catMaybes $ map type_strip_generics [ set_type int, int ]

case8 :: IO (Maybe FOContext)
case8 = return $ Just $ to_fol_ctx types ctx
    where
        fun   = funs set_theory
        ctx   = Context M.empty M.empty fun M.empty M.empty
        types = S.fromList [int, set_type int, set_type $ set_type int]

result8 :: Maybe FOContext
result8 = ctx_strip_generics ctx
    where
        ctx = Context M.empty M.empty fun M.empty M.empty
        fun = -- M.fromList $ map g 
                decorated_table $ concatMap M.elems [ M.map (f m) $ funs set_theory | m <- ms ]
        f m = instantiate m . substitute_type_vars m
        t0 = int
        t1 = set_type int
        ms  = map (M.singleton "t") [t0, t1]

case9 :: IO [ M.Map String FOType ]
case9 = return $ match_some pat types
    where
        types = [set_type int, set_type $ set_type int, fun_type int int]
        var0  = VARIABLE "a"
        var1  = VARIABLE "b"
        var2  = VARIABLE "c"
        pat   = [fun_type var1 var0, set_type var2, var1]
--        pat   = [var0, set_type var1]

result9 :: [ M.Map String FOType ]
result9 = 
        [ M.fromList [ ("a", int), ("b", int), ("c", int) ]
        , M.fromList [ ("a", int), ("b", int), ("c", set_type int) ]
        ]


