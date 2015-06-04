{-# LANGUAGE OverloadedStrings, TemplateHaskell #-}
module Z3.Test where

    -- Modules
import Z3.Z3 as Z

import Logic.Expr
import Logic.Lambda
import Logic.Operator hiding ( Command )
import Logic.Proof 
import Logic.Theory   hiding ( assert )

import Theories.SetTheory

import UnitB.PO

    -- Libraries
import qualified Data.Map as M
import qualified Data.Maybe as M
import qualified Data.Set as S

import Utilities.Syntactic

import Tests.UnitTest

test_case :: TestCase
test_case = test

test :: TestCase
test = test_cases 
        "Z3 test" 
        [ case0, case1
        , case2, case3
        , case4
        , Case "canonical lambdas part a" case5a result5a
        , Case "canonical lambdas part b" case5b result5b
        , Case "canonical lambdas with quantifier part a" case6a result6a
        , Case "canonical lambdas with quantifier part b" case6b result6b
        , Case "conversion to first order typing (no type variables)" case7 result7
        , Case "conversion to first order typing" case8 result8
        , Case "instantiating type variables by matching some generic types" case9 result9 ]

case0 :: TestCase
case0 = Case "sample_quant" (verify (label "") sample_quant 2) $ Right Sat
case1 :: TestCase
case1 = Case "sample_quant2" (verify (label "") sample_quant2 2) $ Right Sat
case2 :: TestCase
case2 = Case "sample_quant3" (verify (label "") sample_quant3 2) $ Right Unsat
case3 :: TestCase
case3 = Case "sample proof" (discharge (label "") sample_proof) Valid
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

a :: AbsExpr Type q
x :: Either a (AbsExpr Type q)
x' :: Var
ff :: Fun

a        = Word (Var "a" int)
(x,x')   = var "x" int
ff       = mk_fun [] "f" [int, bool] int

sample_ast :: [Command]
sample_ast = [
        Decl (ConstDecl "a" int),
        Decl (FunDecl [] "f" [int, bool] int),
        assert $ M.fromJust $ strip_generics (a `zgreater` zint 10),
        assert $ M.fromJust $ strip_generics (f a ztrue `zless` zint 10),
        CheckSat ]
    where
        f x y   = ($fromJust) $ typ_fun2 ff (Right x) (Right y)

sample_quant :: [Command]
sample_quant = [
        Decl (FunDecl [] "f" [int] int),
        assert $ M.fromJust $ strip_generics $ ($fromJust) (mzforall [x'] mztrue (f x `mzless` mzint 10)),
        assert $ M.fromJust $ strip_generics $ ($fromJust) $ mznot (mzforall [x'] mztrue (f x `mzless` mzint 9)),
        CheckSat ]
    where
        ff          = mk_fun [] "f" [int] int
        f           = typ_fun1 ff

sample_proof :: Sequent
sample_proof = Sequent
        ( mk_context [FunDecl [] "f" [int] int] )
        empty_monotonicity
        [($fromJust) $ mzforall [x'] mztrue (f x `mzless` mzint 10)]
        M.empty
        (($fromJust) $ mzforall [x'] mztrue (f x `mzless` mzint 12))
    where
        ff          = mk_fun [] "f" [int] int
        f           = typ_fun1 ff

sample_quant2 :: [Command]
sample_quant2 = [
        Decl (FunDecl [] "f" [int] int),
        assert $ M.fromJust $ strip_generics $ ($fromJust) (mzforall [x'] mztrue (f x `mzless` mzint 10)),
        assert $ M.fromJust $ strip_generics $ ($fromJust) (mzforall [x'] mztrue (f x `mzless` mzint 11)),
        CheckSat]
    where
        f           = typ_fun1 $ mk_fun [] "f" [int] int

sample_quant3 :: [Command]
sample_quant3 = [
        Decl (FunDecl [] "f" [int] int),
        assert $ M.fromJust $ strip_generics $ ($fromJust) (mzforall [x'] mztrue (f x `mzless` mzint 10)),
        assert $ M.fromJust $ strip_generics $ ($fromJust) $ mznot (mzforall [x'] mztrue (f x `mzless` mzint 11)),
        CheckSat] 
    where
        f           = typ_fun1 $ mk_fun [] "f" [int] int
        
assert :: FOExpr -> Command
assert x = Assert x Nothing

sample_calc :: Calculation
sample_calc = (Calc  
        ctx
        (  ($fromJust)  ( (x `mzimplies` y) `mzimplies` (f x `mzimplies` f y) )  )
                   ( ($fromJust) (f x `mzimplies` f y) )
        [ (equal,    ($fromJust) (f x `mzeq` (f x `mzand` f y)),  [], li)
        , (equal,    ($fromJust) ( f x `mzeq` f (x `mzand` y) ),  [hyp], li)
        , (follows,  ($fromJust) ( x `mzeq` (x `mzand` y) ), [], li)
        , (equal,    ($fromJust) ( x `mzimplies` y ),        [], li) 
        ]
        li )
    where
        ctx = mk_context [ FunDecl [] "f" [bool] bool,
                  FunDef [] "follows" [x',y'] 
                    bool (($fromJust) (y `mzimplies` x)),
                  ConstDecl "x" bool,
                  ConstDecl "y" bool ]
        hyp         = ($fromJust) $ mzforall 
            [x',y'] mztrue 
            ( (f (x `mzand` y) `mzeq` (f x `mzand` f y)) )
        (x,x')      = var "x" bool
        (y,y')      = var "y" bool
        f           = typ_fun1 $ mk_fun [] "f" [bool] bool
        li          = LI "" (-1) (-1)

indent :: String -> String
indent xs = unlines (map (">  " ++) (lines xs))

type Result = (Either String Satisfiability, Either String Satisfiability, Validity, [(Validity, Int)])

result5a :: (CanonicalLambda, [Expr'])
result5a = ( CL 
                [fv0_decl] [x_decl] 
                (x `zle` fv0)
                (Just bool)
            , [y])
    where
        (x,x_decl) = var' "@@bv@@_0" int
        (fv0,fv0_decl) = var' "@@fv@@_0" int
        (y,_) = var' "y" int

result5b :: (CanonicalLambda, [Expr'])
result5b = ( CL 
                [fv1_decl,fv2_decl] [x_decl] 
                ( (x `zplus` fv1) `zle` fv2 ) 
                (Just bool)
            , [z `zplus` y,z `zplus` y])
    where
        (x,x_decl) = var' "@@bv@@_0" int
        (fv1,fv1_decl) = var' "@@fv@@_0" int
        (fv2,fv2_decl) = var' "@@fv@@_1" int
        (y,_) = var' "y" int
        (z,_) = var' "z" int

case5a :: IO (CanonicalLambda, [Expr'])
case5a = do
        return (canonical Term [x_decl] (x `zle` y))
    where
        (x,x_decl) = var' "x" int
        (y,_) = var' "y" int

case5b :: IO (CanonicalLambda, [Expr'])
case5b = do
        return (canonical Term [x_decl] ( (x `zplus` (z `zplus` y)) `zle` (z `zplus` y) ))
    where
        (x,x_decl) = var' "x" int
        (y,_) = var' "y" int
        (z,_) = var' "z" int

var' :: String -> Type -> (Expr', Var)
var' x t = (Word (Var x t), Var x t)

result6a :: (CanonicalLambda, [Expr'])
result6a = ( CL 
                [fv0_decl] 
                [x_decl] 
                (x `zle` fv0) 
                (Just bool)
            , [y])
    where
        (x,x_decl) = var' "@@bv@@_0" int
        (fv0,fv0_decl) = var' "@@fv@@_0" int
        (y,_) = var' "y" int

case6a :: IO (CanonicalLambda, [Expr'])
case6a = do
        return (canonical Term [x_decl] (x `zle` y))
    where
        x_decl = Var "x" int
        x = Word x_decl
        y = Word (Var "y" int)

result6b :: (CanonicalLambda, [Expr'])
result6b = ( CL 
                [fv1_decl,fv2_decl,fv3_decl] 
                [x_decl] 
                ( (zforall [lv0_decl] 
                    (x `zle` fv1)
                    ((x `zplus` (lv0 `zplus` fv2)) `zle` (lv0 `zplus` fv3) )) ) 
                (Just bool)
            , [zplus (zint 3) y,y,y])
    where
        (x,x_decl) = var' "@@bv@@_0" int
        (fv1,fv1_decl) = var' "@@fv@@_0" int
        (fv2,fv2_decl) = var' "@@fv@@_1" int
        (fv3,fv3_decl) = var' "@@fv@@_2" int
        (lv0,lv0_decl) = var' "@@lv@@_0" int
        (y,_) = var' "y" int

case6b :: IO (CanonicalLambda, [Expr'])
case6b = do
        return (canonical Term [x_decl] (zforall [z_decl] 
            (x `zle` zplus (zint 3) y)
            ((x `zplus` (z `zplus` y)) `zle` (z `zplus` y) )))
    where
        x_decl = Var "x" int
        x = Word x_decl
        y = Word (Var "y" int)
        z_decl = Var "z" int
        z = Word z_decl

case7 :: IO (Maybe (AbsContext FOType HOQuantifier))
case7 = return $ Just $ to_fol_ctx S.empty ctx
    where
        fun :: M.Map String Fun
        fun = M.map (instantiate m . substitute_type_vars m) $ funs set_theory
        ctx = Context M.empty M.empty fun M.empty M.empty
        t = Gen (Sort "G0" "G0" 0) []
        m = M.fromList [ (ti,t) | ti <- ["t","a","b"] ]

result7 :: Maybe (AbsContext FOType HOQuantifier)
result7 = ctx_strip_generics $ Context M.empty M.empty fun M.empty M.empty
    where 
        fun = decorated_table $ M.elems $ M.map f $ funs set_theory
        f :: Fun -> Fun
        f = instantiate m . substitute_type_vars m
        t = Gen (Sort "G0" "G0" 0) []
        m = M.fromList [ (ti,t) | ti <- ["t","a","b"] ]

fun :: Fun
pat :: [Type]
xs  :: [M.Map String GenericType]
ts  :: S.Set FOType

fun = head $ M.elems (funs set_theory)
pat    = patterns fun
xs     = map (M.map as_generic) 
                            $ match_all pat (S.elems ts)
ts  = S.fromList $ M.catMaybes $ map type_strip_generics [ set_type int, int ]

case8 :: IO (Maybe (AbsContext FOType HOQuantifier))
case8 = return $ Just $ to_fol_ctx types ctx
    where
        fun   = funs set_theory
        ctx   = Context M.empty M.empty fun M.empty M.empty
        types = S.fromList 
                [ int
                , set_type int
                , set_type $ set_type int
                , array int int
                , array int bool
                , array (set_type int) (set_type int)
                , array (set_type int) bool
                ]

result8 :: Maybe (AbsContext FOType HOQuantifier)
result8 = ctx_strip_generics ctx
    where
        ctx = Context M.empty M.empty fun M.empty M.empty
        fun = -- M.fromList $ map g 
                decorated_table $ concatMap M.elems [ M.map (f m) $ funs set_theory | m <- ms ]
        f m = instantiate m . substitute_type_vars m
        t0  = int
        t1  = set_type int
        ms  = [ M.fromList [ (tj,ti) | tj <- ["a","b","t"] ] | ti <- [t0, t1] ]

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


