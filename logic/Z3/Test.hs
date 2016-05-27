{-# LANGUAGE OverloadedStrings #-}
module Z3.Test where

    -- Modules
import Z3.Z3 as Z

import Logic.Expr
import Logic.Expr.Const
import Logic.Expr.Declaration
import Logic.Operator hiding ( Command )
import Logic.Proof 
import Logic.Proof.Lambda
import Logic.Theory

import Logic.Theories.SetTheory

    -- Libraries
import Control.Lens hiding (Context,traverse1)

import Data.Default
import qualified Data.Maybe as M
import qualified Data.Set as S

import Test.UnitTest

import Utilities.Functor
import qualified Data.Map.Class as M
import Utilities.Syntactic
import Utilities.Table

test_case :: TestCase
test_case = test

test :: TestCase
test = test_cases 
        "Z3 test" 
        [ case0, case1
        , case2, case3
        --, case4
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

a :: AbsExpr InternalName Type q
x :: Either a (AbsExpr Name Type q)
x' :: Var
ff :: IsName n => AbsFun n Type

a        = Word (make' Var "a" int)
(x,x')   = var "x" int
ff       = mk_fun' [] "f" [int, bool] int

sample_ast :: [Command]
sample_ast = [
        Decl (make' ConstDecl "a" int),
        Decl (make' (FunDecl []) "f" [int, bool] int),
        assert $ M.fromJust $ strip_generics (a `zgreater` zint 10),
        assert $ M.fromJust $ strip_generics (f a ztrue `zless` zint 10),
        CheckSat ]
    where
        f x y   = ($typeCheck) $ typ_fun2 ff (Right x) (Right y)

sample_quant :: [Command]
sample_quant = [
        Decl (make' (FunDecl []) "f" [int] int),
        assert $ M.fromJust $ strip_generics $ ($typeCheck) (mzforall [x'] mztrue (f x `mzless` mzint 10)),
        assert $ M.fromJust $ strip_generics $ ($typeCheck) $ mznot (mzforall [x'] mztrue (f x `mzless` mzint 9)),
        CheckSat ]
    where
        ff          = mk_fun' [] "f" [int] int
        f           = typ_fun1 ff

sample_proof :: Sequent
sample_proof = Sequent 3000 1
        ( def & functions .~ symbol_table [mk_fun' [] "f" [int] int] )
        empty_monotonicity
        [($typeCheck) $ mzforall [x'] mztrue (f x `mzless` mzint 10)]
        M.empty
        (($typeCheck) $ mzforall [x'] mztrue (f x `mzless` mzint 12))
    where
        ff          = mk_fun' [] "f" [int] int
        f           = typ_fun1 ff

sample_quant2 :: [Command]
sample_quant2 = [
        Decl (make' (FunDecl []) "f" [int] int),
        assert $ M.fromJust $ strip_generics $ ($typeCheck) (mzforall [x'] mztrue (f x `mzless` mzint 10)),
        assert $ M.fromJust $ strip_generics $ ($typeCheck) (mzforall [x'] mztrue (f x `mzless` mzint 11)),
        CheckSat]
    where
        f           = typ_fun1 $ mk_fun' [] "f" [int] int

sample_quant3 :: [Command]
sample_quant3 = [
        Decl (make' (FunDecl []) "f" [int] int),
        assert $ M.fromJust $ strip_generics $ ($typeCheck) (mzforall [x'] mztrue (f x `mzless` mzint 10)),
        assert $ M.fromJust $ strip_generics $ ($typeCheck) $ mznot (mzforall [x'] mztrue (f x `mzless` mzint 11)),
        CheckSat] 
    where
        f           = typ_fun1 $ mk_fun' [] "f" [int] int
        
assert :: FOExpr -> Command
assert x = Assert x Nothing

sample_calc :: Calculation
sample_calc = (Calc  
        ctx
        (  ($typeCheck)  ( (x `mzimplies` y) `mzimplies` (f x `mzimplies` f y) )  )
                   ( ($typeCheck) (f x `mzimplies` f y) )
        [ (equal,    ($typeCheck) (f x `mzeq` (f x `mzand` f y)),  [], li)
        , (equal,    ($typeCheck) ( f x `mzeq` f (x `mzand` y) ),  [hyp], li)
        , (follows,  ($typeCheck) ( x `mzeq` (x `mzand` y) ), [], li)
        , (equal,    ($typeCheck) ( x `mzimplies` y ),        [], li) 
        ]
        li )
    where
        ctx = def & functions .~ symbol_table [ mk_fun' [] "f" [bool] bool ]
                  & definitions .~ symbol_table [ z3Def [] "follows" [x',y'] 
                                    bool (($typeCheck) (y `mzimplies` x)) ]
                  & constants .~ symbol_table ( (traverse.traverse1 %~ fromString'')
                                 [ Var "x" bool
                                 , Var "y" bool ] )
        hyp         = ($typeCheck) $ mzforall 
            [x',y'] mztrue 
            ( (f (x `mzand` y) `mzeq` (f x `mzand` f y)) )
        (x,x')      = var "x" bool
        (y,y')      = var "y" bool
        f           = typ_fun1 $ mk_fun' [] "f" [bool] bool
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
        (x,x_decl) = var' (reserved "bv" 0) int
        (fv0,fv0_decl) = var' (reserved "fv" 0) int
        (y,_) = var' [smt|y|] int
        y :: Expr'

result5b :: (CanonicalLambda, [Expr'])
result5b = ( CL 
                [fv1_decl,fv2_decl] [x_decl] 
                ( (x `zplus` fv1) `zle` fv2 ) 
                (Just bool)
            , [z `zplus` y,z `zplus` y])
    where
        (x,x_decl) = var' (reserved "bv" 0) int
        (fv1,fv1_decl) = var' (reserved "fv" 0) int
        (fv2,fv2_decl) = var' (reserved "fv" 1) int
        (y,_) = var' [smt|y|] int
        (z,_) = var' [smt|z|] int

case5a :: IO (CanonicalLambda, [Expr'])
case5a = do
        return (canonical Term [x_decl] (x `zle` y))
    where
        (x,x_decl) = var' [smt|x|] int
        (y,_) = var' [smt|y|] int

case5b :: IO (CanonicalLambda, [Expr'])
case5b = do
        return (canonical Term [x_decl] ( (x `zplus` (z `zplus` y)) `zle` (z `zplus` y) ))
    where
        (x,x_decl) = var' [smt|x|] int
        (y,_) = var' [smt|y|] int
        (z,_) = var' [smt|z|] int

var' :: InternalName -> Type -> (Expr', Var')
var' x t = (Word (Var x t), Var x t)

result6a :: (CanonicalLambda, [Expr'])
result6a = ( CL 
                [fv0_decl] 
                [x_decl] 
                (x `zle` fv0) 
                (Just bool)
            , [y])
    where
        (x,x_decl) = var' (reserved "bv" 0) int
        (fv0,fv0_decl) = var' (reserved "fv" 0) int
        (y,_) = var' [smt|y|] int

case6a :: IO (CanonicalLambda, [Expr'])
case6a = do
        return (canonical Term [x_decl] (x `zle` y))
    where
        x_decl = make' Var "x" int
        x = Word x_decl
        y = Word (make' Var "y" int)

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
        (x,x_decl) = var' (reserved "bv" 0) int
        (fv1,fv1_decl) = var' (reserved "fv" 0) int
        (fv2,fv2_decl) = var' (reserved "fv" 1) int
        (fv3,fv3_decl) = var' (reserved "fv" 2) int
        (lv0,lv0_decl) = var' (reserved "lv" 0) int
        (y,_) = var' [smt|y|] int

case6b :: IO (CanonicalLambda, [Expr'])
case6b = do
        return (canonical Term [x_decl] (zforall [z_decl] 
            (x `zle` zplus (zint 3) y)
            ((x `zplus` (z `zplus` y)) `zle` (z `zplus` y) )))
    where
        x_decl = make' Var "x" int
        x = Word x_decl
        y = Word (make' Var "y" int)
        z_decl = make' Var "z" int
        z = Word z_decl

case7 :: IO (Maybe (GenContext InternalName FOType HOQuantifier))
case7 = return $ Just $ to_fol_ctx S.empty ctx
    where
        fun :: Table Name Fun
        fun = M.map (instantiate m . substitute_type_vars m) $ set_theory^.funs
        ctx = Context M.empty M.empty fun M.empty M.empty
        t = Gen (Sort (fromString'' "G0") (fromString'' "G0") 0) []
        m = M.fromList [ (ti,t) | ti <- map fromString'' ["t","a","b"] ]

result7 :: Maybe (GenContext InternalName FOType HOQuantifier)
result7 = ctx_strip_generics $ Context M.empty M.empty fun' M.empty M.empty
    where 
        fun' = fun & traverse.namesOf %~ asInternal
        fun :: Table InternalName Fun
        fun = decorated_table $ M.elems $ M.map f $ set_theory^.funs
        f :: AbsFun n Type -> AbsFun n Type
        f = instantiate m . substitute_type_vars m
        t = Gen (z3Sort "G0" "G0" 0) []
        m = M.fromList [ (ti,t) | ti <- map fromString'' ["t","a","b"] ]

fun :: Fun
pat :: [Type]
xs  :: [M.Map InternalName GenericType]
ts  :: S.Set FOType

fun = head $ M.elems (set_theory^.funs)
pat    = patterns fun
xs     = map (M.map as_generic) 
                            $ match_all pat (S.elems ts)
ts  = S.fromList $ M.catMaybes $ map type_strip_generics [ set_type int, int ]

case8 :: IO (Maybe (GenContext InternalName FOType HOQuantifier))
case8 = return $ Just $ to_fol_ctx types ctx
    where
        fun   = set_theory^.funs
        ctx   = Context M.empty M.empty fun M.empty M.empty
        types = S.fromList 
                [ int
                , set_type int
                , set_type $ set_type int
                , array int int
                , array int (set_type int)
                , array (set_type int) (set_type $ set_type int)
                , array int bool
                , array (set_type int) (set_type int)
                , array (set_type int) int
                , array int (set_type $ set_type int) -- (set_type $ set_type int)
                , array (set_type int) bool
                ]

result8 :: Maybe (GenContext InternalName FOType HOQuantifier)
result8 = ctx_strip_generics ctx & traverse.functions %~ M.delete pow
    where
        pow :: InternalName
        pow = addSuffix "@Open@@set@@Int@Close" [smt|pow|]
        ctx = Context M.empty M.empty fun' M.empty M.empty
        fun' = fun & traverse.namesOf %~ asInternal
        fun = -- M.fromList $ map g 
                decorated_table $ concatMap M.elems [ M.map (f m) $ set_theory^.funs | m <- ms ]
        f m = instantiate m . substitute_type_vars m
        t0  = int
        t1  = set_type int
        m0  = M.fromList $ [ ("a",t0), ("b",t1), ("t",t0) ] & traverse._1 %~ fromString''
        m1  = M.fromList $ [ ("a",t1), ("b",t0), ("t",t0) ] & traverse._1 %~ fromString''
        ms  = [m0,m1] ++ [ M.fromList [ (tj,ti) | tj <- map fromString'' ["a","b","t"] ] | ti <- [t0, t1] ]

case9 :: IO [ M.Map InternalName FOType ]
case9 = return $ match_some pat types
    where
        types = [set_type int, set_type $ set_type int, fun_type int int]
        var0  = make' VARIABLE "a"
        var1  = make' VARIABLE "b"
        var2  = make' VARIABLE "c"
        pat   = [fun_type var1 var0, set_type var2, var1]
--        pat   = [var0, set_type var1]

result9 :: [ M.Map InternalName FOType ]
result9 = 
        [ M.fromList $ [ ("a", int), ("b", int), ("c", int) ] & traverse._1 %~ fromString''
        , M.fromList $ [ ("a", int), ("b", int), ("c", set_type int) ] & traverse._1 %~ fromString''
        ]


