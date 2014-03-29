module Z3.Test where

    -- Modules
import Z3.Z3 as Z

import Logic.Calculation
import Logic.Const
import Logic.Expr
import Logic.Lambda
import Logic.Operator

import UnitB.PO
import UnitB.AST

    -- Libraries
import Data.Map as M ( empty )

import Utilities.Syntactic

import Tests.UnitTest

test :: IO Bool
test = test_cases 
        [ case0, case1
        , case2, case3
        , case4
        , Case "canonical lambdas" case5 result5
        , Case "canonical lambdas with quantifier" case6 result6]

test_case :: ([Char], IO Bool, Bool)
test_case = ("Z3 test", test, True)

case0 :: TestCase
case0 = Case "sample_quant" (verify sample_quant) $ Right Sat
case1 :: TestCase
case1 = Case "sample_quant2" (verify sample_quant2) $ Right Sat
case2 :: TestCase
case2 = Case "sample_quant3" (verify sample_quant3) $ Right Unsat
case3 :: TestCase
case3 = Case "sample proof" (discharge sample_proof) Valid
case4 :: TestCase
case4 = Case "check sample calc" (check empty_theory sample_calc) (Right [])

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
        Assert (a `zgreater` zint 10),
        Assert (f a ztrue `zless` zint 10),
        CheckSat ]
    where
        f       = fun2 ff

sample_quant :: [Command]
sample_quant = [
        Decl (FunDecl [] "f" [int] int),
        Assert $ fromJust (mzforall [x'] mztrue (f x `mzless` mzint 10)),
        Assert $ fromJust $ mznot (mzforall [x'] mztrue (f x `mzless` mzint 9)),
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
        Assert $ fromJust (mzforall [x'] mztrue (f x `mzless` mzint 10)),
        Assert $ fromJust (mzforall [x'] mztrue (f x `mzless` mzint 11)),
        CheckSat]
    where
        f           = maybe1 $ fun1 $ Fun [] "f" [int] int

sample_quant3 :: [Command]
sample_quant3 = [
        Decl (FunDecl [] "f" [int] int),
        Assert $ fromJust (mzforall [x'] mztrue (f x `mzless` mzint 10)),
        Assert $ fromJust $ mznot (mzforall [x'] mztrue (f x `mzless` mzint 11)),
        CheckSat]
    where
        f           = maybe1 $ fun1 $ Fun [] "f" [int] int
        
sample_calc :: Calculation
sample_calc = (Calc  
        ( mk_context [ FunDecl [] "f" [bool] bool,
              FunDef [] "follows" [x',y'] 
                bool (fromJust (y `mzimplies` x)),
              ConstDecl "x" bool,
              ConstDecl "y" bool ] )
        (  fromJust  ( (x `mzimplies` y) `mzimplies` (f x `mzimplies` f y) )  )
                   ( fromJust (f x `mzimplies` f y) )
        [ (equal,    fromJust (f x `mzeq` (f x `mzand` f y)),  [], li)
        , (equal,    fromJust ( f x `mzeq` f (x `mzand` y) ),  [hyp], li)
        , (follows,  fromJust ( x `mzeq` (x `mzand` y) ), [], li)
        , (equal,    fromJust ( x `mzimplies` y ),        [], li) 
        ]
        li )
    where
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
        (Right x,x_decl) = var "@@bv@@_0" int
        (Right fv0,fv0_decl) = var "@@fv@@_0" int
        (Right fv1,fv1_decl) = var "@@fv@@_1" int
        (Right fv2,fv2_decl) = var "@@fv@@_2" int
        (Right y,_) = var "y" int
        (Right z,_) = var "z" int

case5 :: IO (CanonicalLambda, [Expr])
case5 = do
        return (canonical [x_decl] (x `zle` y) ( (x `zplus` (z `zplus` y)) `zle` (z `zplus` y) ))
    where
        (Right x,x_decl) = var "x" int
        (Right y,_) = var "y" int
        (Right z,_) = var "z" int

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
        (Right x,x_decl) = var "@@bv@@_0" int
        (Right fv0,fv0_decl) = var "@@fv@@_0" int
        (Right fv1,fv1_decl) = var "@@fv@@_1" int
        (Right fv2,fv2_decl) = var "@@fv@@_2" int
        (Right fv3,fv3_decl) = var "@@fv@@_3" int
        (Right lv0,lv0_decl) = var "@@lv@@_0" int
        (Right y,_) = var "y" int
--        (Right z,z_decl) = var "z" int

case6 :: IO (CanonicalLambda, [Expr])
case6 = do
        return (canonical [x_decl] (x `zle` y) (zforall [z_decl] 
            (x `zle` zplus (zint 3) y)
            ((x `zplus` (z `zplus` y)) `zle` (z `zplus` y) )))
    where
        (Right x,x_decl) = var "x" int
        (Right y,_) = var "y" int
        (Right z,z_decl) = var "z" int

