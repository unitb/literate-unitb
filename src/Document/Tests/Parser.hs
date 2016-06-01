{-# LANGUAGE OverloadedStrings #-}
module Document.Tests.Parser where

    -- Modules
import Document.Tests.Suite as S

import Test.UnitTest

import Logic.Theories.FunctionTheory

import UnitB.Expr
import UnitB.QuasiQuote

    -- Library
import Control.Lens
import Control.Monad.State

import Data.Map.Class

test_case :: TestCase
test_case = test_cases 
    "Parser" 
    [ poCase "test0: verify m0" case0 result0 
    , poCase "test1: verify m1" case1 result1 
    , poCase "test2: verify m2" case2 result2 
    , aCase "test3: spontaneous events" case3 result3 
    ]

path0 :: FilePath
path0 = [path|Tests/parser/main.tex|]

case0 :: IO POResult
case0 = verify path0 0

result0 :: String
result0 = unlines
    [ "  o  m0/INIT/FIS/in"
    , "  o  m0/INIT/FIS/v"
    , "  o  m0/INIT/INV/m0:inv0"
    , "  o  m0/INIT/INV/m0:inv1"
    , "  o  m0/INIT/WD"
    , "  o  m0/INIT/WWD"
    , "  o  m0/INV/WD"
    , "  o  m0/input/FIS/in@prime"
    , "  o  m0/input/FIS/v@prime"
    , "  o  m0/input/INV/m0:inv0"
    , "  o  m0/input/INV/m0:inv1"
    , "  o  m0/input/SAF/m0:saf0"
    , "  o  m0/input/WD/ACT/m0:act0"
    , "  o  m0/input/WD/ACT/m0:act1"
    , "  o  m0/input/WD/C_SCH"
    , "  o  m0/input/WD/F_SCH"
    , "  o  m0/input/WD/GRD"
    , "  o  m0/input/WWD"
    , "  o  m0/m0:saf0/SAF/WD/lhs"
    , "  o  m0/m0:saf0/SAF/WD/rhs"
    , "passed 20 / 20"
    ]

case1 :: IO POResult
case1 = verify path0 1

result1 :: String
result1 = unlines
    [ "  o  m1/INIT/FIS/c"
    , "  o  m1/INIT/FIS/err"
    , "  o  m1/INIT/FIS/in"
    , "  o  m1/INIT/FIS/nx"
    , "  o  m1/INIT/FIS/v"
    , "  o  m1/INIT/INV/m1:inv0"
    , "  o  m1/INIT/INV/m1:inv1"
    , "  o  m1/INIT/INV/m1:inv2"
    , "  o  m1/INIT/INV/m1:inv3"
    , "  o  m1/INIT/WD"
    , "  o  m1/INIT/WWD"
    , "  o  m1/INV/WD"
    , "  o  m1/LIVE/m1:prog2/ensure/SAF/WD/lhs"
    , "  o  m1/LIVE/m1:prog2/ensure/SAF/WD/rhs"
    , "  o  m1/LIVE/m1:prog2/ensure/TR/WD"
    , "  o  m1/LIVE/m1:prog2/ensure/TR/choose/EN"
    , "  o  m1/LIVE/m1:prog2/ensure/TR/choose/NEG"
    , "  o  m1/LIVE/m1:prog4/ensure/SAF/WD/lhs"
    , "  o  m1/LIVE/m1:prog4/ensure/SAF/WD/rhs"
    , "  o  m1/LIVE/m1:prog4/ensure/TR/WD"
    , "  o  m1/LIVE/m1:prog4/ensure/TR/parse/EN"
    , "  o  m1/LIVE/m1:prog4/ensure/TR/parse/NEG"
    , "  o  m1/LIVE/m1:prog5/ensure/SAF/WD/lhs"
    , "  o  m1/LIVE/m1:prog5/ensure/SAF/WD/rhs"
    , "  o  m1/LIVE/m1:prog5/ensure/TR/WD"
    , "  o  m1/LIVE/m1:prog5/ensure/TR/fail/EN"
    , "  o  m1/LIVE/m1:prog5/ensure/TR/fail/NEG"
    , "  o  m1/choose/FIS/ast@prime"
    , "  o  m1/choose/FIS/c@prime"
    , "  o  m1/choose/FIS/err@prime"
    , "  o  m1/choose/FIS/in@prime"
    , "  o  m1/choose/FIS/nx@prime"
    , "  o  m1/choose/FIS/v@prime"
    , "  o  m1/choose/INV/m1:inv0"
    , "  o  m1/choose/INV/m1:inv1"
    , "  o  m1/choose/INV/m1:inv2"
    , "  o  m1/choose/INV/m1:inv3"
    , "  o  m1/choose/SAF/LIVE/m1:prog2/ensure"
    , "  o  m1/choose/SAF/LIVE/m1:prog4/ensure"
    , "  o  m1/choose/SAF/LIVE/m1:prog5/ensure"
    , "  o  m1/choose/SCH"
    , "  o  m1/choose/SCH/vv"
    , "  o  m1/choose/WD/ACT/m1:act0"
    , "  o  m1/choose/WD/C_SCH"
    , "  o  m1/choose/WD/F_SCH"
    , "  o  m1/choose/WD/GRD"
    , "  o  m1/choose/WWD"
    , "  o  m1/fail/FIS/ast@prime"
    , "  o  m1/fail/FIS/c@prime"
    , "  o  m1/fail/FIS/err@prime"
    , "  o  m1/fail/FIS/in@prime"
    , "  o  m1/fail/FIS/nx@prime"
    , "  o  m1/fail/FIS/v@prime"
    , "  o  m1/fail/INV/m1:inv0"
    , "  o  m1/fail/INV/m1:inv1"
    , "  o  m1/fail/INV/m1:inv2"
    , "  o  m1/fail/INV/m1:inv3"
    , "  o  m1/fail/SAF/LIVE/m1:prog2/ensure"
    , "  o  m1/fail/SAF/LIVE/m1:prog4/ensure"
    , "  o  m1/fail/SAF/LIVE/m1:prog5/ensure"
    , "  o  m1/fail/WD/ACT/m1:act0"
    , "  o  m1/fail/WD/ACT/m1:act1"
    , "  o  m1/fail/WD/C_SCH"
    , "  o  m1/fail/WD/F_SCH"
    , "  o  m1/fail/WD/GRD"
    , "  o  m1/fail/WWD"
    , "  o  m1/input/FIS/ast@prime"
    , "  o  m1/input/FIS/c@prime"
    , "  o  m1/input/FIS/err@prime"
    , "  o  m1/input/FIS/in@prime"
    , "  o  m1/input/FIS/nx@prime"
    , "  o  m1/input/FIS/v@prime"
    , "  o  m1/input/INV/m1:inv0"
    , "  o  m1/input/INV/m1:inv1"
    , "  o  m1/input/INV/m1:inv2"
    , "  o  m1/input/INV/m1:inv3"
    , "  o  m1/input/IWWD/input"
    , "  o  m1/input/SAF/LIVE/m1:prog2/ensure"
    , "  o  m1/input/SAF/LIVE/m1:prog4/ensure"
    , "  o  m1/input/SAF/LIVE/m1:prog5/ensure"
    , "  o  m1/input/WD/C_SCH"
    , "  o  m1/input/WD/F_SCH"
    , "  o  m1/input/WD/GRD"
    , "  o  m1/input/WWD"
    , "  o  m1/m1:prog0/LIVE/trading/lhs"
    , "  o  m1/m1:prog0/LIVE/trading/rhs"
    , "  o  m1/m1:prog0/PROG/WD/lhs"
    , "  o  m1/m1:prog0/PROG/WD/rhs"
    , "  o  m1/m1:prog1/LIVE/transitivity/lhs"
    , "  o  m1/m1:prog1/LIVE/transitivity/mhs/0/1"
    , "  o  m1/m1:prog1/LIVE/transitivity/rhs"
    , "  o  m1/m1:prog1/PROG/WD/lhs"
    , "  o  m1/m1:prog1/PROG/WD/rhs"
    , "  o  m1/m1:prog2/PROG/WD/lhs"
    , "  o  m1/m1:prog2/PROG/WD/rhs"
    , "  o  m1/m1:prog3/LIVE/disjunction/lhs"
    , "  o  m1/m1:prog3/LIVE/disjunction/rhs"
    , "  o  m1/m1:prog3/PROG/WD/lhs"
    , "  o  m1/m1:prog3/PROG/WD/rhs"
    , "  o  m1/m1:prog4/PROG/WD/lhs"
    , "  o  m1/m1:prog4/PROG/WD/rhs"
    , "  o  m1/m1:prog5/PROG/WD/lhs"
    , "  o  m1/m1:prog5/PROG/WD/rhs"
    , "  o  m1/parse/FIS/ast@prime"
    , "  o  m1/parse/FIS/c@prime"
    , "  o  m1/parse/FIS/err@prime"
    , "  o  m1/parse/FIS/in@prime"
    , "  o  m1/parse/FIS/nx@prime"
    , "  o  m1/parse/FIS/v@prime"
    , "  o  m1/parse/INV/m1:inv0"
    , "  o  m1/parse/INV/m1:inv1"
    , "  o  m1/parse/INV/m1:inv2"
    , "  o  m1/parse/INV/m1:inv3"
    , "  o  m1/parse/SAF/LIVE/m1:prog2/ensure"
    , "  o  m1/parse/SAF/LIVE/m1:prog4/ensure"
    , "  o  m1/parse/SAF/LIVE/m1:prog5/ensure"
    , "  o  m1/parse/WD/ACT/m1:act0"
    , "  o  m1/parse/WD/ACT/m1:act1"
    , "  o  m1/parse/WD/ACT/m1:act2"
    , "  o  m1/parse/WD/C_SCH"
    , "  o  m1/parse/WD/F_SCH"
    , "  o  m1/parse/WD/GRD"
    , "  o  m1/parse/WWD"
    , "passed 123 / 123"
    ]

case2 :: IO POResult
case2 = verify path0 2

result2 :: String
result2 = unlines
    [ "  o  m2/INIT/FIS/c"
    , "  o  m2/INIT/FIS/err"
    , "  o  m2/INIT/FIS/in"
    , "  o  m2/INIT/FIS/nx"
    , "  o  m2/INIT/FIS/v"
    , "  o  m2/INIT/WD"
    , "  o  m2/INIT/WWD"
    , "  o  m2/INV/WD"
    , "  o  m2/choose/FIS/ast@prime"
    , "  o  m2/choose/FIS/c@prime"
    , "  o  m2/choose/FIS/err@prime"
    , "  o  m2/choose/FIS/in@prime"
    , "  o  m2/choose/FIS/nx@prime"
    , "  o  m2/choose/FIS/v@prime"
    , "  o  m2/choose/IWWD/choose"
    , "  o  m2/choose/WD/C_SCH"
    , "  o  m2/choose/WD/F_SCH"
    , "  o  m2/choose/WD/GRD"
    , "  o  m2/choose/WWD"
    , "  o  m2/fail/FIS/ast@prime"
    , "  o  m2/fail/FIS/c@prime"
    , "  o  m2/fail/FIS/err@prime"
    , "  o  m2/fail/FIS/in@prime"
    , "  o  m2/fail/FIS/nx@prime"
    , "  o  m2/fail/FIS/v@prime"
    , "  o  m2/fail/IWWD/fail"
    , "  o  m2/fail/WD/C_SCH"
    , "  o  m2/fail/WD/F_SCH"
    , "  o  m2/fail/WD/GRD"
    , "  o  m2/fail/WWD"
    , "  o  m2/input/FIS/ast@prime"
    , "  o  m2/input/FIS/c@prime"
    , "  o  m2/input/FIS/err@prime"
    , "  o  m2/input/FIS/in@prime"
    , "  o  m2/input/FIS/nx@prime"
    , "  o  m2/input/FIS/v@prime"
    , "  o  m2/input/IWWD/input"
    , "  o  m2/input/WD/C_SCH"
    , "  o  m2/input/WD/F_SCH"
    , "  o  m2/input/WD/GRD"
    , "  o  m2/input/WWD"
    , "  o  m2/parse/FIS/ast@prime"
    , "  o  m2/parse/FIS/c@prime"
    , "  o  m2/parse/FIS/err@prime"
    , "  o  m2/parse/FIS/in@prime"
    , "  o  m2/parse/FIS/nx@prime"
    , "  o  m2/parse/FIS/v@prime"
    , "  o  m2/parse/IWWD/parse"
    , "  o  m2/parse/WD/C_SCH"
    , "  o  m2/parse/WD/F_SCH"
    , "  o  m2/parse/WD/GRD"
    , "  o  m2/parse/WWD"
    , "passed 52 / 52"
    ]

case3 :: IO (Either [Error] (EventRef Expr))
case3 = runEitherT $ do
    r <- EitherT $ parse_machine path0 2
    S.lookup (Right "input",Right "input") $ all_refs' r

result3 :: Either [Error] EventRef'
result3 = Right $ eventRef "input" "input" &~ do
        let fs = make_type (z3Sort "FS" "FS" 0) []
            file = symbol_table [z3Var "file" fs]
            c = ctxWith [function_theory] $ do
                [carrier| FS |]
                [var| file : FS |]
                [var| in : \Int \pfun FS |]
                [var| v : \Int |]
            acts  = fromList 
                    [ ("m0:act0",c [act| in := in \1| (v+1) \fun file |])
                    , ("m0:act1",c [act| v := v + 1 |]) ]
        old %= execState (do
            params  .= file
            actions .= acts
            )
        abs_actions .= acts
        new %= execState (do
            params  .= file
            actions .= acts
            )

