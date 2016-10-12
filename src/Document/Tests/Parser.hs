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

import Data.Map

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
    [ "  o  m0/INIT/INV/m0:inv0"
    , "  o  m0/INIT/INV/m0:inv1"
    , "  o  m0/input/INV/m0:inv0"
    , "  o  m0/input/INV/m0:inv1"
    , "  o  m0/input/SAF/m0:saf0"
    , "passed 5 / 5"
    ]

case1 :: IO POResult
case1 = verify path0 1

result1 :: String
result1 = unlines
    [ "  o  m1/INIT/INV/m1:inv0"
    , "  o  m1/INIT/INV/m1:inv1"
    , "  o  m1/INIT/INV/m1:inv2"
    , "  o  m1/INIT/INV/m1:inv3"
    , "  o  m1/INV/WD"
    , "  o  m1/LIVE/m1:prog2/ensure/TR/choose/EN"
    , "  o  m1/LIVE/m1:prog2/ensure/TR/choose/NEG"
    , "  o  m1/LIVE/m1:prog4/ensure/SAF/WD/lhs"
    , "  o  m1/LIVE/m1:prog4/ensure/TR/WD"
    , "  o  m1/LIVE/m1:prog4/ensure/TR/parse/EN"
    , "  o  m1/LIVE/m1:prog4/ensure/TR/parse/NEG"
    , "  o  m1/LIVE/m1:prog5/ensure/SAF/WD/lhs"
    , "  o  m1/LIVE/m1:prog5/ensure/TR/WD"
    , "  o  m1/LIVE/m1:prog5/ensure/TR/fail/EN"
    , "  o  m1/LIVE/m1:prog5/ensure/TR/fail/NEG"
    , "  o  m1/choose/INV/m1:inv0"
    , "  o  m1/choose/INV/m1:inv1"
    , "  o  m1/choose/INV/m1:inv2"
    , "  o  m1/choose/INV/m1:inv3"
    , "  o  m1/choose/SAF/LIVE/m1:prog2/ensure"
    , "  o  m1/choose/SAF/LIVE/m1:prog4/ensure"
    , "  o  m1/choose/SAF/LIVE/m1:prog5/ensure"
    , "  o  m1/choose/SCH"
    , "  o  m1/choose/SCH/vv"
    , "  o  m1/fail/INV/m1:inv0"
    , "  o  m1/fail/INV/m1:inv1"
    , "  o  m1/fail/INV/m1:inv2"
    , "  o  m1/fail/INV/m1:inv3"
    , "  o  m1/fail/SAF/LIVE/m1:prog2/ensure"
    , "  o  m1/fail/SAF/LIVE/m1:prog4/ensure"
    , "  o  m1/fail/SAF/LIVE/m1:prog5/ensure"
    , "  o  m1/fail/WD/C_SCH"
    , "  o  m1/input/INV/m1:inv0"
    , "  o  m1/input/INV/m1:inv1"
    , "  o  m1/input/INV/m1:inv2"
    , "  o  m1/input/INV/m1:inv3"
    , "  o  m1/input/SAF/LIVE/m1:prog2/ensure"
    , "  o  m1/input/SAF/LIVE/m1:prog4/ensure"
    , "  o  m1/input/SAF/LIVE/m1:prog5/ensure"
    , "  o  m1/m1:prog0/LIVE/trading/lhs"
    , "  o  m1/m1:prog0/LIVE/trading/rhs"
    , "  o  m1/m1:prog1/LIVE/transitivity/lhs"
    , "  o  m1/m1:prog1/LIVE/transitivity/mhs/0/1"
    , "  o  m1/m1:prog1/LIVE/transitivity/rhs"
    , "  o  m1/m1:prog3/LIVE/disjunction/lhs"
    , "  o  m1/m1:prog3/LIVE/disjunction/rhs"
    , "  o  m1/m1:prog4/PROG/WD/lhs"
    , "  o  m1/m1:prog5/PROG/WD/lhs"
    , "  o  m1/parse/INV/m1:inv0"
    , "  o  m1/parse/INV/m1:inv1"
    , "  o  m1/parse/INV/m1:inv2"
    , "  o  m1/parse/INV/m1:inv3"
    , "  o  m1/parse/SAF/LIVE/m1:prog2/ensure"
    , "  o  m1/parse/SAF/LIVE/m1:prog4/ensure"
    , "  o  m1/parse/SAF/LIVE/m1:prog5/ensure"
    , "  o  m1/parse/WD/ACT/m1:act0"
    , "  o  m1/parse/WD/C_SCH"
    , "passed 57 / 57"
    ]

case2 :: IO POResult
case2 = verify path0 2

result2 :: String
result2 = unlines
    [ "passed 0 / 0"
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

