{-# LANGUAGE OverloadedStrings #-}
module Document.Tests.Cubes 
    ( test_case, test ) 
where

import Document.Tests.Suite

import Test.UnitTest

import Logic.Proof

import UnitB.Expr

    -- Libraries
import Control.Lens
import Control.Precondition

import Data.List hiding (inits)
import Data.Map hiding ( map )

test_case :: TestCase
test_case = test

test :: TestCase
test = test_cases
        "table of cubes example"
        [ (aCase "test 0 (syntax)" 
                case6 $ Right [machine6])
        , (poCase "test 1 (verification)" 
                case7 result7)
        , (stringCase "test 2 (init/fis po)" 
             case8 result8)
        , (stringCase "proof of inv0" 
             case9 result9)
        , (stringCase "empty proof"
             case10 result10) 
        ]

var_a  :: Var
var_b  :: Var 
var_c  :: Var
var_n  :: Var
var_a' :: Var
var_b' :: Var 
var_c' :: Var
var_n' :: Var

var_a = Var [smt|a|] int
var_b = Var [smt|b|] int
var_c = Var [smt|c|] int
var_n = Var [smt|n|] int

var_a' = Var [smt|a@prime|] int
var_b' = Var [smt|b@prime|] int
var_c' = Var [smt|c@prime|] int
var_n' = Var [smt|n@prime|] int

machine6 :: RawMachineAST
machine6 = newMachine [tex|m0|] $ do
        variables .= fromList (map as_pair [var_a,var_b,var_c,var_n])
        inits .= fromList
                  [ (label "in2", fromRight' $ c .=. 6)
                  , (label "in1", fromRight' $ b .=. 1)
                  , (label "init0", fromRight' $ (n .=. 0) /\ (a .=. 0) )
                  ]
        props .= prop_set6
        event_table .= newEvents [("evt",event6_evt)]
    where
        a = Right $ Word var_a
        b = Right $ Word var_b
        c = Right $ Word var_c
        n = Right $ Word var_n

prop_set6 :: PropertySet' RawExpr
prop_set6 = empty_property_set {
        _inv = fromList $ zip 
                (map label ["inv0","inv1","inv2"]) 
                [ fromRight' $ a .=. (n .^ 3)
                , fromRight' $ b .=.    3 * (n .^ 2)
                                   + 3 * n
                                   + 1     
                , fromRight' $ c .=. 6 * n + 6 ] }
    where
        a = Right $ Word var_a
        b = Right $ Word var_b
        c = Right $ Word var_c
        n = Right $ Word var_n

vars :: [Var]
vars = [var_a,var_b,var_c,var_n] 

event6_evt :: Event' RawExpr
event6_evt = empty_event {
        _actions = rel_action vars $ fromList $ zip 
            (map label ["a1", "a0", "a2", "a3"])
            [ a' `zeq` (a `zplus` b), 
              n' `zeq` (n `zplus` zint 1),
              b' `zeq` (b `zplus` c),
              c' `zeq` (c `zplus` zint 6) ] }
    where
        a  = Word var_a
        a' = Word var_a'
        n  = Word var_n
        n' = Word var_n'
        b  = Word var_b
        b' = Word var_b'
        c  = Word var_c
        c' = Word var_c'

path6 :: FilePath
path6    = [path|Tests/integers.tex|]

case6 :: IO (Either [Error] [RawMachineAST])
case6    = (traverse.traverse %~ fmap getExpr.view' syntax) <$> parse path6

result7 :: String
result7 = unlines 
    [ "  o  m0/INIT/INV/inv0"
    , "  o  m0/INIT/INV/inv1"
    , "  o  m0/INIT/INV/inv2"
    , "  o  m0/evt/FIS/a@prime"
    , "  o  m0/evt/FIS/b@prime"
    , "  o  m0/evt/FIS/c@prime"
    , "  o  m0/evt/FIS/n@prime"
    , "  o  m0/evt/INV/inv0/goal"
    , "  o  m0/evt/INV/inv0/hypotheses"
    , "  o  m0/evt/INV/inv0/relation"
    , "  o  m0/evt/INV/inv0/step 1"
    , "  o  m0/evt/INV/inv0/step 2"
    , "  o  m0/evt/INV/inv0/step 3"
    , "  o  m0/evt/INV/inv0/step 4"
    , "  o  m0/evt/INV/inv0/step 5"
    , "  o  m0/evt/INV/inv1/goal"
    , "  o  m0/evt/INV/inv1/hypotheses"
    , "  o  m0/evt/INV/inv1/relation"
    , "  o  m0/evt/INV/inv1/step 1"
    , "  o  m0/evt/INV/inv1/step 2"
    , "  o  m0/evt/INV/inv1/step 3"
    , "  o  m0/evt/INV/inv1/step 4"
    , "  o  m0/evt/INV/inv1/step 5"
    , "  o  m0/evt/INV/inv1/step 6"
    , "  o  m0/evt/INV/inv2/goal"
    , "  o  m0/evt/INV/inv2/hypotheses"
    , "  o  m0/evt/INV/inv2/relation"
    , "  o  m0/evt/INV/inv2/step 1"
    , "  o  m0/evt/INV/inv2/step 2"
    , "  o  m0/evt/INV/inv2/step 3"
    , "  o  m0/evt/INV/inv2/step 4"
    , "passed 31 / 31"
    ]

case7 :: IO (String, Map Label Sequent)
case7 = do
    verify path6 0

path8 :: FilePath
path8   = [path|Tests/integers_t8.tex|]

result8 :: String
result8 = unlines
    [ "; m0/INIT/FIS/x"
    , "(set-option :auto-config false)"
    , "(set-option :smt.timeout 3000)"
    , "(declare-datatypes (a) ( (Maybe (Just (fromJust a)) Nothing) ))"
    , "(declare-datatypes () ( (Null null) ))"
    , "(declare-datatypes (a b) ( (Pair (pair (first a) (second b))) ))"
    , "(define-sort guarded (a) (Maybe a))"
    , "; comment: we don't need to declare the sort Bool"
    , "; comment: we don't need to declare the sort Int"
    , "; comment: we don't need to declare the sort Real"
    , "(define-sort set (a) (Array a Bool))"
    , "(declare-const x Int)"
    , "(assert (not (exists ( (x Int) ) (and true (= x x)))))"
    , "(assert (not true))"
    , "(check-sat-using (or-else (then qe smt)"
    , "                          (then simplify smt)"
    , "                          (then skip smt)"
    , "                          (then (using-params simplify :expand-power true) smt)))"
    , "; m0/INIT/FIS/x"
    ]

case8 :: IO String
case8 = do
        proof_obligation path8 "m0/INIT/FIS/x" 0

result9 :: String
result9 = unlines 
    [ "m0/evt/INV/inv0:"
    , "(= (^ n' 3) a')"
    , "----"
    , "    (^ n' 3)"
    , "      | (= n' (+ n 1))"
    , "    (^ (+ n 1) 3)"
    , "    (+ (+ (+ (^ n 3) (* 3 (^ n 2))) (* 3 n)) 1)"
    , "      | (= a (^ n 3))"
    , "    (+ (+ (+ a (* 3 (^ n 2))) (* 3 n)) 1)"
    , "      | (= b (+ (+ (* 3 (^ n 2)) (* 3 n)) 1))"
    , "    (+ a b)"
    , "      | (= a' (+ a b))"
    , "    a'"
    ]

case9 :: IO String
case9 = do
        r <- parse path6
        case r of
            Right [m] -> do
                case toList $ m!.proofs of
                    (lbl,ByCalc calc):_ -> 
                          return (pretty lbl ++ ":\n" ++ show_proof calc)
                    xs -> return (
                              "found "
                           ++ intercalate "," (map (proof_kind . snd) xs) 
                           ++ " proofs")
            x -> return $ show x

proof_kind :: Proof -> String
proof_kind (ByCalc _) = "calc"
proof_kind (Easy _ _) = "easy"
proof_kind (ByCases _ _) = "cases"
proof_kind (ByParts _ _) = "parts"
proof_kind (FreeGoal _ _ _ _ _) = "free goal"
proof_kind (Keep _ _ _ _ _) = "keep"
proof_kind (Assertion _ _ _ _) = "assertion"
proof_kind (InstantiateHyp _ _ _ _) = "InstantiateHyp"
proof_kind (Assume _ _ _ _) = "assume"
proof_kind (Definition _ _ _) = "definition"

path10 :: FilePath
path10   = [path|Tests/integers_t10.tex|]

result10 :: String
result10 = unlines
    [ "error 31:21:"
    , "    type error: a calculation must include at least one reasoning step"
    ]

case10 :: IO String
case10 = do
    find_errors path10
