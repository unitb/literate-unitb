module Document.Tests.Puzzle where

    -- Modules
import Document.Tests.Suite

import Logic.Expr
import Logic.Proof

    -- Library
import Data.Map

import Tests.UnitTest

test_case :: TestCase
test_case = test_cases 
        "The king and his advisors puzzle"
        [ POCase "puzzle, m0" case0 result0
        , POCase "puzzle, m1" case1 result1
        , Case "puzzle, proof obligation" case2 result2
        ]

path0 :: FilePath
path0 = "Tests/puzzle/puzzle.tex"

case0 :: IO (String, Map Label Sequent)
case0 = verify path0 0

result0 :: String
result0 = unlines
    [ "  o  m0/INIT/FIS/b"
    , "  o  m0/INIT/WD"
    , "  o  m0/INV/WD"
    , "  o  m0/prog0/PROG/WD/lhs"
    , "  o  m0/prog0/PROG/WD/rhs"
    , "  o  m0/prog0/REF/ensure/m0/TR/term/EN"
    , "  o  m0/prog0/REF/ensure/m0/TR/term/NEG"
    , "  o  m0/prog0/REF/ensure/m0/term/SAF"
    , "  o  m0/term/FIS/b@prime"
    , "  o  m0/term/SCH"
    , "  o  m0/term/SCH/m0/0/REF/weaken"
    , "  o  m0/term/WD/ACT/act0"
    , "  o  m0/term/WD/C_SCH"
    , "  o  m0/term/WD/F_SCH"
    , "  o  m0/term/WD/GRD"
    , "passed 15 / 15"
    ]

case1 :: IO (String, Map Label Sequent)
case1 = verify path0 1

result1 :: String
result1 = unlines
    [ "  o  m1/INIT/FIS/b"
    , "  o  m1/INIT/INV/inv0"
    , "  o  m1/INIT/WD"
    , "  o  m1/INV/WD"
    , "  o  m1/prog1/PROG/WD/lhs"
    , "  o  m1/prog1/PROG/WD/rhs"
    , "  o  m1/prog1/REF/induction/lhs"
    , "  o  m1/prog1/REF/induction/rhs"
    , "  o  m1/prog2/PROG/WD/lhs"
    , "  o  m1/prog2/PROG/WD/rhs"
    , " xxx m1/prog2/REF/add"
    , "  o  m1/saf1/SAF/WD/lhs"
    , "  o  m1/saf1/SAF/WD/rhs"
    , "  o  m1/term/FIS/b@prime"
    , "  o  m1/term/FIS/vs@prime"
    , "  o  m1/term/INV/inv0"
    , "  o  m1/term/SAF/saf1"
    , "  o  m1/term/SCH"
    , "  o  m1/term/SCH/m1/0/REF/delay/prog/lhs"
    , "  o  m1/term/SCH/m1/0/REF/delay/prog/rhs"
    , "  o  m1/term/SCH/m1/0/REF/delay/saf/lhs"
    , "  o  m1/term/SCH/m1/0/REF/delay/saf/rhs"
    , "  o  m1/term/WD/C_SCH"
    , "  o  m1/term/WD/F_SCH"
    , "  o  m1/term/WD/GRD"
    , "passed 24 / 25"
    ]

case2 :: IO String
case2 = proof_obligation path0 "m1/prog1/REF/induction/rhs" 1

result2 :: String
result2 = unlines
    [ "(declare-datatypes (a) ( (Maybe (Just (fromJust a)) Nothing) ))"
    , "(declare-datatypes () ( (Null null) ))"
    , "(declare-datatypes (a b) ( (Pair (pair (first a) (second b))) ))"
    , "; comment: we don't need to declare the sort Bool"
    , "; comment: we don't need to declare the sort Int"
    , "(declare-sort P 0)"
    , "; comment: we don't need to declare the sort Real"
    , "(define-sort set (a) (Array a Bool))"
    , "(declare-const V (set P))"
    , "(declare-const b Bool)"
    , "(declare-const b@prime Bool)"
    , "(declare-const vs (set P))"
    , "(declare-const vs@prime (set P))"
    , "(declare-fun mk-set@@P (P) (set P))"
    , "(define-fun P () (set P) ( (as const (set P)) true ))"
    , "(define-fun compl@@P ( (s1 (set P)) ) (set P) ((_ map not) s1))"
    , "(define-fun elem@@P ( (x P) (s1 (set P)) ) Bool (select s1 x))"
    , "(define-fun empty-set@@P"
    , "            ()"
    , "            (set P)"
    , "            ( (as const (set P))"
    , "              false ))"
    , "(define-fun set-diff@@P"
    , "            ( (s1 (set P))"
    , "              (s2 (set P)) )"
    , "            (set P)"
    , "            (intersect s1 ((_ map not) s2)))"
    , "(define-fun st-subset@@P"
    , "            ( (s1 (set P))"
    , "              (s2 (set P)) )"
    , "            Bool"
    , "            (and (subset s1 s2) (not (= s1 s2))))"
    , "(assert (forall ( (x P)"
    , "                  (y P) )"
    , "                (! (= (elem@@P x (mk-set@@P y)) (= x y))"
    , "                   :pattern"
    , "                   ( (elem@@P x (mk-set@@P y)) ))))"
    , "(assert (not (forall ( (V (set P)) )"
    , "                     (=> true"
    , "                         (=> (or (st-subset@@P (set-diff@@P P vs) V) (= vs P))"
    , "                             (or (and (subset (set-diff@@P P vs) V)"
    , "                                      (subset empty-set@@P (set-diff@@P P vs)))"
    , "                                 (= vs P)))))))"
    , "(assert (not (=> (or (st-subset@@P (set-diff@@P P vs) V) (= vs P))"
    , "                 (or (and (subset (set-diff@@P P vs) V)"
    , "                          (subset empty-set@@P (set-diff@@P P vs)))"
    , "                     (= vs P)))))"
    , "; inv0"
    , "(assert (=> b (= vs P)))"
    , "(assert (not (=> (st-subset@@P (set-diff@@P P vs) V)"
    , "                 (and (subset (set-diff@@P P vs) V)"
    , "                      (subset empty-set@@P (set-diff@@P P vs))))))"
    , "(check-sat-using (or-else (then qe smt)"
    , "                          (then simplify smt)"
    , "                          (then skip smt)"
    , "                          (then (using-params simplify :expand-power true) smt)))"
    ]
