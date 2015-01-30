module Document.Tests.TrainStationRefinement 
    ( test, test_case, case10 )
where

    -- Modules
import Document.Machine
import Document.Tests.Suite

    -- Libraries
import Tests.UnitTest

import Utilities.Syntactic

case10 :: IO Bool
case10 = test_cases [StringCase "cyclic proof of liveness through 3 refinements" (parse path3) result3]

test_case :: TestCase
test_case = Case "train station example, with refinement" test True

test :: IO Bool
test = test_cases
            [ POCase "verify machine m0 (ref)" (verify path0 0) result0
            , POCase "verify machine m1 (ref)" (verify path0 1) result1
            , POCase "verify machine m2 (ref)" (verify path0 2) result2
            , POCase "verify machine m2 (ref), in many files" (verify path1 2) result2
            , StringCase "cyclic proof of liveness through 3 refinements" (parse path3) result3
            , StringCase "refinement of undefined machine" (parse path4) result4
            , StringCase "repeated imports" case5 result5
            ]

result0 :: String
result0 = unlines
    [ "  o  m0/INIT/FIS/in"
    , "  o  m0/INIT/WD"
    , "  o  m0/INV/WD"
    , "  o  m0/TR/m0:tr0/t@param"
    , "  o  m0/m0:enter/FIS/in@prime"
    , "  o  m0/m0:enter/SCH"
    , "  o  m0/m0:enter/WD/ACT/a1"
    , "  o  m0/m0:enter/WD/C_SCH"
    , "  o  m0/m0:enter/WD/F_SCH"
    , "  o  m0/m0:enter/WD/GRD"
    , "  o  m0/m0:leave/FIS/in@prime"
    , "  o  m0/m0:leave/SCH"
    , "  o  m0/m0:leave/SCH/m0/0/REF/weaken"
    , "  o  m0/m0:leave/WD/ACT/lv:a0"
    , "  o  m0/m0:leave/WD/C_SCH"
    , "  o  m0/m0:leave/WD/F_SCH"
    , "  o  m0/m0:leave/WD/GRD"
    , "  o  m0/m0:prog0/PROG/WD/lhs"
    , "  o  m0/m0:prog0/PROG/WD/rhs"
    , "  o  m0/m0:prog0/REF/discharge/tr/lhs"
    , "  o  m0/m0:prog0/REF/discharge/tr/rhs"
    , "  o  m0/m0:tr0/TR/WD"
    , "passed 22 / 22"
    ]

result1 :: String
result1 = unlines
    [ "  o  m1/INIT/FIS/in"
    , "  o  m1/INIT/FIS/loc"
    , "  o  m1/INIT/INV/inv0"
    , "  o  m1/INIT/WD"
    , "  o  m1/INV/WD"
    , "  o  m1/TR/m1:tr0/t@param"
    , "  o  m1/TR/m1:tr1/m1:movein/EN"
    , "  o  m1/TR/m1:tr1/m1:movein/NEG"
    , "  o  m1/m0:enter/FIS/in@prime"
    , "  o  m1/m0:enter/FIS/loc@prime"
    , "  o  m1/m0:enter/INV/inv0"
    , "  o  m1/m0:enter/SAF/m1:saf0"
    , "  o  m1/m0:enter/SAF/m1:saf1"
    , "  o  m1/m0:enter/SAF/m1:saf2"
    , "  o  m1/m0:enter/SAF/m1:saf3"
    , "  o  m1/m0:enter/SCH"
    , "  o  m1/m0:enter/WD/ACT/a3"
    , "  o  m1/m0:enter/WD/C_SCH"
    , "  o  m1/m0:enter/WD/F_SCH"
    , "  o  m1/m0:enter/WD/GRD"
    , "  o  m1/m0:leave/FIS/in@prime"
    , "  o  m1/m0:leave/FIS/loc@prime"
    , "  o  m1/m0:leave/INV/inv0"
    , "  o  m1/m0:leave/SAF/m1:saf0"
    , "  o  m1/m0:leave/SAF/m1:saf1"
    , "  o  m1/m0:leave/SAF/m1:saf2"
    , "  o  m1/m0:leave/SAF/m1:saf3"
    , "  o  m1/m0:leave/SCH"
    , "  o  m1/m0:leave/SCH/m1/0/REF/delay/prog/lhs"
    , "  o  m1/m0:leave/SCH/m1/0/REF/delay/prog/rhs"
    , "  o  m1/m0:leave/SCH/m1/0/REF/delay/saf/lhs"
    , "  o  m1/m0:leave/SCH/m1/0/REF/delay/saf/rhs"
    , "  o  m1/m0:leave/WD/ACT/lv:a2"
    , "  o  m1/m0:leave/WD/C_SCH"
    , "  o  m1/m0:leave/WD/F_SCH"
    , "  o  m1/m0:leave/WD/GRD"
    , "  o  m1/m1:movein/FIS/in@prime"
    , "  o  m1/m1:movein/FIS/loc@prime"
    , "  o  m1/m1:movein/INV/inv0"
    , "  o  m1/m1:movein/SAF/m1:saf0"
    , "  o  m1/m1:movein/SAF/m1:saf1"
    , "  o  m1/m1:movein/SAF/m1:saf2"
    , "  o  m1/m1:movein/SAF/m1:saf3"
    , "  o  m1/m1:movein/SCH"
    , "  o  m1/m1:movein/SCH/m1/0/REF/weaken"
    , "  o  m1/m1:movein/WD/ACT/mi:a2"
    , "  o  m1/m1:movein/WD/C_SCH"
    , "  o  m1/m1:movein/WD/F_SCH"
    , "  o  m1/m1:movein/WD/GRD"
    , "  o  m1/m1:moveout/FIS/in@prime"
    , "  o  m1/m1:moveout/FIS/loc@prime"
    , "  o  m1/m1:moveout/INV/inv0"
    , "  o  m1/m1:moveout/SAF/m1:saf0"
    , "  o  m1/m1:moveout/SAF/m1:saf1"
    , "  o  m1/m1:moveout/SAF/m1:saf2"
    , "  o  m1/m1:moveout/SAF/m1:saf3"
    , "  o  m1/m1:moveout/SCH"
    , "  o  m1/m1:moveout/SCH/m1/0/REF/weaken"
    , "  o  m1/m1:moveout/WD/ACT/a2"
    , "  o  m1/m1:moveout/WD/C_SCH"
    , "  o  m1/m1:moveout/WD/F_SCH"
    , "  o  m1/m1:moveout/WD/GRD"
    , "  o  m1/m1:prog0/PROG/WD/lhs"
    , "  o  m1/m1:prog0/PROG/WD/rhs"
    , "  o  m1/m1:prog0/REF/disjunction/lhs"
    , "  o  m1/m1:prog0/REF/disjunction/rhs"
    , "  o  m1/m1:prog1/PROG/WD/lhs"
    , "  o  m1/m1:prog1/PROG/WD/rhs"
    , "  o  m1/m1:prog1/REF/transitivity/lhs"
    , "  o  m1/m1:prog1/REF/transitivity/mhs"
    , "  o  m1/m1:prog1/REF/transitivity/rhs"
    , "  o  m1/m1:prog2/PROG/WD/lhs"
    , "  o  m1/m1:prog2/PROG/WD/rhs"
    , "  o  m1/m1:prog2/REF/implication"
    , "  o  m1/m1:prog3/PROG/WD/lhs"
    , "  o  m1/m1:prog3/PROG/WD/rhs"
    , "  o  m1/m1:prog3/REF/discharge/saf/lhs"
    , "  o  m1/m1:prog3/REF/discharge/saf/rhs"
    , "  o  m1/m1:prog3/REF/discharge/tr"
    , "  o  m1/m1:prog4/PROG/WD/lhs"
    , "  o  m1/m1:prog4/PROG/WD/rhs"
    , "  o  m1/m1:prog4/REF/discharge/saf/lhs"
    , "  o  m1/m1:prog4/REF/discharge/saf/rhs"
    , "  o  m1/m1:prog4/REF/discharge/tr"
    , "  o  m1/m1:saf0/SAF/WD/lhs"
    , "  o  m1/m1:saf0/SAF/WD/rhs"
    , "  o  m1/m1:saf1/SAF/WD/lhs"
    , "  o  m1/m1:saf1/SAF/WD/rhs"
    , "  o  m1/m1:saf2/SAF/WD/lhs"
    , "  o  m1/m1:saf2/SAF/WD/rhs"
    , "  o  m1/m1:saf3/SAF/WD/lhs"
    , "  o  m1/m1:saf3/SAF/WD/rhs"
    , "  o  m1/m1:tr0/TR/WD"
    , "  o  m1/m1:tr1/TR/WD"
    , "passed 94 / 94"
    ]

result2 :: String
result2 = unlines
    [ "  o  m2/INIT/FIS/in"
    , "  o  m2/INIT/FIS/loc"
    , "  o  m2/INIT/INV/m2:inv0"
    , "  o  m2/INIT/WD"
    , "  o  m2/INV/WD"
    , "  o  m2/TR/m2:tr0/t@param"
    , "  o  m2/TR/m2:tr1/leadsto/lhs"
    , "  o  m2/TR/m2:tr1/leadsto/rhs"
    , "  o  m2/TR/m2:tr1/m1:moveout/EN"
    , "  o  m2/TR/m2:tr1/m1:moveout/NEG"
    , "  o  m2/m0:enter/FIS/in@prime"
    , "  o  m2/m0:enter/FIS/loc@prime"
    , "  o  m2/m0:enter/INV/m2:inv0"
    , "  o  m2/m0:enter/SAF/m2:saf0"
    , "  o  m2/m0:enter/SAF/m2:saf1"
    , "  o  m2/m0:enter/SAF/m2:saf2"
    , "  o  m2/m0:enter/SCH"
    , "  o  m2/m0:enter/WD/C_SCH"
    , "  o  m2/m0:enter/WD/F_SCH"
    , "  o  m2/m0:enter/WD/GRD"
    , "  o  m2/m0:leave/FIS/in@prime"
    , "  o  m2/m0:leave/FIS/loc@prime"
    , "  o  m2/m0:leave/INV/m2:inv0/assertion/hyp3/easy "
    , "  o  m2/m0:leave/INV/m2:inv0/assertion/hyp4/easy "
    , "  o  m2/m0:leave/INV/m2:inv0/assertion/hyp5/easy "
    , "  o  m2/m0:leave/INV/m2:inv0/assertion/hyp6/easy "
    , "  o  m2/m0:leave/INV/m2:inv0/assertion/hyp7/goal "
    , "  o  m2/m0:leave/INV/m2:inv0/assertion/hyp7/hypotheses "
    , "  o  m2/m0:leave/INV/m2:inv0/assertion/hyp7/relation "
    , "  o  m2/m0:leave/INV/m2:inv0/assertion/hyp7/step "
    , "  o  m2/m0:leave/INV/m2:inv0/assertion/hyp7/step "
    , "  o  m2/m0:leave/INV/m2:inv0/assertion/hyp7/step "
    , "  o  m2/m0:leave/INV/m2:inv0/assertion/hyp8/goal "
    , "  o  m2/m0:leave/INV/m2:inv0/assertion/hyp8/hypotheses "
    , "  o  m2/m0:leave/INV/m2:inv0/assertion/hyp8/relation "
    , "  o  m2/m0:leave/INV/m2:inv0/assertion/hyp8/step "
    , "  o  m2/m0:leave/INV/m2:inv0/assertion/hyp8/step "
    , "  o  m2/m0:leave/INV/m2:inv0/assertion/hyp8/step "
    , "  o  m2/m0:leave/INV/m2:inv0/main goal/goal "
    , "  o  m2/m0:leave/INV/m2:inv0/main goal/hypotheses "
    , "  o  m2/m0:leave/INV/m2:inv0/main goal/relation "
    , "  o  m2/m0:leave/INV/m2:inv0/main goal/step "
    , "  o  m2/m0:leave/INV/m2:inv0/main goal/step "
    , "  o  m2/m0:leave/INV/m2:inv0/main goal/step "
    , "  o  m2/m0:leave/INV/m2:inv0/new assumption "
    , "  o  m2/m0:leave/SAF/m2:saf0"
    , "  o  m2/m0:leave/SAF/m2:saf1"
    , "  o  m2/m0:leave/SAF/m2:saf2"
    , "  o  m2/m0:leave/SCH"
    , "  o  m2/m0:leave/WD/C_SCH"
    , "  o  m2/m0:leave/WD/F_SCH"
    , "  o  m2/m0:leave/WD/GRD"
    , "  o  m2/m1:movein/FIS/in@prime"
    , "  o  m2/m1:movein/FIS/loc@prime"
    , "  o  m2/m1:movein/INV/m2:inv0"
    , "  o  m2/m1:movein/SAF/m2:saf0"
    , "  o  m2/m1:movein/SAF/m2:saf1"
    , "  o  m2/m1:movein/SAF/m2:saf2"
    , "  o  m2/m1:movein/SCH"
    , "  o  m2/m1:movein/SCH/m2/0/REF/delay/prog/lhs"
    , "  o  m2/m1:movein/SCH/m2/0/REF/delay/prog/rhs"
    , "  o  m2/m1:movein/SCH/m2/0/REF/delay/saf/lhs"
    , "  o  m2/m1:movein/SCH/m2/0/REF/delay/saf/rhs"
    , "  o  m2/m1:movein/WD/C_SCH"
    , "  o  m2/m1:movein/WD/F_SCH"
    , "  o  m2/m1:movein/WD/GRD"
    , "  o  m2/m1:moveout/FIS/in@prime"
    , "  o  m2/m1:moveout/FIS/loc@prime"
    , "  o  m2/m1:moveout/INV/m2:inv0"
    , "  o  m2/m1:moveout/SAF/m2:saf0"
    , "  o  m2/m1:moveout/SAF/m2:saf1"
    , "  o  m2/m1:moveout/SAF/m2:saf2"
    , "  o  m2/m1:moveout/SCH"
    , "  o  m2/m1:moveout/SCH/m2/0/REF/replace/prog/lhs"
    , "  o  m2/m1:moveout/SCH/m2/0/REF/replace/prog/rhs"
    , "  o  m2/m1:moveout/SCH/m2/0/REF/replace/str"
    , "  o  m2/m1:moveout/WD/C_SCH"
    , "  o  m2/m1:moveout/WD/F_SCH"
    , "  o  m2/m1:moveout/WD/GRD"
    , "  o  m2/m2:prog0/PROG/WD/lhs"
    , "  o  m2/m2:prog0/PROG/WD/rhs"
    , "  o  m2/m2:prog0/REF/trading/lhs"
    , "  o  m2/m2:prog0/REF/trading/rhs"
    , "  o  m2/m2:prog1/PROG/WD/lhs"
    , "  o  m2/m2:prog1/PROG/WD/rhs"
    , "  o  m2/m2:prog1/REF/trading/lhs"
    , "  o  m2/m2:prog1/REF/trading/rhs"
    , "  o  m2/m2:prog2/PROG/WD/lhs"
    , "  o  m2/m2:prog2/PROG/WD/rhs"
    , "  o  m2/m2:prog2/REF/disjunction/lhs"
    , "  o  m2/m2:prog2/REF/disjunction/rhs"
    , "  o  m2/m2:prog3/PROG/WD/lhs"
    , "  o  m2/m2:prog3/PROG/WD/rhs"
    , "  o  m2/m2:prog3/REF/discharge/saf/lhs"
    , "  o  m2/m2:prog3/REF/discharge/saf/rhs"
    , "  o  m2/m2:prog3/REF/discharge/tr"
    , "  o  m2/m2:prog4/PROG/WD/lhs"
    , "  o  m2/m2:prog4/PROG/WD/rhs"
    , "  o  m2/m2:prog4/REF/monotonicity/lhs"
    , "  o  m2/m2:prog4/REF/monotonicity/rhs"
    , "  o  m2/m2:prog5/PROG/WD/lhs"
    , "  o  m2/m2:prog5/PROG/WD/rhs"
    , "  o  m2/m2:prog5/REF/disjunction/lhs"
    , "  o  m2/m2:prog5/REF/disjunction/rhs"
    , "  o  m2/m2:prog6/PROG/WD/lhs"
    , "  o  m2/m2:prog6/PROG/WD/rhs"
    , "  o  m2/m2:prog6/REF/discharge/saf/lhs"
    , "  o  m2/m2:prog6/REF/discharge/saf/rhs"
    , "  o  m2/m2:prog6/REF/discharge/tr"
    , "  o  m2/m2:saf0/SAF/WD/lhs"
    , "  o  m2/m2:saf0/SAF/WD/rhs"
    , "  o  m2/m2:saf1/SAF/WD/lhs"
    , "  o  m2/m2:saf1/SAF/WD/rhs"
    , "  o  m2/m2:saf2/SAF/WD/lhs"
    , "  o  m2/m2:saf2/SAF/WD/rhs"
    , "  o  m2/m2:tr0/TR/WD"
    , "  o  m2/m2:tr1/TR/WD"
    , "passed 117 / 117"
    ]

path0 :: String
path0 = "Tests/train-station-ref.tex"

path1 :: String
path1 = "Tests/train-station-ref/main.tex"

path3 :: String
path3 = "Tests/train-station-ref-err0.tex"

result3 :: String
result3 = unlines
    [ "error: A cycle exists in the liveness proof"
    , "\tProgress property p0 (refined in m0): (41,1)"
    , "\tEvent evt (refined in m1): (50,1)"
    , ""
    ]

path4 :: String
path4 = "Tests/train-station-ref-err1.tex"

result4 :: String
result4 = concat 
    [ "error (30,20): Machine m0 refines a non-existant machine: mm\n"
    ]

parse :: FilePath -> IO String
parse path = do
    r <- parse_machine path
    return $ case r of
        Right _ -> "ok"
        Left xs -> unlines $ map report xs

path5 :: FilePath
path5 = "tests/train-station-ref-err2.tex"

result5 :: String
result5 = unlines
    [ "error: Theory imported multiple times"
    , "\t\"sets\": (37,1)"
    , "\t\"sets\": (87,1)"
    , "\t\"sets\": (443,1)"
    , "\t\"sets\": (444,12)"
    , ""
    , "error: Theory imported multiple times"
    , "\t\"functions\": (88,12)"
    , "\t\"functions\": (445,12)"
    , ""
    ]

case5 :: IO String
case5 = find_errors path5

