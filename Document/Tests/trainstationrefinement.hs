module Document.Tests.TrainStationRefinement 
    ( test, test_case )
where

    -- Modules
import Document.Machine

import UnitB.PO

    -- Libraries
import Tests.UnitTest

import Data.String.Utils

import Utilities.Format (format)
import Utilities.Syntactic

test_case :: TestCase
test_case = Case "train station example, with refinement" test True

test :: IO Bool
test = test_cases
            [ Case "verify machine m0" (verify 0 path0) result0
            , Case "verify machine m1" (verify 1 path0) result1
            , Case "verify machine m2" (verify 2 path0) result2
            , Case "verify machine m2, in many files" (verify 2 path1) result2
            , StringCase "cyclic proof of liveness through 3 refinements" (parse path3) result3
            , StringCase "refinement of undefined machine" (parse path4) result4
            ]

result0 :: String
result0 = unlines
     [ "  o  m0/INIT/FIS/in"
     , "  o  m0/m0:enter/FIS/in@prime"
     , "  o  m0/m0:enter/SCH"
     , "  o  m0/m0:leave/FIS/in@prime"
     , "  o  m0/m0:leave/SCH"
     , "  o  m0/m0:leave/SCH/m0/0/REF/weaken"
     , "  o  m0/m0:leave/TR/m0:tr0"
     , "  o  m0/m0:prog0/REF/discharge/tr/lhs"
     , "  o  m0/m0:prog0/REF/discharge/tr/rhs"
     , "passed 9 / 9" 
     ]

result1 :: String
result1 = unlines
     [ "  o  m1/INIT/FIS/in"
     , "  o  m1/INIT/FIS/loc"
     , "  o  m1/INIT/INV/inv0"
     , "  o  m1/SKIP/CO/m1:saf0"
     , "  o  m1/SKIP/CO/m1:saf1"
     , "  o  m1/SKIP/CO/m1:saf2"
     , "  o  m1/SKIP/CO/m1:saf3"
     , "  o  m1/m0:enter/CO/m1:saf0"
     , "  o  m1/m0:enter/CO/m1:saf1"
     , "  o  m1/m0:enter/CO/m1:saf2"
     , "  o  m1/m0:enter/CO/m1:saf3"
     , "  o  m1/m0:enter/FIS/in@prime"
     , "  o  m1/m0:enter/FIS/loc@prime"
     , "  o  m1/m0:enter/INV/inv0"
     , "  o  m1/m0:enter/SCH"
     , "  o  m1/m0:leave/CO/m1:saf0"
     , "  o  m1/m0:leave/CO/m1:saf1"
     , "  o  m1/m0:leave/CO/m1:saf2"
     , "  o  m1/m0:leave/CO/m1:saf3"
     , "  o  m1/m0:leave/FIS/in@prime"
     , "  o  m1/m0:leave/FIS/loc@prime"
     , "  o  m1/m0:leave/INV/inv0"
     , "  o  m1/m0:leave/SCH"
     , "  o  m1/m0:leave/SCH/m1/2/REF/delay/prog/lhs"
     , "  o  m1/m0:leave/SCH/m1/2/REF/delay/prog/rhs"
     , "  o  m1/m0:leave/SCH/m1/2/REF/delay/saf/lhs"
     , "  o  m1/m0:leave/SCH/m1/2/REF/delay/saf/rhs"
     , "  o  m1/m1:movein/CO/m1:saf0"
     , "  o  m1/m1:movein/CO/m1:saf1"
     , "  o  m1/m1:movein/CO/m1:saf2"
     , "  o  m1/m1:movein/CO/m1:saf3"
     , "  o  m1/m1:movein/FIS/in@prime"
     , "  o  m1/m1:movein/FIS/loc@prime"
     , "  o  m1/m1:movein/INV/inv0"
     , "  o  m1/m1:movein/SCH"
     , "  o  m1/m1:movein/SCH/m1/3/REF/weaken"
     , "  o  m1/m1:movein/TR/m1:tr1/EN"
     , "  o  m1/m1:movein/TR/m1:tr1/NEG"
     , "  o  m1/m1:moveout/CO/m1:saf0"
     , "  o  m1/m1:moveout/CO/m1:saf1"
     , "  o  m1/m1:moveout/CO/m1:saf2"
     , "  o  m1/m1:moveout/CO/m1:saf3"
     , "  o  m1/m1:moveout/FIS/in@prime"
     , "  o  m1/m1:moveout/FIS/loc@prime"
     , "  o  m1/m1:moveout/INV/inv0"
     , "  o  m1/m1:moveout/SCH"
     , "  o  m1/m1:moveout/SCH/m1/2/REF/weaken"
     , "  o  m1/m1:moveout/TR/m1:tr0"
     , "  o  m1/m1:prog0/REF/disjunction/lhs"
     , "  o  m1/m1:prog0/REF/disjunction/rhs"
     , "  o  m1/m1:prog1/REF/transitivity/lhs"
     , "  o  m1/m1:prog1/REF/transitivity/mhs"
     , "  o  m1/m1:prog1/REF/transitivity/rhs"
     , "  o  m1/m1:prog2/REF/implication"
     , "  o  m1/m1:prog3/REF/discharge/saf/lhs"
     , "  o  m1/m1:prog3/REF/discharge/saf/rhs"
     , "  o  m1/m1:prog3/REF/discharge/tr"
     , "  o  m1/m1:prog4/REF/discharge/saf/lhs"
     , "  o  m1/m1:prog4/REF/discharge/saf/rhs"
     , "  o  m1/m1:prog4/REF/discharge/tr"
     , "passed 60 / 60"
     ]

result2 :: String
result2 = unlines
    [ "  o  m2/INIT/FIS/in"
    , "  o  m2/INIT/FIS/loc"
    , "  o  m2/INIT/INV/m2:inv0"
    , "  o  m2/SKIP/CO/m2:saf0"
    , "  o  m2/SKIP/CO/m2:saf1"
    , "  o  m2/SKIP/CO/m2:saf2"
    , "  o  m2/m0:enter/CO/m2:saf0"
    , "  o  m2/m0:enter/CO/m2:saf1"
    , "  o  m2/m0:enter/CO/m2:saf2"
    , "  o  m2/m0:enter/FIS/in@prime"
    , "  o  m2/m0:enter/FIS/loc@prime"
    , "  o  m2/m0:enter/INV/m2:inv0"
    , "  o  m2/m0:enter/SCH"
    , "  o  m2/m0:leave/CO/m2:saf0"
    , "  o  m2/m0:leave/CO/m2:saf1"
    , "  o  m2/m0:leave/CO/m2:saf2"
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
    , "  o  m2/m0:leave/SCH"
    , "  o  m2/m0:leave/TR/m2:tr0"
    , " xxx m2/m1:movein/CO/m2:saf0"
    , "  o  m2/m1:movein/CO/m2:saf1"
    , "  o  m2/m1:movein/CO/m2:saf2"
    , "  o  m2/m1:movein/FIS/in@prime"
    , "  o  m2/m1:movein/FIS/loc@prime"
    , "  o  m2/m1:movein/INV/m2:inv0"
    , "  o  m2/m1:movein/SCH"
    , "  o  m2/m1:movein/SCH/m2/1/REF/delay/prog/lhs"
    , "  o  m2/m1:movein/SCH/m2/1/REF/delay/prog/rhs"
    , "  o  m2/m1:movein/SCH/m2/1/REF/delay/saf/lhs"
    , "  o  m2/m1:movein/SCH/m2/1/REF/delay/saf/rhs"
    , "  o  m2/m1:moveout/CO/m2:saf0"
    , "  o  m2/m1:moveout/CO/m2:saf1"
    , "  o  m2/m1:moveout/CO/m2:saf2"
    , "  o  m2/m1:moveout/FIS/in@prime"
    , "  o  m2/m1:moveout/FIS/loc@prime"
    , "  o  m2/m1:moveout/INV/m2:inv0"
    , "  o  m2/m1:moveout/SCH"
    , "  o  m2/m1:moveout/SCH/m2/1/REF/replace/prog/lhs"
    , "  o  m2/m1:moveout/SCH/m2/1/REF/replace/prog/rhs"
    , "  o  m2/m1:moveout/SCH/m2/1/REF/replace/str"
    , "  o  m2/m1:moveout/TR/m2:tr1/EN"
    , "  o  m2/m1:moveout/TR/m2:tr1/EN/leadsto/lhs"
    , "  o  m2/m1:moveout/TR/m2:tr1/EN/leadsto/rhs"
    , "  o  m2/m1:moveout/TR/m2:tr1/NEG"
    , "  o  m2/m2:prog0/REF/trading/lhs"
    , "  o  m2/m2:prog0/REF/trading/rhs"
    , "  o  m2/m2:prog1/REF/trading/lhs"
    , "  o  m2/m2:prog1/REF/trading/rhs"
    , "  o  m2/m2:prog2/REF/disjunction/lhs"
    , "  o  m2/m2:prog2/REF/disjunction/rhs"
    , "  o  m2/m2:prog3/REF/discharge/saf/lhs"
    , "  o  m2/m2:prog3/REF/discharge/saf/rhs"
    , "  o  m2/m2:prog3/REF/discharge/tr"
    , "  o  m2/m2:prog4/REF/monotonicity/lhs"
    , "  o  m2/m2:prog4/REF/monotonicity/rhs"
    , "  o  m2/m2:prog5/REF/disjunction/lhs"
    , "  o  m2/m2:prog5/REF/disjunction/rhs"
    , "  o  m2/m2:prog6/REF/discharge/saf/lhs"
    , "  o  m2/m2:prog6/REF/discharge/saf/rhs"
    , "  o  m2/m2:prog6/REF/discharge/tr"
    , "passed 83 / 84"
    ]

path0 :: String
path0 = "Tests/train-station-ref.tex"

path1 :: String
path1 = "Tests/train-station-ref/main.tex"

path3 :: String
path3 = "Tests/train-station-ref-err0.tex"

result3 :: String
result3 = concat 
    [ "error (1,1): A cycle exists in the proof of liveness: "
    , "m0/evt/SCH, m1/evt/SCH, p0, tr0\n"
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
        Left xs -> unlines $ map (\(Error x (LI _ i j)) -> format "error ({0},{1}): {2}" i j x) xs

verify :: Int -> FilePath -> IO String
verify n path = do
    r <- parse_machine path
    case r of
        Right ms -> do
            (s,_,_) <- str_verify_machine $ ms !! n
            return $ unlines $ map (head . split "(") $ lines s
        x -> return $ show x
