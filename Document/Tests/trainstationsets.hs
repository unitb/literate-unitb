module Document.Tests.TrainStationSets where

import Document.Document

import UnitB.PO

    -- Libraries
import Data.String.Utils

import Tests.UnitTest

test_case :: TestCase
test_case = Case "train station example, with sets" test True

test :: IO Bool
test = test_cases
            [ Case "verify machine m0" (verify 0 path0) result0
            , Case "verify machine m1" (verify 1 path0) result1
            , Case "verify machine m2" (verify 2 path0) result2
            , Case "verify machine m3" (verify 3 path0) result5
            , Case "type checking of boolean expressions" case3 result3
            , Case "verify machine m3 error (wandering free variable)" (verify 3 path4) result4
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
    , "  o  m2/m2:prog6/REF/disjunction/lhs"
    , "  o  m2/m2:prog6/REF/disjunction/rhs"
    , "  o  m2/m2:prog7/REF/discharge/saf/lhs"
    , "  o  m2/m2:prog7/REF/discharge/saf/rhs"
    , "  o  m2/m2:prog7/REF/discharge/tr"
  	, "passed 85 / 86"
	]

path0 :: String
path0 = "Tests/train-station-set.tex"

result3 :: String
result3 = concat
    [ "Left [Error \"type error: expression has type incompatible with its type annotation:\\n"
    , "  expression: ent\\n"
    , "  type: BLK\\n"
    , "  type annotation: Bool \\n"
    , "\" (295,54)]"
    ]

path3 :: String
path3 = "Tests/train-station-set-err0.tex"

case3 :: IO String
case3 = do
    r <- parse_machine path3
    return $ show r

path4 :: String
path4 = "Tests/train-station-set-err1.tex"

case4 :: IO String
case4 = do
    r <- parse_machine path4
    return $ show r

result4 :: String
result4 = "Left [Error \"undeclared variable: t\" (494,26)]"

result5 :: String
result5 = unlines
	[ "  o  m3/INIT/FIS/in"
	, "  o  m3/INIT/FIS/isgn"
	, "  o  m3/INIT/FIS/loc"
	, "  o  m3/INIT/FIS/osgn"
	, "  o  m3/INIT/INV/m3:inv0"
	, "  o  m3/INIT/INV/m3:inv1"
	, "  o  m3/INIT/INV/m3:inv2"
	, "  o  m3/INIT/INV/m3:inv3"
	, "  o  m3/SKIP/CO/m3:saf0"
	, "  o  m3/SKIP/CO/m3:saf1"
	, "  o  m3/m0:enter/CO/m3:saf0"
	, "  o  m3/m0:enter/CO/m3:saf1"
	, "  o  m3/m0:enter/FIS/in@prime"
	, "  o  m3/m0:enter/FIS/isgn@prime"
	, "  o  m3/m0:enter/FIS/loc@prime"
	, "  o  m3/m0:enter/FIS/osgn@prime"
	, "  o  m3/m0:enter/INV/m3:inv0"
	, "  o  m3/m0:enter/INV/m3:inv1"
	, "  o  m3/m0:enter/INV/m3:inv2"
	, " xxx m3/m0:enter/INV/m3:inv3"
	, "  o  m3/m0:enter/SCH"
	, "  o  m3/m0:leave/CO/m3:saf0"
	, "  o  m3/m0:leave/CO/m3:saf1"
	, "  o  m3/m0:leave/FIS/in@prime"
	, "  o  m3/m0:leave/FIS/isgn@prime"
	, "  o  m3/m0:leave/FIS/loc@prime"
	, "  o  m3/m0:leave/FIS/osgn@prime"
	, "  o  m3/m0:leave/INV/m3:inv0"
	, "  o  m3/m0:leave/INV/m3:inv1"
	, "  o  m3/m0:leave/INV/m3:inv2"
	, "  o  m3/m0:leave/INV/m3:inv3"
	, "  o  m3/m0:leave/SCH"
	, "  o  m3/m1:movein/CO/m3:saf0"
	, "  o  m3/m1:movein/CO/m3:saf1"
	, "  o  m3/m1:movein/FIS/in@prime"
	, "  o  m3/m1:movein/FIS/isgn@prime"
	, "  o  m3/m1:movein/FIS/loc@prime"
	, "  o  m3/m1:movein/FIS/osgn@prime"
	, "  o  m3/m1:movein/INV/m3:inv0"
	, "  o  m3/m1:movein/INV/m3:inv1"
	, "  o  m3/m1:movein/INV/m3:inv2"
	, "  o  m3/m1:movein/INV/m3:inv3"
	, "  o  m3/m1:movein/SCH"
	, "  o  m3/m1:moveout/CO/m3:saf0"
	, "  o  m3/m1:moveout/CO/m3:saf1"
	, "  o  m3/m1:moveout/FIS/in@prime"
	, "  o  m3/m1:moveout/FIS/isgn@prime"
	, "  o  m3/m1:moveout/FIS/loc@prime"
	, "  o  m3/m1:moveout/FIS/osgn@prime"
	, "  o  m3/m1:moveout/GRD/m3/3/REF/grd"
	, "  o  m3/m1:moveout/INV/m3:inv0"
	, "  o  m3/m1:moveout/INV/m3:inv1"
	, "  o  m3/m1:moveout/INV/m3:inv2"
	, "  o  m3/m1:moveout/INV/m3:inv3"
	, "  o  m3/m1:moveout/SCH"
	, "  o  m3/m1:moveout/SCH/m3/1/REF/delay/prog/lhs"
	, "  o  m3/m1:moveout/SCH/m3/1/REF/delay/prog/rhs"
	, "  o  m3/m1:moveout/SCH/m3/1/REF/delay/saf/lhs"
	, "  o  m3/m1:moveout/SCH/m3/1/REF/delay/saf/rhs"
	, "  o  m3/m1:moveout/SCH/m3/2/REF/replace/prog/lhs"
	, "  o  m3/m1:moveout/SCH/m3/2/REF/replace/prog/rhs"
	, "  o  m3/m1:moveout/SCH/m3/2/REF/replace/str"
	, "  o  m3/m3:ctr:plf/CO/m3:saf0"
	, "  o  m3/m3:ctr:plf/CO/m3:saf1"
	, "  o  m3/m3:ctr:plf/FIS/in@prime"
	, "  o  m3/m3:ctr:plf/FIS/isgn@prime"
	, "  o  m3/m3:ctr:plf/FIS/loc@prime"
	, "  o  m3/m3:ctr:plf/FIS/osgn@prime"
	, " xxx m3/m3:ctr:plf/INV/m3:inv0"
	, " xxx m3/m3:ctr:plf/INV/m3:inv1"
	, " xxx m3/m3:ctr:plf/INV/m3:inv2"
	, " xxx m3/m3:ctr:plf/INV/m3:inv3"
	, "  o  m3/m3:ctr:plf/SCH"
	, " xxx m3/m3:ctr:plf/TR/m3:tr0/EN"
	, "  o  m3/m3:ctr:plf/TR/m3:tr0/NEG"
	, "  o  m3/m3:prog0/REF/discharge/saf/lhs"
	, "  o  m3/m3:prog0/REF/discharge/saf/rhs"
	, "  o  m3/m3:prog0/REF/discharge/tr"
	, "passed 72 / 78" ]

verify :: Int -> String -> IO String
verify n path = do
    r <- parse_machine path
    case r of
        Right ms -> do
            (s,_,_) <- str_verify_machine $ ms !! n
            return $ unlines $ map (head . split "(") $ lines s
        x -> return $ show x
