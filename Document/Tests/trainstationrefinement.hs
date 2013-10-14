module Document.Tests.TrainStationRefinement 
    ( test, test_case )
where

import Document.Machine

import UnitB.PO

import Tests.UnitTest

import Data.String.Utils

test_case = Case "train station example, with refinement" test True

test = test_cases
            [ Case "verify machine m0" (verify 0) result0
            , Case "verify machine m1" (verify 1) result1
            , Case "verify machine m2" (verify 2) result2
            ]

result0 = unlines
     [ "  o  m0/INIT/FIS/in"
     , "  o  m0/m0:enter/FIS/in@prime"
     , "  o  m0/m0:enter/SCH"
     , "  o  m0/m0:leave/FIS/in@prime"
     , "  o  m0/m0:leave/SCH"
     , "  o  m0/m0:leave/SCH/0/REF/weaken"
     , "  o  m0/m0:leave/TR/m0:tr0"
     , "  o  m0/m0:prog0/REF/discharge"
     , "passed 8 / 8"
     ]

result1 = unlines
     [ "  o  m1/INIT/FIS/in"
     , "  o  m1/INIT/FIS/loc"
     , "  o  m1/INIT/INV/inv0"
     , "  o  m1/SKIP/CO/saf0"
     , "  o  m1/SKIP/CO/saf1"
     , "  o  m1/SKIP/CO/saf2"
     , "  o  m1/SKIP/CO/saf3"
     , "  o  m1/m0:enter/CO/saf0"
     , "  o  m1/m0:enter/CO/saf1"
     , "  o  m1/m0:enter/CO/saf2"
     , "  o  m1/m0:enter/CO/saf3"
     , "  o  m1/m0:enter/FIS/in@prime"
     , "  o  m1/m0:enter/FIS/loc@prime"
     , "  o  m1/m0:enter/INV/inv0"
     , "  o  m1/m0:enter/SCH"
     , "  o  m1/m0:leave/CO/saf0"
     , "  o  m1/m0:leave/CO/saf1"
     , "  o  m1/m0:leave/CO/saf2"
     , "  o  m1/m0:leave/CO/saf3"
     , "  o  m1/m0:leave/FIS/in@prime"
     , "  o  m1/m0:leave/FIS/loc@prime"
     , "  o  m1/m0:leave/INV/inv0"
     , "  o  m1/m0:leave/SCH"
     , "  o  m1/m0:leave/SCH/1/REF/delay/prog/lhs"
     , "  o  m1/m0:leave/SCH/1/REF/delay/prog/rhs"
     , "  o  m1/m0:leave/SCH/1/REF/delay/saf/lhs"
     , "  o  m1/m0:leave/SCH/1/REF/delay/saf/rhs"
     , "  o  m1/m1:movein/CO/saf0"
     , "  o  m1/m1:movein/CO/saf1"
     , "  o  m1/m1:movein/CO/saf2"
     , "  o  m1/m1:movein/CO/saf3"
     , "  o  m1/m1:movein/FIS/in@prime"
     , "  o  m1/m1:movein/FIS/loc@prime"
     , "  o  m1/m1:movein/INV/inv0"
     , "  o  m1/m1:movein/SCH"
     , "  o  m1/m1:movein/SCH/0/REF/weaken"
     , "  o  m1/m1:movein/TR/m1:tr1/EN"
     , "  o  m1/m1:movein/TR/m1:tr1/NEG"
     , "  o  m1/m1:moveout/CO/saf0"
     , "  o  m1/m1:moveout/CO/saf1"
     , "  o  m1/m1:moveout/CO/saf2"
     , "  o  m1/m1:moveout/CO/saf3"
     , "  o  m1/m1:moveout/FIS/in@prime"
     , "  o  m1/m1:moveout/FIS/loc@prime"
     , "  o  m1/m1:moveout/INV/inv0"
     , "  o  m1/m1:moveout/SCH"
     , "  o  m1/m1:moveout/SCH/0/REF/weaken"
     , "  o  m1/m1:moveout/TR/m1:tr0"
     , "  o  m1/m1:prog0/REF/disjunction/lhs"
     , "  o  m1/m1:prog0/REF/disjunction/rhs"
     , "  o  m1/prog1/REF/transitivity"
     , "  o  m1/prog2/REF/implication"
     , "  o  m1/prog3/REF/discharge"
     , "  o  m1/prog4/REF/discharge"
     , "passed 54 / 54"
     ]

result2 = unlines
	[ "  o  m2/INIT/FIS/in"
	, "  o  m2/INIT/FIS/loc"
	, "  o  m2/INIT/INV/m2:inv0"
	, "  o  m2/SKIP/CO/m2:saf0"
	, "  o  m2/m0:enter/CO/m2:saf0"
	, "  o  m2/m0:enter/FIS/in@prime"
	, "  o  m2/m0:enter/FIS/loc@prime"
	, "  o  m2/m0:enter/INV/m2:inv0"
	, "  o  m2/m0:enter/SCH"
	, "  o  m2/m0:leave/CO/m2:saf0"
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
	, "  o  m2/m1:movein/CO/m2:saf0"
	, "  o  m2/m1:movein/FIS/in@prime"
	, "  o  m2/m1:movein/FIS/loc@prime"
	, "  o  m2/m1:movein/INV/m2:inv0"
	, "  o  m2/m1:movein/SCH"
	, "  o  m2/m1:movein/SCH/1/REF/delay/prog/lhs"
	, "  o  m2/m1:movein/SCH/1/REF/delay/prog/rhs"
	, "  o  m2/m1:movein/SCH/1/REF/delay/saf/lhs"
	, "  o  m2/m1:movein/SCH/1/REF/delay/saf/rhs"
	, "  o  m2/m1:moveout/CO/m2:saf0"
	, "  o  m2/m1:moveout/FIS/in@prime"
	, "  o  m2/m1:moveout/FIS/loc@prime"
	, "  o  m2/m1:moveout/INV/m2:inv0"
	, "  o  m2/m1:moveout/SCH"
	, "  o  m2/m1:moveout/SCH/1/REF/replace/prog/lhs"
	, "  o  m2/m1:moveout/SCH/1/REF/replace/prog/rhs"
	, "  o  m2/m1:moveout/SCH/1/REF/replace/str"
	, " xxx m2/m2:prog0/REF/add"
	, " xxx m2/m2:prog1/REF/add"
	, "passed 53 / 55"
	]

path0 = "Tests/train-station-ref.tex"

verify n = do
    r <- parse_machine path0
    case r of
        Right ms -> do
            (s,_,_) <- str_verify_machine $ ms !! n
            return $ unlines $ map (head . split "(") $ lines s
        x -> return $ show x
