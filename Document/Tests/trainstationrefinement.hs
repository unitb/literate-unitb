module Document.Tests.TrainStationRefinement 
    ( test, test_case )
where

import Document.Machine

import UnitB.PO

import Tests.UnitTest

test_case = Case "train station example, with refinement" test True

test = test_cases
            [ Case "verify machine m0" (verify 0) result0
            , Case "verify machine m1" (verify 1) result1
            ]

result0 = unlines
     [ "  o  m0/INIT/FIS/in"
     , "  o  m0/m0:enter/FIS/in@prime"
     , "  o  m0/m0:enter/SCH"
     , "  o  m0/m0:leave/FIS/in@prime"
     , "  o  m0/m0:leave/SCH"
     , "  o  m0/m0:leave/SCH/0/REF/weaken"
     , "  o  m0/m0:leave/TR/tr0"
     , "  o  m0/prog0/REF/discharge"
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
     , "  o  m1/m1:movein/TR/tr1"
     , "  o  m1/m1:moveout/CO/saf0"
     , "  o  m1/m1:moveout/CO/saf1"
     , "  o  m1/m1:moveout/CO/saf2"
     , "  o  m1/m1:moveout/CO/saf3"
     , "  o  m1/m1:moveout/FIS/in@prime"
     , "  o  m1/m1:moveout/FIS/loc@prime"
     , "  o  m1/m1:moveout/INV/inv0"
     , "  o  m1/m1:moveout/SCH"
     , "  o  m1/m1:moveout/SCH/0/REF/weaken"
     , "  o  m1/m1:moveout/TR/tr0"
     , "  o  m1/prog0/REF/disjunction/lhs"
     , "  o  m1/prog0/REF/disjunction/rhs"
     , "  o  m1/prog1/REF/transitivity"
     , "  o  m1/prog2/REF/implication"
     , "  o  m1/prog3/REF/discharge"
     , "  o  m1/prog4/REF/discharge"
     , "passed 53 / 53"
     ]

path0 = "Tests/train-station-ref.tex"

verify n = do
    r <- parse_machine path0
    case r of
        Right ms -> do
            (s,_,_) <- str_verify_machine $ ms !! n
            return s
        x -> return $ show x
