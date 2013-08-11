module Document.Tests.Lambdas 
    ( test_case, test )
where

import Document.Document

import UnitB.PO

import Tests.UnitTest

test_case = Case "lambda expressions in the cube example" test True

test = test_cases 
            [ (StringCase "test 0, verification, lambda vs empty-fun" case0 result0)
            , (StringCase "test 1, verification, lambda vs ovl, mk-fun" case1 result1)
            ]

result0 = unlines 
     [ "  o  m0/INIT/FIS"
     , "  o  m0/INIT/INV/inv0"
     , "  o  m0/INIT/INV/inv1"
     , "  o  m0/INIT/INV/inv2"
     , "  o  m0/INIT/INV/inv3/goal (221,1)"
     , "  o  m0/INIT/INV/inv3/hypotheses (221,1)"
     , "  o  m0/INIT/INV/inv3/relation (221,1)"
     , "  o  m0/INIT/INV/inv3/step (223,1)"
     , "  o  m0/INIT/INV/inv3/step (225,1)"
     , "  o  m0/INIT/INV/inv3/step (229,1)"
     , "  o  m0/evt/FIS"
     , "  o  m0/evt/INV/inv0/goal (63,1)"
     , "  o  m0/evt/INV/inv0/hypotheses (63,1)"
     , "  o  m0/evt/INV/inv0/relation (63,1)"
     , "  o  m0/evt/INV/inv0/step (65,1)"
     , "  o  m0/evt/INV/inv0/step (67,1)"
     , "  o  m0/evt/INV/inv0/step (69,1)"
     , "  o  m0/evt/INV/inv0/step (71,1)"
     , "  o  m0/evt/INV/inv0/step (73,1)"
     , "  o  m0/evt/INV/inv1/goal (141,1)"
     , "  o  m0/evt/INV/inv1/hypotheses (141,1)"
     , "  o  m0/evt/INV/inv1/relation (141,1)"
     , "  o  m0/evt/INV/inv1/step (143,1)"
     , "  o  m0/evt/INV/inv1/step (145,1)"
     , "  o  m0/evt/INV/inv1/step (147,1)"
     , "  o  m0/evt/INV/inv1/step (149,1)"
     , "  o  m0/evt/INV/inv1/step (151,1)"
     , "  o  m0/evt/INV/inv1/step (153,1)"
     , "  o  m0/evt/INV/inv1/step (155,1)"
     , "  o  m0/evt/INV/inv2/easy (190,1)"
     , " xxx m0/evt/INV/inv3"
     , "  o  m0/evt/SCH"
     , "passed 31 / 32"
     ]

path0 = "tests/cubes-t0.tex"

case0 = do
    r <- parse_machine path0
    case r of
        Right [m] -> do
            (s,_,_) <- str_verify_machine m
            return s
        x -> return $ show x


result1 = unlines
     [ "  o  m0/INIT/FIS"
     , "  o  m0/INIT/INV/inv0"
     , "  o  m0/INIT/INV/inv1"
     , "  o  m0/INIT/INV/inv2"
     , "  o  m0/INIT/INV/inv3/goal (221,1)"
     , "  o  m0/INIT/INV/inv3/hypotheses (221,1)"
     , "  o  m0/INIT/INV/inv3/relation (221,1)"
     , "  o  m0/INIT/INV/inv3/step (223,1)"
     , "  o  m0/INIT/INV/inv3/step (225,1)"
     , "  o  m0/INIT/INV/inv3/step (229,1)"
     , "  o  m0/INIT/INV/inv4"
     , "  o  m0/evt/FIS"
     , "  o  m0/evt/INV/inv0/goal (63,1)"
     , "  o  m0/evt/INV/inv0/hypotheses (63,1)"
     , "  o  m0/evt/INV/inv0/relation (63,1)"
     , "  o  m0/evt/INV/inv0/step (65,1)"
     , "  o  m0/evt/INV/inv0/step (67,1)"
     , "  o  m0/evt/INV/inv0/step (69,1)"
     , "  o  m0/evt/INV/inv0/step (71,1)"
     , "  o  m0/evt/INV/inv0/step (73,1)"
     , "  o  m0/evt/INV/inv1/goal (141,1)"
     , "  o  m0/evt/INV/inv1/hypotheses (141,1)"
     , "  o  m0/evt/INV/inv1/relation (141,1)"
     , "  o  m0/evt/INV/inv1/step (143,1)"
     , "  o  m0/evt/INV/inv1/step (145,1)"
     , "  o  m0/evt/INV/inv1/step (147,1)"
     , "  o  m0/evt/INV/inv1/step (149,1)"
     , "  o  m0/evt/INV/inv1/step (151,1)"
     , "  o  m0/evt/INV/inv1/step (153,1)"
     , "  o  m0/evt/INV/inv1/step (155,1)"
     , "  o  m0/evt/INV/inv2/easy (190,1)"
     , "  o  m0/evt/INV/inv3/goal (240,1)"
     , "  o  m0/evt/INV/inv3/hypotheses (240,1)"
     , "  o  m0/evt/INV/inv3/relation (240,1)"
     , "  o  m0/evt/INV/inv3/step (242,1)"
     , "  o  m0/evt/INV/inv3/step (244,1)"
     , "  o  m0/evt/INV/inv3/step (246,1)"
     , "  o  m0/evt/INV/inv3/step (248,1)"
     , "  o  m0/evt/INV/inv3/step (250,1)"
     , "  o  m0/evt/INV/inv3/step (252,1)"
     , "  o  m0/evt/INV/inv4"
     , "  o  m0/evt/SCH"
     , "passed 42 / 42"
     ]

path1 = "tests/cubes-t1.tex"

case1 = do
    r <- parse_machine path1
    case r of
        Right [m] -> do
            (s,_,_) <- str_verify_machine m
            return s
        x -> return $ show x
