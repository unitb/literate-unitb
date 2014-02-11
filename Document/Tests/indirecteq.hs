module Document.Tests.IndirectEq where

import Document.Document

import UnitB.PO

    -- Libraries
import Data.String.Utils

import Tests.UnitTest


test_case = Case "train station example, with sets" test True

test = test_cases
            [ Case "verify proof with galois connections" (verify 0 path0) result0
            ]

path0 = "tests/indirect-equality.tex"

result0 = unlines 
	[ " xxx m0/INIT/INV/inv0/assertion/indirect:eq/easy "
	, "  o  m0/INIT/INV/inv0/assertion/new:goal/goal "
	, "  o  m0/INIT/INV/inv0/assertion/new:goal/hypotheses "
	, "  o  m0/INIT/INV/inv0/assertion/new:goal/relation "
	, "  o  m0/INIT/INV/inv0/assertion/new:goal/step "
	, "  o  m0/INIT/INV/inv0/assertion/new:goal/step "
	, "  o  m0/INIT/INV/inv0/assertion/new:goal/step "
	, "  o  m0/INIT/INV/inv0/assertion/new:goal/step "
	, "  o  m0/INIT/INV/inv0/main goal/easy "
	, "  o  m0/INIT/INV/inv1/completeness "
	, "  o  m0/INIT/INV/inv1/part 1/easy "
	, "  o  m0/INIT/INV/inv1/part 2/goal "
	, "  o  m0/INIT/INV/inv1/part 2/hypotheses "
	, "  o  m0/INIT/INV/inv1/part 2/new assumption "
	, "  o  m0/INIT/INV/inv1/part 2/relation "
	, "  o  m0/INIT/INV/inv1/part 2/step "
	, "  o  m0/INIT/INV/inv1/part 2/step "
	, "  o  m0/INIT/INV/inv1/part 2/step "
	, "passed 17 / 18" ]
	
verify n path = do
    r <- parse_machine path
    case r of
        Right ms -> do
            (s,_,_) <- str_verify_machine $ ms !! n
            return $ unlines $ map (head . split "(") $ lines s
        x -> return $ show x
