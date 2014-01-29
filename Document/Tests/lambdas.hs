module Document.Tests.Lambdas 
    ( test_case, test
    , part0, part1
    , part2, part3 )
where

    -- Modules
import Document.Document

import Logic.Const
import Logic.Expr

import Theories.FunctionTheory

import UnitB.AST
import UnitB.PO

    -- Libraries
import Control.Monad.Trans.Either

import Data.Map

import Tests.UnitTest

import Utilities.Syntactic

test_case = Case "lambda expressions in the cube example" test True

test = test_cases
            [ (Case "part 0" part0 True)
            , (Case "part 1" part1 True) 
            , (Case "part 2" part2 True) 
            , (Case "part 3" part3 True) 
            ]            
part0 = test_cases
            [ (StringCase "test 0, verification, lambda vs empty-fun" (verify path0) result0)
            , (StringCase "test 1, verification, lambda vs ovl, mk-fun" (verify path1) result1)
            , (StringCase "test 2, verification, lambda vs apply" (verify path2) result2)
            ]            
part1 = test_cases
            [ (StringCase "test 3, verification, set comprehension, failed proof" (verify path3) result3)
            , (Case "test 4, adding a progress property" case4 result4)
            , (Case "test 5, unless properties" case5 result5)
            ]            
part2 = test_cases
            [ (StringCase "test 6, verify progress refinement" (verify path6) result6)
            , (StringCase "test 7, verify refinement rules" (verify path7) result7)
            , (StringCase "test 8, verify refinement rules" (verify path8) result8)
            ]            
part3 = test_cases
            [ (StringCase "test 9, verify disjunction rule" (verify path9) result9)
            , (StringCase "test 10, error: cyclic proof" (verify path10) result10)
            ]

result0 = unlines 
     [ "  o  m0/INIT/FIS/a"
     , "  o  m0/INIT/FIS/b"
     , "  o  m0/INIT/FIS/c"
     , "  o  m0/INIT/FIS/f"
     , "  o  m0/INIT/FIS/n"
     , "  o  m0/INIT/INV/inv0"
     , "  o  m0/INIT/INV/inv1"
     , "  o  m0/INIT/INV/inv2"
     , "  o  m0/INIT/INV/inv3/goal (221,1)"
     , "  o  m0/INIT/INV/inv3/hypotheses (221,1)"
     , "  o  m0/INIT/INV/inv3/relation (221,1)"
     , "  o  m0/INIT/INV/inv3/step (223,1)"
     , "  o  m0/INIT/INV/inv3/step (225,1)"
     , "  o  m0/INIT/INV/inv3/step (229,1)"
     , "  o  m0/evt/FIS/a@prime"
     , "  o  m0/evt/FIS/b@prime"
     , "  o  m0/evt/FIS/c@prime"
     , "  o  m0/evt/FIS/f@prime"
     , "  o  m0/evt/FIS/n@prime"
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
     , "passed 39 / 40"
     ]

path0 = "tests/cubes-t0.tex"

result1 = unlines
     [ "  o  m0/INIT/FIS/a"
     , "  o  m0/INIT/FIS/b"
     , "  o  m0/INIT/FIS/c"
     , "  o  m0/INIT/FIS/f"
     , "  o  m0/INIT/FIS/n"
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
     , "  o  m0/evt/FIS/a@prime"
     , "  o  m0/evt/FIS/b@prime"
     , "  o  m0/evt/FIS/c@prime"
     , "  o  m0/evt/FIS/f@prime"
     , "  o  m0/evt/FIS/n@prime"
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
     , "passed 50 / 50"
     ]

path1 = "tests/cubes-t1.tex"

result2 = unlines
     [ "  o  m0/INIT/FIS/a"
     , "  o  m0/INIT/FIS/b"
     , "  o  m0/INIT/FIS/c"
     , "  o  m0/INIT/FIS/f"
     , "  o  m0/INIT/FIS/n"
     , "  o  m0/INIT/INV/inv0"
     , "  o  m0/INIT/INV/inv1"
     , "  o  m0/INIT/INV/inv2"
     , "  o  m0/INIT/INV/inv3/goal (222,1)"
     , "  o  m0/INIT/INV/inv3/hypotheses (222,1)"
     , "  o  m0/INIT/INV/inv3/relation (222,1)"
     , "  o  m0/INIT/INV/inv3/step (224,1)"
     , "  o  m0/INIT/INV/inv3/step (226,1)"
     , "  o  m0/INIT/INV/inv3/step (230,1)"
     , "  o  m0/INIT/INV/inv4"
     , "  o  m0/INIT/INV/inv5"
     , "  o  m0/evt/FIS/a@prime"
     , "  o  m0/evt/FIS/b@prime"
     , "  o  m0/evt/FIS/c@prime"
     , "  o  m0/evt/FIS/f@prime"
     , "  o  m0/evt/FIS/n@prime"
     , "  o  m0/evt/INV/inv0/goal (64,1)"
     , "  o  m0/evt/INV/inv0/hypotheses (64,1)"
     , "  o  m0/evt/INV/inv0/relation (64,1)"
     , "  o  m0/evt/INV/inv0/step (66,1)"
     , "  o  m0/evt/INV/inv0/step (68,1)"
     , "  o  m0/evt/INV/inv0/step (70,1)"
     , "  o  m0/evt/INV/inv0/step (72,1)"
     , "  o  m0/evt/INV/inv0/step (74,1)"
     , "  o  m0/evt/INV/inv1/goal (142,1)"
     , "  o  m0/evt/INV/inv1/hypotheses (142,1)"
     , "  o  m0/evt/INV/inv1/relation (142,1)"
     , "  o  m0/evt/INV/inv1/step (144,1)"
     , "  o  m0/evt/INV/inv1/step (146,1)"
     , "  o  m0/evt/INV/inv1/step (148,1)"
     , "  o  m0/evt/INV/inv1/step (150,1)"
     , "  o  m0/evt/INV/inv1/step (152,1)"
     , "  o  m0/evt/INV/inv1/step (154,1)"
     , "  o  m0/evt/INV/inv1/step (156,1)"
     , "  o  m0/evt/INV/inv2/easy (191,1)"
     , "  o  m0/evt/INV/inv3/goal (241,1)"
     , "  o  m0/evt/INV/inv3/hypotheses (241,1)"
     , "  o  m0/evt/INV/inv3/relation (241,1)"
     , "  o  m0/evt/INV/inv3/step (243,1)"
     , "  o  m0/evt/INV/inv3/step (245,1)"
     , "  o  m0/evt/INV/inv3/step (247,1)"
     , "  o  m0/evt/INV/inv3/step (253,1)"
     , "  o  m0/evt/INV/inv3/step (255,1)"
     , "  o  m0/evt/INV/inv4"
     , "  o  m0/evt/INV/inv5/assertion/asm0/easy (298,1)"
     , "  o  m0/evt/INV/inv5/main goal/goal (279,1)"
     , "  o  m0/evt/INV/inv5/main goal/hypotheses (279,1)"
     , "  o  m0/evt/INV/inv5/main goal/relation (279,1)"
     , "  o  m0/evt/INV/inv5/main goal/step (281,1)"
     , "  o  m0/evt/INV/inv5/main goal/step (283,1)"
     , "  o  m0/evt/INV/inv5/main goal/step (285,1)"
     , " xxx m0/evt/INV/inv5/main goal/step (287,1)"
--     , "  o  m0/evt/INV/inv5/main goal/step (287,1)"
     , "  o  m0/evt/INV/inv5/main goal/step (290,1)"
     , "  o  m0/evt/SCH"
     , "passed 58 / 59"
     ]

path2 = "tests/cubes-t2.tex"

result3 = unlines
     [ "  o  m0/INIT/FIS/a"
     , "  o  m0/INIT/FIS/b"
     , "  o  m0/INIT/FIS/c"
     , "  o  m0/INIT/FIS/f"
     , "  o  m0/INIT/FIS/n"
     , "  o  m0/INIT/INV/inv0"
     , "  o  m0/INIT/INV/inv1"
     , "  o  m0/INIT/INV/inv2"
     , "  o  m0/INIT/INV/inv3/goal (222,1)"
     , "  o  m0/INIT/INV/inv3/hypotheses (222,1)"
     , "  o  m0/INIT/INV/inv3/relation (222,1)"
     , "  o  m0/INIT/INV/inv3/step (224,1)"
     , "  o  m0/INIT/INV/inv3/step (226,1)"
     , "  o  m0/INIT/INV/inv3/step (230,1)"
     , "  o  m0/INIT/INV/inv4"
     , "  o  m0/INIT/INV/inv5"
     , "  o  m0/INIT/INV/inv6"
     , "  o  m0/evt/FIS/a@prime"
     , "  o  m0/evt/FIS/b@prime"
     , "  o  m0/evt/FIS/c@prime"
     , "  o  m0/evt/FIS/f@prime"
     , "  o  m0/evt/FIS/n@prime"
     , "  o  m0/evt/INV/inv0/goal (64,1)"
     , "  o  m0/evt/INV/inv0/hypotheses (64,1)"
     , "  o  m0/evt/INV/inv0/relation (64,1)"
     , "  o  m0/evt/INV/inv0/step (66,1)"
     , "  o  m0/evt/INV/inv0/step (68,1)"
     , "  o  m0/evt/INV/inv0/step (70,1)"
     , "  o  m0/evt/INV/inv0/step (72,1)"
     , "  o  m0/evt/INV/inv0/step (74,1)"
     , "  o  m0/evt/INV/inv1/goal (142,1)"
     , "  o  m0/evt/INV/inv1/hypotheses (142,1)"
     , "  o  m0/evt/INV/inv1/relation (142,1)"
     , "  o  m0/evt/INV/inv1/step (144,1)"
     , "  o  m0/evt/INV/inv1/step (146,1)"
     , "  o  m0/evt/INV/inv1/step (148,1)"
     , "  o  m0/evt/INV/inv1/step (150,1)"
     , "  o  m0/evt/INV/inv1/step (152,1)"
     , "  o  m0/evt/INV/inv1/step (154,1)"
     , "  o  m0/evt/INV/inv1/step (156,1)"
     , "  o  m0/evt/INV/inv2/easy (191,1)"
     , "  o  m0/evt/INV/inv3/goal (241,1)"
     , "  o  m0/evt/INV/inv3/hypotheses (241,1)"
     , "  o  m0/evt/INV/inv3/relation (241,1)"
     , "  o  m0/evt/INV/inv3/step (243,1)"
     , "  o  m0/evt/INV/inv3/step (245,1)"
     , "  o  m0/evt/INV/inv3/step (247,1)"
     , "  o  m0/evt/INV/inv3/step (253,1)"
     , "  o  m0/evt/INV/inv3/step (255,1)"
     , "  o  m0/evt/INV/inv4"
     , "  o  m0/evt/INV/inv5/assertion/asm0/easy (298,1)"
     , "  o  m0/evt/INV/inv5/main goal/goal (279,1)"
     , "  o  m0/evt/INV/inv5/main goal/hypotheses (279,1)"
     , "  o  m0/evt/INV/inv5/main goal/relation (279,1)"
     , "  o  m0/evt/INV/inv5/main goal/step (281,1)"
     , "  o  m0/evt/INV/inv5/main goal/step (283,1)"
     , "  o  m0/evt/INV/inv5/main goal/step (285,1)"
     , " xxx m0/evt/INV/inv5/main goal/step (287,1)"
--     , "  o  m0/evt/INV/inv5/main goal/step (287,1)"
     , "  o  m0/evt/INV/inv5/main goal/step (290,1)"
     , " xxx m0/evt/INV/inv6"
     , "  o  m0/evt/SCH"
     , "passed 59 / 61"
     ]

path3 = "tests/cubes-t3.tex"

result4 = either g Right (do
        q0 <- f `mzeq` zlambda [i_decl] 
            (mzle (mzint 0) i `mzand` mzless i bigN) 
            (mzpow i $ mzint 3)
        q1 <- bigN `mzeq` n
        q2 <- (k `mzless` n) `mzor` (n `mzeq` bigN)
        p1  <- (n `mzeq` k)
        p2  <- mzall [k `mzle` n, n `mzeq` k, mznot (n `mzeq` bigN)]
        p3 <-  mzall [n `mzeq` k, mznot (n `mzeq` bigN)]
        q3 <- mzor 
                (mzle k n `mzand` mznot (k `mzeq` n)) 
                (n `mzeq` bigN)
        q4 <- mznot (n `mzeq` k)
        return $ fromList 
            [   (label "prog0", LeadsTo [] ztrue q0)
            ,   (label "prog1", LeadsTo [] ztrue q1)
            ,   (label "prog2", LeadsTo [] p1 q2)
            ,   (label "prog3", LeadsTo [] p2 q3)
            ,   (label "prog4", LeadsTo [] p3 q4)
            ])
    where
        (k,_)      = var "k" int
        (i,i_decl) = var "i" int
        (f,_)      = var "f" (fun_type int int)
        (n,_)      = var "n" int
        (bigN,_)   = var "N" int
        g x = Left [Error x (LI path4 0 0)]

path4 = "tests/cubes-t6.tex"

case4 = runEitherT (do
    ms <- EitherT $ parse_machine path4 :: EitherT [Error] IO [Machine]
    case ms of
        [m] -> right $ progress $ props $ m
        _   -> left [Error "a single machine is expected" (LI "" 0 0)])

result5 = either g Right (do
        q0  <- bigN `mzeq` n
        p0  <- (k `mzle` n)
        q1  <- mznot (n `mzeq` k)
        p1  <- mzall
                [ n `mzeq` k
                , mznot (n `mzeq` bigN)
                ]
        return $ fromList 
            [   (label "saf0", Unless [k_decl] p0 q0 Nothing)
            ,   (label "saf1", Unless [k_decl] p1 q1 Nothing)
            ])
    where
        (k,k_decl) = var "k" int
        (n,_)      = var "n" int
        (bigN,_)   = var "N" int
        g x = Left [Error x (LI path4 0 0)]

case5 = runEitherT (do
    ms <- EitherT $ parse_machine path4 :: EitherT [Error] IO [Machine]
    case ms of
        [m] -> right $ safety $ props $ m
        _   -> left [Error "a single machine is expected" (LI "" 0 0)])

result6 = unlines
     [ "  o  m0/INIT/FIS/a"
     , "  o  m0/INIT/FIS/b"
     , "  o  m0/INIT/FIS/c"
     , "  o  m0/INIT/FIS/f"
     , "  o  m0/INIT/FIS/n"
     , "  o  m0/INIT/INV/inv0"
     , "  o  m0/INIT/INV/inv1"
     , "  o  m0/INIT/INV/inv2"
     , "  o  m0/INIT/INV/inv3/goal (224,1)"
     , "  o  m0/INIT/INV/inv3/hypotheses (224,1)"
     , "  o  m0/INIT/INV/inv3/relation (224,1)"
     , "  o  m0/INIT/INV/inv3/step (226,1)"
     , "  o  m0/INIT/INV/inv3/step (228,1)"
     , "  o  m0/INIT/INV/inv3/step (232,1)"
     , "  o  m0/INIT/INV/inv4"
     , "  o  m0/INIT/INV/inv5"
     , "  o  m0/INIT/INV/inv6"
     , " xxx m0/INIT/INV/inv8"
     , "  o  m0/SKIP/CO/saf0"
     , "  o  m0/evt/CO/saf0"
     , "  o  m0/evt/FIS/a@prime"
     , "  o  m0/evt/FIS/b@prime"
     , "  o  m0/evt/FIS/c@prime"
     , "  o  m0/evt/FIS/f@prime"
     , "  o  m0/evt/FIS/n@prime"
     , "  o  m0/evt/INV/inv0/goal (66,1)"
     , "  o  m0/evt/INV/inv0/hypotheses (66,1)"
     , "  o  m0/evt/INV/inv0/relation (66,1)"
     , "  o  m0/evt/INV/inv0/step (68,1)"
     , "  o  m0/evt/INV/inv0/step (70,1)"
     , "  o  m0/evt/INV/inv0/step (72,1)"
     , "  o  m0/evt/INV/inv0/step (74,1)"
     , "  o  m0/evt/INV/inv0/step (76,1)"
     , "  o  m0/evt/INV/inv1/goal (144,1)"
     , "  o  m0/evt/INV/inv1/hypotheses (144,1)"
     , "  o  m0/evt/INV/inv1/relation (144,1)"
     , "  o  m0/evt/INV/inv1/step (146,1)"
     , "  o  m0/evt/INV/inv1/step (148,1)"
     , "  o  m0/evt/INV/inv1/step (150,1)"
     , "  o  m0/evt/INV/inv1/step (152,1)"
     , "  o  m0/evt/INV/inv1/step (154,1)"
     , "  o  m0/evt/INV/inv1/step (156,1)"
     , "  o  m0/evt/INV/inv1/step (158,1)"
     , "  o  m0/evt/INV/inv2/easy (193,1)"
     , "  o  m0/evt/INV/inv3/goal (243,1)"
     , "  o  m0/evt/INV/inv3/hypotheses (243,1)"
     , "  o  m0/evt/INV/inv3/relation (243,1)"
     , "  o  m0/evt/INV/inv3/step (245,1)"
     , "  o  m0/evt/INV/inv3/step (247,1)"
     , "  o  m0/evt/INV/inv3/step (249,1)"
     , "  o  m0/evt/INV/inv3/step (255,1)"
     , "  o  m0/evt/INV/inv3/step (257,1)"
     , "  o  m0/evt/INV/inv4"
     , "  o  m0/evt/INV/inv5/assertion/asm0/easy (300,1)"
     , "  o  m0/evt/INV/inv5/main goal/goal (281,1)"
     , "  o  m0/evt/INV/inv5/main goal/hypotheses (281,1)"
     , "  o  m0/evt/INV/inv5/main goal/relation (281,1)"
     , "  o  m0/evt/INV/inv5/main goal/step (283,1)"
     , "  o  m0/evt/INV/inv5/main goal/step (285,1)"
     , "  o  m0/evt/INV/inv5/main goal/step (287,1)"
     , " xxx m0/evt/INV/inv5/main goal/step (289,1)"
--     , "  o  m0/evt/INV/inv5/main goal/step (289,1)"
     , "  o  m0/evt/INV/inv5/main goal/step (292,1)"
     , "  o  m0/evt/INV/inv6/goal (310,1)"
     , "  o  m0/evt/INV/inv6/hypotheses (310,1)"
     , "  o  m0/evt/INV/inv6/relation (310,1)"
     , "  o  m0/evt/INV/inv6/step (312,1)"
     , " xxx m0/evt/INV/inv6/step (314,1)"
     , "  o  m0/evt/INV/inv6/step (316,1)"
     , " xxx m0/evt/INV/inv6/step (318,1)"
     , " xxx m0/evt/INV/inv6/step (320,1)"
     , "  o  m0/evt/INV/inv8"
     , "  o  m0/evt/SCH"
     , "  o  m0/evt/SCH/m0/0/REF/weaken"
     , "  o  m0/evt/TR/tr0/EN"
     , "  o  m0/evt/TR/tr0/NEG"
     , "  o  m0/prog0/REF/monotonicity/lhs"
     , "  o  m0/prog0/REF/monotonicity/rhs"
     , " xxx m0/prog1/REF/add" 
     , "  o  m0/prog2/REF/trading/lhs"
     , "  o  m0/prog2/REF/trading/rhs"
     , "  o  m0/prog3/REF/PSP/lhs"
     , "  o  m0/prog3/REF/PSP/rhs"
     , "  o  m0/prog4/REF/discharge/tr/lhs"
     , " xxx m0/prog4/REF/discharge/tr/rhs"
     , "passed 77 / 84"
     ]

path6 = "tests/cubes-t5.tex"

result7 = unlines
     [ "  o  m0/INIT/FIS/a"
     , "  o  m0/INIT/FIS/b"
     , "  o  m0/INIT/FIS/c"
     , "  o  m0/INIT/FIS/f"
     , "  o  m0/INIT/FIS/n"
     , "  o  m0/INIT/INV/inv0"
     , "  o  m0/INIT/INV/inv1"
     , "  o  m0/INIT/INV/inv2"
     , "  o  m0/INIT/INV/inv3/goal (224,1)"
     , "  o  m0/INIT/INV/inv3/hypotheses (224,1)"
     , "  o  m0/INIT/INV/inv3/relation (224,1)"
     , "  o  m0/INIT/INV/inv3/step (226,1)"
     , "  o  m0/INIT/INV/inv3/step (228,1)"
     , "  o  m0/INIT/INV/inv3/step (232,1)"
     , "  o  m0/INIT/INV/inv4"
     , "  o  m0/INIT/INV/inv5"
     , "  o  m0/INIT/INV/inv6"
     , "  o  m0/SKIP/CO/saf0"
     , "  o  m0/evt/CO/saf0"
     , "  o  m0/evt/FIS/a@prime"
     , "  o  m0/evt/FIS/b@prime"
     , "  o  m0/evt/FIS/c@prime"
     , "  o  m0/evt/FIS/f@prime"
     , "  o  m0/evt/FIS/n@prime"
     , "  o  m0/evt/INV/inv0/goal (66,1)"
     , "  o  m0/evt/INV/inv0/hypotheses (66,1)"
     , "  o  m0/evt/INV/inv0/relation (66,1)"
     , "  o  m0/evt/INV/inv0/step (68,1)"
     , "  o  m0/evt/INV/inv0/step (70,1)"
     , "  o  m0/evt/INV/inv0/step (72,1)"
     , "  o  m0/evt/INV/inv0/step (74,1)"
     , "  o  m0/evt/INV/inv0/step (76,1)"
     , "  o  m0/evt/INV/inv1/goal (144,1)"
     , "  o  m0/evt/INV/inv1/hypotheses (144,1)"
     , "  o  m0/evt/INV/inv1/relation (144,1)"
     , "  o  m0/evt/INV/inv1/step (146,1)"
     , "  o  m0/evt/INV/inv1/step (148,1)"
     , "  o  m0/evt/INV/inv1/step (150,1)"
     , "  o  m0/evt/INV/inv1/step (152,1)"
     , "  o  m0/evt/INV/inv1/step (154,1)"
     , "  o  m0/evt/INV/inv1/step (156,1)"
     , "  o  m0/evt/INV/inv1/step (158,1)"
     , "  o  m0/evt/INV/inv2/easy (193,1)"
     , "  o  m0/evt/INV/inv3/goal (243,1)"
     , "  o  m0/evt/INV/inv3/hypotheses (243,1)"
     , "  o  m0/evt/INV/inv3/relation (243,1)"
     , "  o  m0/evt/INV/inv3/step (245,1)"
     , "  o  m0/evt/INV/inv3/step (247,1)"
     , "  o  m0/evt/INV/inv3/step (249,1)"
     , "  o  m0/evt/INV/inv3/step (255,1)"
     , "  o  m0/evt/INV/inv3/step (257,1)"
     , "  o  m0/evt/INV/inv4"
     , "  o  m0/evt/INV/inv5/assertion/asm0/easy (300,1)"
     , "  o  m0/evt/INV/inv5/main goal/goal (281,1)"
     , "  o  m0/evt/INV/inv5/main goal/hypotheses (281,1)"
     , "  o  m0/evt/INV/inv5/main goal/relation (281,1)"
     , "  o  m0/evt/INV/inv5/main goal/step (283,1)"
     , "  o  m0/evt/INV/inv5/main goal/step (285,1)"
     , "  o  m0/evt/INV/inv5/main goal/step (287,1)"
--     , "  o  m0/evt/INV/inv5/main goal/step (289,1)"
     , " xxx m0/evt/INV/inv5/main goal/step (289,1)"
     , "  o  m0/evt/INV/inv5/main goal/step (292,1)"
     , "  o  m0/evt/INV/inv6/goal (310,1)"
     , "  o  m0/evt/INV/inv6/hypotheses (310,1)"
     , "  o  m0/evt/INV/inv6/relation (310,1)"
     , "  o  m0/evt/INV/inv6/step (312,1)"
     , " xxx m0/evt/INV/inv6/step (314,1)"
     , "  o  m0/evt/INV/inv6/step (316,1)"
     , " xxx m0/evt/INV/inv6/step (318,1)"
     , " xxx m0/evt/INV/inv6/step (320,1)"
     , "  o  m0/evt/SCH"
     , "  o  m0/prog0/REF/monotonicity/lhs"
     , "  o  m0/prog0/REF/monotonicity/rhs"
     , " xxx m0/prog1/REF/add"
     , " xxx m0/prog10/REF/add"
     , " xxx m0/prog2/REF/trading/lhs"
     , "  o  m0/prog2/REF/trading/rhs"
     , " xxx m0/prog3/REF/PSP/lhs"
     , " xxx m0/prog3/REF/PSP/rhs"
     , " xxx m0/prog4/REF/add"
     , " xxx m0/prog5/REF/transitivity/lhs"
     , "  o  m0/prog5/REF/transitivity/mhs"
     , "  o  m0/prog5/REF/transitivity/rhs"
     , " xxx m0/prog6/REF/add"
     , " xxx m0/prog7/REF/add"
     , "  o  m0/prog8/REF/transitivity/lhs"
     , "  o  m0/prog8/REF/transitivity/mhs"
     , "  o  m0/prog8/REF/transitivity/rhs"
     , " xxx m0/prog9/REF/add"
     , "passed 74 / 88"
     ]

path7 = "tests/cubes-t4.tex"

result8 = unlines
     [ "  o  m0/INIT/FIS/a"
     , "  o  m0/INIT/FIS/b"
     , "  o  m0/INIT/FIS/c"
     , "  o  m0/INIT/FIS/f"
     , "  o  m0/INIT/FIS/n"
     , "  o  m0/INIT/INV/inv0"
     , "  o  m0/INIT/INV/inv1"
     , "  o  m0/INIT/INV/inv2"
     , "  o  m0/INIT/INV/inv3/goal (224,1)"
     , "  o  m0/INIT/INV/inv3/hypotheses (224,1)"
     , "  o  m0/INIT/INV/inv3/relation (224,1)"
     , "  o  m0/INIT/INV/inv3/step (226,1)"
     , "  o  m0/INIT/INV/inv3/step (228,1)"
     , "  o  m0/INIT/INV/inv3/step (232,1)"
     , "  o  m0/INIT/INV/inv4"
     , "  o  m0/INIT/INV/inv5"
     , "  o  m0/INIT/INV/inv6"
     , "  o  m0/INIT/INV/inv7"
     , "  o  m0/SKIP/CO/saf0"
     , "  o  m0/SKIP/CO/saf1"
     , "  o  m0/evt/CO/saf0"
     , "  o  m0/evt/CO/saf1"
     , "  o  m0/evt/FIS/a@prime"
     , "  o  m0/evt/FIS/b@prime"
     , "  o  m0/evt/FIS/c@prime"
     , "  o  m0/evt/FIS/f@prime"
     , "  o  m0/evt/FIS/n@prime"
     , "  o  m0/evt/INV/inv0/goal (66,1)"
     , "  o  m0/evt/INV/inv0/hypotheses (66,1)"
     , "  o  m0/evt/INV/inv0/relation (66,1)"
     , "  o  m0/evt/INV/inv0/step (68,1)"
     , "  o  m0/evt/INV/inv0/step (70,1)"
     , "  o  m0/evt/INV/inv0/step (72,1)"
     , "  o  m0/evt/INV/inv0/step (74,1)"
     , "  o  m0/evt/INV/inv0/step (76,1)"
     , "  o  m0/evt/INV/inv1/goal (144,1)"
     , "  o  m0/evt/INV/inv1/hypotheses (144,1)"
     , "  o  m0/evt/INV/inv1/relation (144,1)"
     , "  o  m0/evt/INV/inv1/step (146,1)"
     , "  o  m0/evt/INV/inv1/step (148,1)"
     , "  o  m0/evt/INV/inv1/step (150,1)"
     , "  o  m0/evt/INV/inv1/step (152,1)"
     , "  o  m0/evt/INV/inv1/step (154,1)"
     , "  o  m0/evt/INV/inv1/step (156,1)"
     , "  o  m0/evt/INV/inv1/step (158,1)"
     , "  o  m0/evt/INV/inv2/easy (193,1)"
     , "  o  m0/evt/INV/inv3/goal (243,1)"
     , "  o  m0/evt/INV/inv3/hypotheses (243,1)"
     , "  o  m0/evt/INV/inv3/relation (243,1)"
     , "  o  m0/evt/INV/inv3/step (245,1)"
     , "  o  m0/evt/INV/inv3/step (247,1)"
     , "  o  m0/evt/INV/inv3/step (249,1)"
     , "  o  m0/evt/INV/inv3/step (255,1)"
     , "  o  m0/evt/INV/inv3/step (257,1)"
     , "  o  m0/evt/INV/inv4"
--     , "  o  m0/evt/INV/inv5/assertion/asm0/easy (300,1)"
     , "  o  m0/evt/INV/inv5/goal (281,1)"
     , "  o  m0/evt/INV/inv5/hypotheses (281,1)"
     , "  o  m0/evt/INV/inv5/relation (281,1)"
     , "  o  m0/evt/INV/inv5/step (283,1)"
     , "  o  m0/evt/INV/inv5/step (285,1)"
     , "  o  m0/evt/INV/inv5/step (287,1)"
     , " xxx m0/evt/INV/inv5/step (289,1)"
     , "  o  m0/evt/INV/inv5/step (292,1)"
     , "  o  m0/evt/INV/inv6/goal (310,1)"
     , "  o  m0/evt/INV/inv6/hypotheses (310,1)"
     , "  o  m0/evt/INV/inv6/relation (310,1)"
     , "  o  m0/evt/INV/inv6/step (312,1)"
     , " xxx m0/evt/INV/inv6/step (314,1)"
     , "  o  m0/evt/INV/inv6/step (316,1)"
     , "  o  m0/evt/INV/inv6/step (318,1)"
     , " xxx m0/evt/INV/inv6/step (320,1)"
     , "  o  m0/evt/INV/inv7"
     , "  o  m0/evt/SCH"
     , "  o  m0/evt/SCH/m0/0/REF/weaken"
     , "  o  m0/evt/TR/tr0/EN"
     , "  o  m0/evt/TR/tr0/NEG"
     , "  o  m0/prog0/REF/monotonicity/lhs"
     , "  o  m0/prog0/REF/monotonicity/rhs"
     , "  o  m0/prog1/REF/induction/lhs"
     , "  o  m0/prog1/REF/induction/rhs"
     , "  o  m0/prog2/REF/trading/lhs"
     , "  o  m0/prog2/REF/trading/rhs"
     , "  o  m0/prog3/REF/PSP/lhs"
     , "  o  m0/prog3/REF/PSP/rhs"
     , "  o  m0/prog4/REF/discharge/saf/lhs"
     , "  o  m0/prog4/REF/discharge/saf/rhs"
     , "  o  m0/prog4/REF/discharge/tr"
     , "passed 84 / 87"
     ]
     
path8 = "tests/cubes-t7.tex"

result9 = unlines
     [ "  o  m0/INIT/FIS/a"
     , "  o  m0/INIT/FIS/b"
     , "  o  m0/INIT/FIS/c"
     , "  o  m0/INIT/FIS/f"
     , "  o  m0/INIT/FIS/n"
     , "  o  m0/INIT/INV/inv0"
     , "  o  m0/INIT/INV/inv1"
     , "  o  m0/INIT/INV/inv2"
     , "  o  m0/INIT/INV/inv3/goal (224,1)"
     , "  o  m0/INIT/INV/inv3/hypotheses (224,1)"
     , "  o  m0/INIT/INV/inv3/relation (224,1)"
     , "  o  m0/INIT/INV/inv3/step (226,1)"
     , "  o  m0/INIT/INV/inv3/step (228,1)"
     , "  o  m0/INIT/INV/inv3/step (232,1)"
     , "  o  m0/INIT/INV/inv4"
     , "  o  m0/INIT/INV/inv5"
     , "  o  m0/INIT/INV/inv6"
     , "  o  m0/INIT/INV/inv7"
     , "  o  m0/SKIP/CO/saf0"
     , "  o  m0/SKIP/CO/saf1"
     , "  o  m0/evt/CO/saf0"
     , "  o  m0/evt/CO/saf1"
     , "  o  m0/evt/FIS/a@prime"
     , "  o  m0/evt/FIS/b@prime"
     , "  o  m0/evt/FIS/c@prime"
     , "  o  m0/evt/FIS/f@prime"
     , "  o  m0/evt/FIS/n@prime"
     , "  o  m0/evt/INV/inv0/goal (66,1)"
     , "  o  m0/evt/INV/inv0/hypotheses (66,1)"
     , "  o  m0/evt/INV/inv0/relation (66,1)"
     , "  o  m0/evt/INV/inv0/step (68,1)"
     , "  o  m0/evt/INV/inv0/step (70,1)"
     , "  o  m0/evt/INV/inv0/step (72,1)"
     , "  o  m0/evt/INV/inv0/step (74,1)"
     , "  o  m0/evt/INV/inv0/step (76,1)"
     , "  o  m0/evt/INV/inv1/goal (144,1)"
     , "  o  m0/evt/INV/inv1/hypotheses (144,1)"
     , "  o  m0/evt/INV/inv1/relation (144,1)"
     , "  o  m0/evt/INV/inv1/step (146,1)"
     , "  o  m0/evt/INV/inv1/step (148,1)"
     , "  o  m0/evt/INV/inv1/step (150,1)"
     , "  o  m0/evt/INV/inv1/step (152,1)"
     , "  o  m0/evt/INV/inv1/step (154,1)"
     , "  o  m0/evt/INV/inv1/step (156,1)"
     , "  o  m0/evt/INV/inv1/step (158,1)"
     , "  o  m0/evt/INV/inv2/easy (193,1)"
     , "  o  m0/evt/INV/inv3/goal (243,1)"
     , "  o  m0/evt/INV/inv3/hypotheses (243,1)"
     , "  o  m0/evt/INV/inv3/relation (243,1)"
     , "  o  m0/evt/INV/inv3/step (245,1)"
     , "  o  m0/evt/INV/inv3/step (247,1)"
     , "  o  m0/evt/INV/inv3/step (249,1)"
     , "  o  m0/evt/INV/inv3/step (255,1)"
     , "  o  m0/evt/INV/inv3/step (257,1)"
     , "  o  m0/evt/INV/inv4"
--     , "  o  m0/evt/INV/inv5/assertion/asm0/easy (300,1)"
     , "  o  m0/evt/INV/inv5/goal (281,1)"
     , "  o  m0/evt/INV/inv5/hypotheses (281,1)"
     , "  o  m0/evt/INV/inv5/relation (281,1)"
     , "  o  m0/evt/INV/inv5/step (283,1)"
     , "  o  m0/evt/INV/inv5/step (285,1)"
     , "  o  m0/evt/INV/inv5/step (287,1)"
     , " xxx m0/evt/INV/inv5/step (289,1)"
     , "  o  m0/evt/INV/inv5/step (292,1)"
     , "  o  m0/evt/INV/inv6/goal (310,1)"
     , "  o  m0/evt/INV/inv6/hypotheses (310,1)"
     , "  o  m0/evt/INV/inv6/relation (310,1)"
     , "  o  m0/evt/INV/inv6/step (312,1)"
     , " xxx m0/evt/INV/inv6/step (314,1)"
     , "  o  m0/evt/INV/inv6/step (316,1)"
     , " xxx m0/evt/INV/inv6/step (318,1)"
     , " xxx m0/evt/INV/inv6/step (320,1)"
     , "  o  m0/evt/INV/inv7"
     , "  o  m0/evt/SCH"
     , "  o  m0/evt/SCH/m0/0/REF/weaken"
     , "  o  m0/evt/TR/tr0/EN"
     , "  o  m0/evt/TR/tr0/NEG"
     , "  o  m0/prog0/REF/monotonicity/lhs"
     , "  o  m0/prog0/REF/monotonicity/rhs"
     , "  o  m0/prog1/REF/induction/lhs"
     , "  o  m0/prog1/REF/induction/rhs"
     , "  o  m0/prog2/REF/trading/lhs"
     , "  o  m0/prog2/REF/trading/rhs"
     , "  o  m0/prog3/REF/PSP/lhs"
     , "  o  m0/prog3/REF/PSP/rhs"
     , "  o  m0/prog4/REF/discharge/saf/lhs"
     , "  o  m0/prog4/REF/discharge/saf/rhs"
     , "  o  m0/prog4/REF/discharge/tr"
     , "  o  m0/prog5/REF/disjunction/lhs"
     , "  o  m0/prog5/REF/disjunction/rhs"
     , " xxx m0/prog6/REF/add"
     , " xxx m0/prog7/REF/add"
     , " xxx m0/prog8/REF/add"
     , "passed 85 / 92"
     ]
     
path9 = "tests/cubes-t8.tex"
     
path10 = "tests/cubes-t9.tex"

result10 = "Left [Error \"A cycle exists in the proof of liveness: prog0, prog1, prog2, prog3\" (1,1)]"

verify path = do
    r <- parse_machine path
    case r of
        Right [m] -> do
            (s,_,_) <- str_verify_machine m
            return s
        x -> return $ show x
