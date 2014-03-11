module Document.Tests.IndirectEq where

import Document.Document

import UnitB.AST
import UnitB.PO

    -- Libraries
import Data.Map hiding (split, map)
import Data.String.Utils

import Control.Monad.Trans
import Control.Monad.Trans.Either

import Tests.UnitTest

test_case :: TestCase
test_case = Case "train station example, with sets" test True

test :: IO Bool
test = test_cases
            [ Case "verify proof with galois connections" (verify 0 path0) result0
            , Case "verify theory 1: indirect (in)equality" case1 result1
            , Case "verify theory 2: lattices" case2 result2
            ]

path0 :: String
path0 = "tests/indirect-equality.tex"

result0 :: String
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
	
result1 :: String
result1 = unlines
    [ "  o  THM/thm0/completeness (131,1)"
    , "  o  THM/thm0/part 1/easy (133,2)"
    , "  o  THM/thm0/part 2/goal (143,2)"
    , "  o  THM/thm0/part 2/hypotheses (143,2)"
    , "  o  THM/thm0/part 2/new assumption (138,2)"
    , "  o  THM/thm0/part 2/relation (143,2)"
    , "  o  THM/thm0/part 2/step (145,2)"
    , "  o  THM/thm0/part 2/step (147,2)"
    , "  o  THM/thm0/part 2/step (150,2)"
    , "  o  THM/thm1/completeness (162,1)"
    , "  o  THM/thm1/part 1/goal (165,2)"
    , "  o  THM/thm1/part 1/hypotheses (165,2)"
    , "  o  THM/thm1/part 1/relation (165,2)"
    , "  o  THM/thm1/part 1/step (167,2)"
    , "  o  THM/thm1/part 2/goal (173,2)"
    , "  o  THM/thm1/part 2/hypotheses (173,2)"
    , "  o  THM/thm1/part 2/relation (173,2)"
    , "  o  THM/thm1/part 2/step (175,2)"
    , "  o  THM/thm1/part 2/step (177,2)"
    ]

verify_thy :: String -> IO String
verify_thy name = do
        r <- runEitherT $ do
            s <- EitherT $ parse_system path0
            pos <- hoistEither $ theory_po $ theories s ! name
            res <- lift $ verify_all pos
            return $ unlines $ map (\(k,r) -> success r ++ show k) $ toList res        
        case r of
            Right r -> do
                return r
            Left x -> return $ show x
    where
        success True  = "  o  "
        success False = " xxx "

case1 :: IO String
case1 = verify_thy "ctx0"

result2 :: String
result2 = unlines
    [ "  o  THM/thm3/goal (213,1)"
    , "  o  THM/thm3/hypotheses (213,1)"
    , "  o  THM/thm3/relation (213,1)"
    , "  o  THM/thm3/step (216,1)"
    , "  o  THM/thm3/step (219,1)"
    , "  o  THM/thm3/step (221,1)"
    , "  o  THM/thm4/assertion/indirect:eq/easy (236,24)"
    , "  o  THM/thm4/assertion/new:goal/goal (237,41)"
    , "  o  THM/thm4/assertion/new:goal/hypotheses (237,41)"
    , "  o  THM/thm4/assertion/new:goal/relation (237,41)"
    , "  o  THM/thm4/assertion/new:goal/step (240,1)"
    , "  o  THM/thm4/assertion/new:goal/step (242,1)"
    , "  o  THM/thm4/assertion/new:goal/step (244,1)"
    , " xxx THM/thm4/assertion/new:goal/step (246,1)"
    , "  o  THM/thm4/main goal/easy (236,24)"
    , "  o  THM/thm5/goal (262,1)"
    , "  o  THM/thm5/hypotheses (262,1)"
    , "  o  THM/thm5/relation (262,1)"
    , "  o  THM/thm5/step (265,1)"
    , "  o  THM/thm5/step (267,1)"
    , "  o  THM/thm5/step (269,1)"
    , "  o  THM/thm5/step (271,1)" ]

case2 :: IO String
case2 = verify_thy "ctx1"

verify :: Int -> FilePath -> IO String
verify n path = do
    r <- parse_machine path
    case r of
        Right ms -> do
            (s,_,_) <- str_verify_machine $ ms !! n
            return $ unlines $ map (head . split "(") $ lines s
        x -> return $ show x
