module Code.Test where

import Code.Synthesis

import Document.Machine

import Logic.Label
import Logic.Const

import UnitB.AST

    -- Libraries
import Control.Monad.Trans.Either

import Data.List
import Data.Map

import Tests.UnitTest

test_case = ( "code generation in the cube example", test, True )

test = test_cases
            [ (StringCase "test0: code for the {state}" case0 result0)
            , (StringCase "test1: code for the {event}" case1 result1)
            , (StringCase "test2: code for the {initialization}" case2 result2) 
            , (StringCase "test3: code for the {procedure + loop}" case3 result3) ]


result0 = intercalate "\n"
        [ "data State = State"
        , "    { v_a :: Int" 
        , "    , v_b :: Int" 
        , "    , v_c :: Int"
        , "    , v_f :: M.Map (Int) (Int)" 
        , "    , v_n :: Int"
        , "    , c_N :: Int }" ]

path0 = "tests/cubes-t8.tex"

case0 = do x <- runEitherT $ do
                m <- EitherT $ parse path0
                EitherT $ return $ struct m
           return $ either id id x    
        

result1 = unlines
        [ "modify $ \\s'@(State { .. }) ->"
        , "  if (v_n < c_N) then"
        , "    s' { v_n = (v_n + 1)"
        , "       , v_a = (v_a + v_b)"
        , "       , v_b = (v_b + v_c)"
        , "       , v_c = (v_c + 6)" 
        , "       , v_f = (M.insert v_n v_a v_f) }" 
        , "  else s'" ]
     
case1 = do x <- runEitherT $ do
                m <- EitherT $ parse path0
                EitherT $ return $ event_code m $ events m ! label "evt"
           return $ either id id x    

result2 = unlines
        [ "s' = State"
        , "       { v_b = 1"
        , "       , v_c = 6" 
        , "       , v_n = 0"
        , "       , v_a = 0"
        , "       , v_f = M.empty }" ]
     
case2 = do x <- runEitherT $ do
                m <- EitherT $ parse path0
                EitherT $ return $ init_code m
           return $ either id id x    

result3 = unlines
        [ "find_cubes c_N = flip execState s' $ fix \\proc' ->"
        , "                      if (v_n == c_N) then return ()"
        , "                      else do"
        , "                         modify $ \\s'@(State { .. }) ->"
        , "                           if (v_n < c_N) then"
        , "                             s' { v_n = (v_n + 1)"
        , "                                , v_a = (v_a + v_b)"
        , "                                , v_b = (v_b + v_c)"
        , "                                , v_c = (v_c + 6)" 
        , "                                , v_f = (M.insert v_n v_a v_f) }" 
        , "                           else s'" 
        , "                         proc'" 
        , "    where"
        , "        s' = State"
        , "               { v_b = 1"
        , "               , v_c = 6" 
        , "               , v_n = 0"
        , "               , v_a = 0"
        , "               , v_f = M.empty }" 
        , "" ]

case3 = do x <- runEitherT $ do
                m <- EitherT $ parse path0
                EitherT $ return $ machine_code "find_cubes" m $ n `zeq` bigN
           return $ either id id x    
    where
        (n)      = fromJust $ fst $ var "n" int
        (bigN)   = fromJust $ fst $ var "N" int
     
parse path = do
    r <- parse_machine path
    case r of
        Right [m] -> do
            return $ Right m
        _ -> return $ Left "wrong number of machines"

