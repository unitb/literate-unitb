module Code.Test where

import Code.Synthesis

import Document.Machine

import Logic.Label
import Logic.Const

import UnitB.AST

    -- Libraries
import Control.Monad.Trans
import Control.Monad.Trans.Either

import Data.List
import Data.Map

import Tests.UnitTest

import System.Directory
import System.Process

test_case = ( "code generation in the cube example", test, True )

test = test_cases
            [ (StringCase "test0: code for the {state}" case0 result0)
            , (StringCase "test1: code for the {event}" case1 result1)
            , (StringCase "test2: code for the {initialization}" case2 result2) 
            , (StringCase "test3: code for the {procedure + loop}" case3 result3) 
            , (StringCase "test4: {whole source file}" case4 result4) 
            , (StringCase "test5: run {source file}" case5 result5) ]


result0 = intercalate "\n"
        [ "data State = State"
        , "    { v_a :: Int" 
        , "    , v_b :: Int" 
        , "    , v_c :: Int"
        , "    , v_f :: M.Map (Int) (Int)" 
        , "    , v_n :: Int }" ]
--        , "    , c_N :: Int }" ]

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
        [ "find_cubes c_N = flip execState s' $ fix $ \\proc' -> do"
        , "                      (State { .. }) <- get"
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
     
result4 = unlines
        [ "{-# LANGUAGE RecordWildCards #-}"
        , "import Data.Map as M"
        , "import Data.Set as S"
        , "import Control.Monad.State"
        , ""
        , "data State = State"
        , "    { v_a :: Int" 
        , "    , v_b :: Int" 
        , "    , v_c :: Int"
        , "    , v_f :: M.Map (Int) (Int)" 
        , "    , v_n :: Int }"
--       , "    , c_N :: Int }" 
        , ""
        , "find_cubes c_N = flip execState s' $ fix $ \\proc' -> do"
        , "                      (State { .. }) <- get"
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
        , ""
        , "" ]


case4 = do x <- runEitherT $ do
                m <- EitherT $ parse path0
                EitherT $ return $ source_file "find_cubes" m $ n `zeq` bigN
           return $ either id id x    
    where
        (n)      = fromJust $ fst $ var "n" int
        (bigN)   = fromJust $ fst $ var "N" int

result5 = unlines
            [ "0^3 = 0"
            , "1^3 = 1"
            , "2^3 = 8"
            , "3^3 = 27"
            , "4^3 = 64"
            , "5^3 = 125"
            , "6^3 = 216"
            , "7^3 = 343"
            , "8^3 = 512"
            , "9^3 = 729" ]

case5 = do  xs <- runEitherT $ do
                m <- EitherT $ parse path0
                xs <- EitherT $ return $ source_file "find_cubes" m $ n `zeq` bigN
                lift $ do 
                    writeFile "tests/code.hs" $ unlines
                        [ xs
                        , ""
                        , "main = do"
                        , "        forM_ (M.toList $ v_f $ find_cubes 10) $ \\(i,n) -> do"
                        , "            putStrLn $ show i ++ \"^3 = \" ++ show n" ]
                    (_,rs,_) <- readProcessWithExitCode "runghc" ["tests/code.hs"] ""
                    removeFile "tests/code.hs"
                    return rs
            return $ either id id xs    
    where
        (n)      = fromJust $ fst $ var "n" int
        (bigN)   = fromJust $ fst $ var "N" int

parse path = do
    r <- parse_machine path
    case r of
        Right [m] -> do
            return $ Right m
        _ -> return $ Left "wrong number of machines"

