{-# LANGUAGE OverloadedStrings #-}
module Code.Test where

import Code.Synthesis hiding (M)

import Document.Document

import Logic.Expr.Const (var)

import UnitB.Expr
import UnitB.UnitB hiding (safety)

import Z3.Z3

    -- Libraries
import Control.Lens
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Either
import Control.Precondition

import Data.Either.Combinators hiding (fromRight')
import Data.List as L
import Data.Map hiding ((!))

import System.Directory
import System.IO.Unsafe
import System.Process

import Test.UnitTest

test_case :: TestCase
test_case = test

test :: TestCase
test = test_cases
            "code generation in the cube example"
            [ (stringCase "test0: code for the {state}" case0 result0)
            , (stringCase "test1: code for the {event}" case1 result1)
            , (stringCase "test2: code for the {initialization}" case2 result2) 
            , (stringCase "test3: code for the {procedure + loop}" case3 result3) 
            , (stringCase "test4: {whole source file}" case4 result4) 
            , (stringCase "test5: run {source file}" case5 result5) 
            , (stringCase "test6: verify {control flow graph}" case6 result6) 
            , (stringCase "test7: {concurrent} code" case7 result7)
            , (stringCase "test8: {run concurrent} code" case8 result8)
            ]


result0 :: String
result0 = unlines
        [ "data State = State"
        , "    { v_a :: Int" 
        , "    , v_b :: Int" 
        , "    , v_c :: Int"
        , "    , v_f :: M.Map (Int) (Int)" 
        , "    , v_n :: Int }" ]

input :: Either String RawMachineAST
input = unsafePerformIO $ fmap (view' syntax.raw) <$> parse path0

path0 :: FilePath
path0 = [path|Tests/cubes-t8.tex|]

case0 :: IO String
case0 = do x <- runEitherT $ do
                m <- hoistEither input
                EitherT $ return $ run $ struct m
           return $ either id id x    
        

result1 :: String
result1 = unlines
        [ "let s' = s"
        , "        { v_n = (v_n + 1)"
        , "        , v_a = (v_a + v_b)"
        , "        , v_b = (v_b + v_c)"
        , "        , v_c = (v_c + 6)" 
        , "        , v_f = (M.insert v_n v_a v_f)"
        , "        }" 
        ]
     
case1 :: IO String
case1 = do x <- runEitherT $ do
                m <- hoistEither input
                EitherT $ return $ run $ void $ event_body_code m $ (conc_events m ! Right "evt")^.new
           return $ either id id x    

result2 :: String
result2 = unlines
        [ "s' = State"
        , "     { v_b = 1"
        , "     , v_c = 6" 
        , "     , v_n = 0"
        , "     , v_a = 0"
        , "     , v_f = M.empty"
        , "     }" ]
     
case2 :: IO String
case2 = do let x = do
                m <- raw <$> input
                run $ init_code m
           return $ either id id x    

result3 :: String
result3 = unlines
        [ "find_cubes c_N = do"
        , "        execState proc s'"
        , "    where"
        , "        s' = State"
        , "             { v_b = 1"
        , "             , v_c = 6" 
        , "             , v_n = 0"
        , "             , v_a = 0"
        , "             , v_f = M.empty"
        , "             }" 
        , "        proc ="
        , "               fix $ \\proc' -> do"
        , "                 (State { .. }) <- get"
        , "                 if (not (v_n < c_N)) then return ()"
        , "                 else do"
        , "                   s@(State { .. }) <- get"
        , "                   if (v_n < c_N) then do"
        , "                     let s' = s"
        , "                             { v_n = (v_n + 1)"
        , "                             , v_a = (v_a + v_b)"
        , "                             , v_b = (v_b + v_c)"
        , "                             , v_c = (v_c + 6)" 
        , "                             , v_f = (M.insert v_n v_a v_f)"
        , "                             }" 
        , "                     put s'"
        , "                   else"
        , "                     put s" 
        , "                   proc'" 
        ]

case3 :: IO String
case3 = do let x = do
                m <- raw <$> input
                run $ machine_code "find_cubes" m $ n `zeq` bigN
           return $ either id id x    
    where
        (n)      = fromRight' $ fst $ var "n" int
        (bigN)   = fromRight' $ fst $ var "N" int
     
result4 :: String
result4 = unlines
        [ "{-# LANGUAGE RecordWildCards #-}"
        , "import Data.Map as M"
        , "import Data.Set as S"
        , "import Control.Monad"
        , "import Control.Monad.Fix"
        , "import Control.Monad.State.Class"
        , "import Control.Monad.Trans"
        , "import Control.Monad.Trans.RWS   hiding (get,put)"
        , "import Control.Monad.Trans.State hiding (get,put)"
        , ""
        , "data State = State"
        , "    { v_a :: Int" 
        , "    , v_b :: Int" 
        , "    , v_c :: Int"
        , "    , v_f :: M.Map (Int) (Int)" 
        , "    , v_n :: Int }"
--       , "    , c_N :: Int }" 
        , ""
        , "find_cubes c_N = do"
        , "        execState proc s'"
        , "    where"
        , "        s' = State"
        , "             { v_b = 1"
        , "             , v_c = 6" 
        , "             , v_n = 0"
        , "             , v_a = 0"
        , "             , v_f = M.empty"
        , "             }" 
        , "        proc ="
        , "               fix $ \\proc' -> do"
        , "                 (State { .. }) <- get"
        , "                 if (not (v_n < c_N)) then return ()"
        , "                 else do"
        , "                   s@(State { .. }) <- get"
        , "                   if (v_n < c_N) then do"
        , "                     let s' = s"
        , "                             { v_n = (v_n + 1)"
        , "                             , v_a = (v_a + v_b)"
        , "                             , v_b = (v_b + v_c)"
        , "                             , v_c = (v_c + 6)" 
        , "                             , v_f = (M.insert v_n v_a v_f)"
        , "                             }" 
        , "                     put s'"
        , "                   else"
        , "                     put s" 
        , "                   proc'" 
        ]



case4 :: IO String
case4 = do let x = do
                m <- input
                source_file "find_cubes" m $ n `zeq` bigN
           return $ either id id x    
    where
        (n)      = fromRight' $ fst $ var "n" int
        (bigN)   = fromRight' $ fst $ var "N" int

result7 :: String
result7 = unlines
        [ "{-# LANGUAGE RecordWildCards #-}"
        , "import Data.Map as M"
        , "import Data.Set as S"
        , "import Control.Concurrent.STM"
        , "import Control.Monad"
        , "import Control.Monad.Fix"
        , "import Control.Monad.State.Class"
        , "import Control.Monad.Trans"
        , "import Control.Monad.Trans.RWS   hiding (get,put)"
        , "import Control.Monad.Trans.State hiding (get,put)"
        , ""
        , "data Shared = Shared"
        , "    { s_b :: TVar (Int)" 
        , "    , s_f :: TVar (M.Map (Int) (Int))"
        , "    , s_n :: TVar (Int) }"
        , ""
        , "data State = State"
        , "    { v_a :: Int" 
        , "    , v_c :: Int }"
        , ""
        , "find_cubes c_N = do"
        , "        s_b <- newTVarIO 1"
        , "        s_n <- newTVarIO 0"
        , "        s_f <- newTVarIO M.empty"
        , "        fst `liftM` (execRWST proc (Shared { .. }) s' :: IO (Main.State,()))"
        , "    where"
        , "        s' = State"
        , "             { v_c = 6" 
        , "             , v_a = 0"
        , "             }" 
        , "        proc ="
        , "               fix $ \\proc' -> do"
        , "                 (State { .. }) <- get"
        , "                 (Shared { .. }) <- ask"
        , "                 expr <- lift $ atomically $ do"
        , "                   v_n <- readTVar s_n"
        , "                   return (not (v_n < c_N))"
        , "                 if expr then return ()"
        , "                 else do"
        , "                   s@(State { .. }) <- get"
        , "                   (Shared { .. }) <- ask"
        , "                   expr <- lift $ atomically $ do"
        , "                     v_n <- readTVar s_n"
        , "                     if (v_n < c_N) then do"
        , "                       v_b <- readTVar s_b"
        , "                       v_f <- readTVar s_f"
        , "                       v_n <- readTVar s_n"
        , "                       let s' = s"
        , "                               { v_a = (v_a + v_b)"
        , "                               , v_c = (v_c + 6)" 
        , "                               }" 
        , "                       writeTVar s_n (v_n + 1)"
        , "                       writeTVar s_b (v_b + v_c)"
        , "                       writeTVar s_f (M.insert v_n v_a v_f)"
        , "                       return s'"
        , "                     else"
        , "                       return s" 
        , "                   put expr" 
        , "                   proc'" 
        ]

case7 :: IO String
case7 = do let x = do
                m <- input
                let vars = L.map fromString'' ["n","f","b"]
                source_file' vars "find_cubes" m $ n `zeq` bigN
           return $ either id id x    
    where
        (n)      = fromRight' $ fst $ var "n" int
        (bigN)   = fromRight' $ fst $ var "N" int

result8 :: String
result8 = unlines 
    [ "1000" ]

case8 :: IO String
case8 = do  xs <- runEitherT $ do
                m  <- hoistEither input
                let vars = L.map fromString'' ["n","f","b"]
                xs <- hoistEither $ source_file' vars "find_cubes" m $ n `zeq` bigN
                lift $ do 
                    file <- tempFile "Tests/code.hs"
                    writeFile file $ unlines
                        [ xs
                        , ""
                        , "main = do"
                        , "        print . v_a =<< find_cubes 10" ]
                    rs <- readProcess "runghc" [file] ""
                    removeFile file
                    return rs
            return $ either id id xs    
    where
        (n)      = fromRight' $ fst $ var "n" int
        (bigN)   = fromRight' $ fst $ var "N" int

result5 :: String
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

case5 :: IO String
case5 = do  xs <- runEitherT $ do
                m  <- hoistEither input
                xs <- hoistEither $ source_file "find_cubes" m $ n `zeq` bigN
                lift $ do 
                    file <- tempFile "Tests/code.hs"
                    writeFile file $ unlines
                        [ xs
                        , ""
                        , "main = do"
                        , "        forM_ (M.toList $ v_f $ find_cubes 10) $ \\(i,n) -> do"
                        , "            putStrLn $ show i ++ \"^3 = \" ++ show n" ]
                    (_,rs,_) <- readProcessWithExitCode "runghc" [file] ""
                    removeFile file
                    return rs
            return $ either id id xs    
    where
        (n)      = fromRight' $ fst $ var "n" int
        (bigN)   = fromRight' $ fst $ var "N" int

result6 :: String
result6 = unlines 
    [ "(m0/body/disabled/evt,Valid)"
    , "(m0/body/forced,Valid)"
    ]

case6 :: IO String
case6 = liftM (either id id) $ runEitherT $ do
    m  <- hoistEither input
    let cfg = default_cfg m
    pos <- hoistEither 
        $ mapLeft unlines
        $ safety m [] [] cfg
    -- xs <- hoistEither $ source_file "find_cubes" m $ n `zeq` bigN
    xs <- lift $ discharge_all (toAscList pos)
    return $ unlines $ L.map (show . (_1 %~ Pretty)) $ zip (keys pos) xs

parse :: FilePath -> IO (Either String Machine)
parse path = do
    r <- parse_machine path
    case r of
        Right [m] -> do
            return $ Right m
        Right _ -> return $ Left "wrong number of machines"
        Left x  -> return $ Left $ unlines $ L.map show x

-- data POLabel = 
--             POLoop 
--             | POSeq 
--             | POEvent 
--             | PONotEvent 
--             | POCondition 
--             | PoWait 
--             | PONumber Int
--     deriving (Eq)

-- type M = ReaderT [Branch] (Either String)

-- type Branch = ([POLabel],Either [Label] [Expr])

-- make_cfg :: [Branch] -> Either String Program
-- make_cfg bs 
--         | valid     = 
--             case bs' of
--                 [b]:_ -> runReaderT (make_cfg' b) (L.map (first $ drop 1) bs)
--         | otherwise = Left "make_cfg: invalid control flow tree"
--     where
--         bs' = L.map (take 1 . fst) bs
--         valid = and $ zipWith (==) bs' (drop 1 bs')

-- make_cfg' :: POLabel -> M Program
-- make_cfg' POLoop = do
--     return $ Loop _ _ _ _
