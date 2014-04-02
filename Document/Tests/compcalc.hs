module Document.Tests.CompCalc where

    -- Modules
import Document.Document

import UnitB.AST
import UnitB.PO

    -- Libraries
import Data.Map as M hiding (split, map)

import Control.Monad.Trans
import Control.Monad.Trans.Either

import Tests.UnitTest

test_case :: TestCase
test_case = Case "theories with new notation: comp calc" test True

test :: IO Bool
test = test_cases
            [ (Case "proving a theorem with the everywhere operator" case0 result0)
            ]            

path0 :: FilePath
path0 = "tests/comp-calc.tex"

result0 :: String
result0 = unlines [" xxx THM/CC:10i"]

case0 :: IO String
case0 = verify_thy path0 "ctx0"

verify_thy :: FilePath -> String -> IO String
verify_thy path name = do
        r <- runEitherT $ do
            s <- EitherT $ parse_system path
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
