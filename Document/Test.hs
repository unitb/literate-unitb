{-# LANGUAGE BangPatterns #-}
module Document.Test where

import Control.Monad

import Data.List as L
import Document.Document

import qualified Document.Tests.Cubes as Cubes
import qualified Document.Tests.Lambdas as Lambdas
import qualified Document.Tests.LockFreeDeque as LFD
import qualified Document.Tests.Phase as Phase
import qualified Document.Tests.Puzzle as Puz
import qualified Document.Tests.SmallMachine as SMch
import qualified Document.Tests.TrainStation as Train
import qualified Document.Tests.TrainStationRefinement as Ref
import qualified Document.Tests.TrainStationSets as Set
import qualified Document.Tests.UnlessExcept as UE
import qualified Document.MachineSpec as MSpec 

import Latex.Parser
import Latex.Scanner

import Test.QuickCheck

import Tests.UnitTest

import UnitB.PO

import Utilities.Syntactic

test_case :: TestCase
test_case = test

test :: TestCase
test = test_cases 
        "Unit-B Document" 
        [ StringCase "basic syntax and scopes" case1 result1
        , StringCase "Contextual predicate visibility rules" case2 result2
        , Puz.test_case
        , UE.test_case
        , LFD.test_case
        , SMch.test_case
        , Cubes.test_case
        , Train.test_case
        , Lambdas.test_case
        , Phase.test_case
        , Ref.test_case
        , Set.test_case
        , Case "QuickCheck spec of machine parser" 
            MSpec.run_spec True
        , all_properties
        ]

result1 :: String
result1 = unlines 
    [ "  o  m/INIT/WD"
    , "  o  m/INIT/WWD"
    , "  o  m/INV/WD"
    , "  o  m/enter/FIS/in@prime"
    , "  o  m/enter/WD/ACT/a1"
    , "  o  m/enter/WD/C_SCH"
    , "  o  m/enter/WD/F_SCH"
    , "  o  m/enter/WD/GRD/goal (21,1)"
    , "  o  m/enter/WD/GRD/hypotheses (21,1)"
    , "  o  m/enter/WD/GRD/relation (21,1)"
    , "  o  m/enter/WD/GRD/step (23,1)"
    , "  o  m/enter/WWD"
    , "passed 12 / 12"
    ]

path1 :: String
path1 = "Tests/new_syntax.tex"

case1 :: IO String
case1 = do
    r <- parse_machine path1
    case r of
        Right [m] -> do
            (s,_,_)   <- str_verify_machine m
            return s
        x -> return $ show x

result2 :: String
result2 = concat [
        "[Error \"predicate is undefined: 'a1'\" (23,11)]"
    ]

path2 :: String
path2 = "Tests/new_syntax-err0.tex"

case2 :: IO String
case2 = do
    r <- parse_machine path2
    case r of
        Right _ -> do
            return "ok"
        Left x -> return $ show x

--prop_parser_exc_free xs = 
--    classify (depth xs < 5) "shallow" $
--    classify (5 <= depth xs && depth xs < 20) "medium" $
--    classify (20 <= depth xs && depth xs < 100) "deep" $
--    classify (100 <= depth xs) "very deep"
--    (case all_machines xs of
--        Right _ -> True
--        Left  _ -> True)

--properties = do
--        r <- quickCheckResult prop_parser_exc_free
--        case r of
--            Success _ _ _ -> return True
--            x -> putStrLn ("failed: " ++ show x) >> return False
--
--depth xs = maximum $ 0:map f xs
--    where
--        f (Env _ _ xs _)    = 1 + depth xs
--        f (Bracket _ _ xs _)  = 1 + depth xs
--        f (Text _)          = 0

instance Arbitrary LatexDoc where
    arbitrary = do
            n <- choose (1,7) :: Gen Int
            if n == 1 
                then do
                    n <- choose (0,length kw+2)
                    name <- if length kw <= n
                        then arbitrary :: Gen String
                        else return (kw !! n)
                    m    <- choose (0,6) :: Gen Int
                    xs   <- forM [1..m] (\_ -> arbitrary :: Gen LatexDoc)
                    return $ Env name (li 0 0) xs (li 0 0)
            else if n == 2
                then do
                    b  <- elements [Curly,Square]
                    m    <- choose (0,6) :: Gen Int
                    xs   <- forM [1..m] (\_ -> arbitrary :: Gen LatexDoc)
                    return $ Bracket b (li 0 0) xs (li 0 0)
            else if 2 < n
                then do
                    xs <- arbitrary :: Gen String
                    let ys = if L.null xs 
                        then "x"
                        else xs
--                    n <- choose (0,length cmd+1)
                    case read_lines tex_tokens "" ys of
                        Right x -> return $ Text $ map fst x
                        Left _  -> return $ Text $ [TextBlock "x" (li 0 0)]
            else error "Document.Test"
        where
            kw =
                [   "machine"
                ,   "variable"
                ,   "indices"
                ,   "evassignment"
                ,   "cschedule"
                ,   "fschedule"
                ,   "invariant"
                ,   "transient"
                ,   "dummy"
                ,   "use:set"
                ,   "constant"
                ,   "assumption"
                ,   "initialization"
                ,   "constraint"
                ,   "proof"
                ,   "calculation"
                ]
--            cmd =
--                [   "\\newset"
--                ,   "\\hint"
--                ,   "\\ref"
--                ,   "\\eqref"
--                ]

all_properties :: TestCase
all_properties = Case "the parser is exception free" 
    (return (all_machines tree) >> return ()) ()

tree0 :: [LatexDoc]
tree0 =         [   Env "machine" (li 0 0) 
                    [   Bracket Square (li 0 0) [] (li 0 0)
                    ,   Bracket Curly (li 0 0) 
                        [   Text 
                            [   TextBlock "\FS1" (li 0 0)
                            ,   Blank "\n" (li 1 2)
                            ,   TextBlock "7\130\220.1\169" (li 1 3)
                            ,   Blank "\n" (li 2 6)
                            ]
                        ,   Text 
                            [   TextBlock "N\183T\241N" (li 0 0)
                            ,   Blank "\n" (li 1 5)
                            ]
                        ,   Bracket Curly (li 0 0) [] (li 0 0)
                        ,   Env "=F\129\216\RS\DC3\USG!0\150`\b\DC2I=}'\DC10\\\196-e9\STX\168\166Nt" (li 0 0) 
                            [   Env "\239\n\132\&0\DC4X\nNr>#a\EOT;\183\188\162\231!l\DC1\STXf\FS" (li 0 0) 
                                [] (li 0 0)
                            ,   Text 
                                [   TextBlock "9\"" (li 0 0)
                                ,   Open Square (li 1 2)
                                ,   TextBlock "\178\179\&6\190s\155\ETB`" (li 1 3)
                                ,   Blank "\n" (li 1 11)
                                ]
                            ] (li 0 0)
                        ,   Text 
                            [   TextBlock "\252\NUL0Sz,\215\255S\235\248\RSAu\251\217" (li 0 0)
                            ,   Blank "\n" (li 1 16)
                            ]
                        ] (li 0 0)
                    ,   Text 
                        [   TextBlock "\198\&6fH\231e" (li 0 0)
                        ,   Command "\\\203" (li 1 6)
                        ,   TextBlock "#" (li 1 8)
                        ,   Open Square (li 1 9)
                        ,   TextBlock "\167\SOH\242\&7\137iS" (li 1 10)
                        ,   Blank "\n" (li 1 17)
                        ]
                    ] (li 0 0)
                ]

tree :: [LatexDoc]
tree = 
    [   Env "fschedule" (li 0 0) 
        [   Text 
            [   TextBlock "ZK\DC3^\EOT<+\202\&0\144Ny\141;\129\242" (li 0 0)
            ,   Blank "\n" (li 1 16)
            ]
        ,   Text 
            [   Blank "\v" (li 0 0)
            ,   TextBlock "@\252l\EOT\183\128\SOH\199" (li 1 1)
            ,   Blank "\f" (li 1 9)
            ,   TextBlock "\DC20\ETB\btT\199p9\248Q&\144\207\221u" (li 1 10)
            ,   Blank "\n" (li 1 26)
            ]
        ,   Text 
            [   TextBlock "\SOH\169\138H\168\&5Z;\EMs\243ddQV\193.\201\184zv\191T\DELm;" (li 0 0)
            ,   Blank "\n" (li 1 26)
            ]
        ,   Text 
            [   TextBlock "\198\&7\230m'\SIq7" (li 0 0)
            ,   Close Square (li 1 8)
            ,   TextBlock "\177" (li 1 9)
            ,   Close Curly (li 1 10)
            ,   TextBlock "1\173\180Bu\aHBJ\SI\ETX" (li 1 11)
            ,   Blank "\n" (li 1 22)
            ]
        ,   Bracket Square (li 0 0) 
        [   Text 
            [   TextBlock "\FSI" (li 0 0)
            ,   Blank " " (li 1 2)
            ,   TextBlock "\175HD\US!0\174\242\DC2Nhx\199Z\143\238+\253?\181k\204?X" (li 1 3)
            ,   Blank "\n" (li 1 27)
            ]
        ,   Text 
            [   Blank "\t" (li 0 0)
            ,   TextBlock "pL/5\212\SOH\164\152),\SUBD\213\US~\199" (li 1 1)
            ,   Close Curly (li 1 17)
            ,   TextBlock "s\209\184\228\239m\DC4" (li 1 18)
            ,   Blank "\n" (li 1 25)
            ]
        ,   Env "fschedule" (li 0 0) 
            [   Text 
                [   TextBlock "x" (li 0 0)
                ,   Blank "\n" (li 1 1)]
                ,   Text 
                    [   TextBlock "/\SYNu\203%/6\221Q\249\193" (li 0 0)
                    ,   Blank " " (li 1 11)
                    ,   TextBlock "gt\DC2\141" (li 1 12)
                    ,   Blank "\n" (li 1 16)
                    ]
                ,   Text 
                    [   TextBlock "\214\162h\DC4!B5p\227\NUL9" (li 0 0)
                    ,   Blank "\n" (li 1 11)
                    ]
                ,   Text 
                    [   TextBlock "c8\136\230\&3H%\SOHi\154wyu\143pc" (li 0 0)
                    ,   Close Square (li 1 16)
                    ,   TextBlock "9\147" (li 1 17)
                    ,   Blank "\r" (li 1 19)
                    ,   TextBlock "\224iZO\169\223" (li 1 20)
                    ,   Blank "\n" (li 1 26)
                    ]
                ,   head tree0
                ] (li 0 0)
            ,   Text 
                [   TextBlock "\186z;\139\254\SIk1wr\a~\131" (li 0 0)
                ,   Close Square (li 1 13)
                ,   TextBlock "l_\192!\170" (li 1 14)
                ,   Blank "\n" (li 1 19)
                ]
            ] (li 0 0)
        ] (li 0 0)
    ]

li :: Int -> Int -> LineInfo
li i j = LI "" i j
