{-# LANGUAGE BangPatterns #-}
module Document.Test where

import Control.Exception (evaluate)

import Document.Document

-- import qualified Document.Tests.CompCalc as CC
import qualified Document.Tests.Cubes as Cubes 
import qualified Document.Tests.Definitions as Defs
-- import qualified Document.Tests.IndirectEq as Ind
import qualified Document.Tests.Lambdas as Lambdas
import qualified Document.Tests.LockFreeDeque as LFD
import qualified Document.Tests.Phase as Phase
import qualified Document.Tests.Puzzle as Puz
import qualified Document.Tests.SmallMachine as SMch
import qualified Document.Tests.TrainStation as Train
import qualified Document.Tests.TrainStationRefinement as Ref
import qualified Document.Tests.TrainStationSets as Set
import qualified Document.Tests.UnlessExcept as UE
-- import qualified Document.Tests.Suite as Suite
import qualified Document.Scope (Scope)
import qualified Document.ExprScope as ESc 
import qualified Document.MachineSpec as MSpec 
import qualified Document.Tests.GarbageCollector as Gar
import qualified Document.Tests.Parser as Parser
import qualified Document.Tests.TerminationDetection as Term
import qualified Document.Phase.Test as PhTest
import Document.Tests.Suite (find_errors)

import Document.Phase.Expressions as PExp 

import Latex.Parser
import Latex.OldMonad


import Test.UnitTest

import UnitB.UnitB

    -- Libraries
import Test.QuickCheck.AxiomaticClass

import Utilities.Syntactic

test_case :: TestCase
test_case = test

test :: TestCase
test = test_cases 
        "Unit-B Document" 
        [ stringCase "basic syntax and scopes" case1 result1
        , LFD.test_case 
        -- , CC.test_case
        -- , Ind.test_case
        , SMch.test_case
        , stringCase "Contextual predicate visibility rules" case2 result2 
        , Puz.test_case
        , UE.test_case
        , PhTest.test_case
        , Cubes.test_case
        , Defs.test_case
        , Train.test_case
        , Lambdas.test_case
        , Phase.test_case
        , Ref.test_case
        , Set.test_case
        , Gar.test_case
        , Term.test_case
        , Parser.test_case
        , QuickCheckProps "QuickCheck spec of machine parser" 
            MSpec.run_spec
        , all_properties
        , check_axioms
        , QuickCheckProps "expression phase, properties" 
            PExp.check_props
        , QuickCheckProps "expression scope, properties" 
            ESc.run_tests
        ]

result1 :: String
result1 = unlines 
    [ "  o  m/enter/FIS/in@prime/goal"
    , "  o  m/enter/FIS/in@prime/hypotheses"
    , "  o  m/enter/FIS/in@prime/relation"
    , "  o  m/enter/FIS/in@prime/step 1"
    , "passed 4 / 4"
    ]

path1 :: FilePath
path1 = [path|Tests/new_syntax.tex|]

case1 :: IO String
case1 = do
    r <- parse_machine path1
    case r of
        Right [m] -> do
            (s,_,_)   <- str_verify_machine m
            return s
        Left x -> return $ show_err x
        x -> return $ show x

result2 :: String
result2 = unlines
    [ "error 23:12:"
    , "    predicate is undefined: 'a1'"
    ]

path2 :: FilePath
path2 = [path|Tests/new_syntax-err0.tex|]

case2 :: IO String
case2 = find_errors path2

check_axioms :: TestCase
check_axioms = QuickCheckProps "conformance of instances to type class axioms"
    $(quickCheckClassesWith [''Document.Scope.Scope])

all_properties :: TestCase
all_properties = aCase "the parser is exception free" 
    (evaluate (all_machines tree) >> return ()) ()

tree0' :: T LatexDoc
tree0' = env "machine"
                    [   bracket Square []
                    ,   bracket Curly
                        [   text 
                            [   textBlock "\FS1"
                            ,   blank "\n"
                            ,   textBlock "7\130\220.1\169"
                            ,   blank "\n"
                            ]
                        ,   text 
                            [   textBlock "N\183T\241N"
                            ,   blank "\n"
                            ]
                        ,   bracket Curly []
                        ,   env "=F\129\216\RS\DC3\USG!0\150`\b\DC2I=}'\DC10\\\196-e9\STX\168\166Nt" 
                            [   env "\239\n\132\&0\DC4X\nNr>#a\EOT;\183\188\162\231!l\DC1\STXf\FS" 
                                []
                            ,   text 
                                [   textBlock "9\""
                                ,   open Square
                                ,   textBlock "\178\179\&6\190s\155\ETB`"
                                ,   blank "\n"
                                ]
                            ] 
                        ,   text 
                            [   textBlock "\252\NUL0Sz,\215\255S\235\248\RSAu\251\217"
                            ,   blank "\n"
                            ]
                        ]
                    ,   text 
                        [   textBlock "\198\&6fH\231e"
                        ,   command "\\\203"
                        ,   textBlock "#"
                        ,   open Square 
                        ,   textBlock "\167\SOH\242\&7\137iS" 
                        ,   blank "\n"
                        ]
                    ] 
                

tree0 :: LatexDoc
tree0 = makeTexDoc [tree0']

tree :: LatexDoc
tree = makeTexDoc
    [   env "fschedule"  
        [   text 
            [   textBlock "ZK\DC3^\EOT<+\202\&0\144Ny\141;\129\242" 
            ,   blank "\n" 
            ]
        ,   text 
            [   blank "\v" 
            ,   textBlock "@\252l\EOT\183\128\SOH\199"
            ,   blank "\f"
            ,   textBlock "\DC20\ETB\btT\199p9\248Q&\144\207\221u" 
            ,   blank "\n" 
            ]
        ,   text 
            [   textBlock "\SOH\169\138H\168\&5Z;\EMs\243ddQV\193.\201\184zv\191T\DELm;" 
            ,   blank "\n" 
            ]
        ,   text 
            [   textBlock "\198\&7\230m'\SIq7" 
            ,   close Square 
            ,   textBlock "\177" 
            ,   close Curly 
            ,   textBlock "1\173\180Bu\aHBJ\SI\ETX" 
            ,   blank "\n" 
            ]
        ,   bracket Square  
        [   text 
            [   textBlock "\FSI" 
            ,   blank " " 
            ,   textBlock "\175HD\US!0\174\242\DC2Nhx\199Z\143\238+\253?\181k\204?X" 
            ,   blank "\n" 
            ]
        ,   text 
            [   blank "\t" 
            ,   textBlock "pL/5\212\SOH\164\152),\SUBD\213\US~\199" 
            ,   close Curly 
            ,   textBlock "s\209\184\228\239m\DC4" 
            ,   blank "\n" 
            ]
        ,   env "fschedule"  
            [   text 
                [   textBlock "x" 
                ,   blank "\n" ]
                ,   text 
                    [   textBlock "/\SYNu\203%/6\221Q\249\193" 
                    ,   blank " " 
                    ,   textBlock "gt\DC2\141" 
                    ,   blank "\n" 
                    ]
                ,   text 
                    [   textBlock "\214\162h\DC4!B5p\227\NUL9" 
                    ,   blank "\n" 
                    ]
                ,   text 
                    [   textBlock "c8\136\230\&3H%\SOHi\154wyu\143pc" 
                    ,   close Square 
                    ,   textBlock "9\147" 
                    ,   blank "\r" 
                    ,   textBlock "\224iZO\169\223" 
                    ,   blank "\n" 
                    ]
                ,   tree0'
                ] 
            ,   text 
                [   textBlock "\186z;\139\254\SIk1wr\a~\131" 
                ,   close Square 
                ,   textBlock "l_\192!\170" 
                ,   blank "\n" 
                ]
            ] 
        ] 
    ]

li :: Int -> Int -> LineInfo
li i j = LI "" i j
