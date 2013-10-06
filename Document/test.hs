{-# LANGUAGE BangPatterns #-}
module Document.Test ( test_case ) where

import Control.Monad

import Data.List as L
import Data.Map hiding ( map )
import qualified Data.Map as M
import Document.Document

import qualified Document.Tests.Cubes as Cubes
import qualified Document.Tests.SmallMachine as SMch
import qualified Document.Tests.TrainStation as Train
import qualified Document.Tests.Lambdas as Lambdas
import qualified Document.Tests.Phase as Phase
import qualified Document.Tests.TrainStationRefinement as Ref

import Latex.Parser
import Latex.Scanner

import System.IO.Unsafe

import Test.QuickCheck

import Tests.UnitTest

import UnitB.AST
import UnitB.PO
import UnitB.Calculation

import Z3.Z3

test_case = ("Unit-B Document", test, True)

test :: IO Bool
test = test_cases 
        [ StringCase "basic syntax and scopes" case1 result1
        , SMch.test_case
        , Cubes.test_case
        , Train.test_case
        , Lambdas.test_case
        , Phase.test_case
        , Ref.test_case
        , all_properties
        ]

result1 = (unlines [
        "  o  m/INIT/FIS",
	    "  o  m/enter/FIS/in@prime",
        "  o  m/enter/SCH/goal (21,1)",
        "  o  m/enter/SCH/hypotheses (21,1)",
        "  o  m/enter/SCH/relation (21,1)",
        "  o  m/enter/SCH/step (23,1)",
        "passed 6 / 6"
    ])

path1 = "Tests/new_syntax.tex"
case1 = do
    r <- parse_machine path1
    case r of
        Right [m] -> do
            (s,_,_)   <- str_verify_machine m
            return s
        x -> return $ show x

prop_parser_exc_free xs = 
    classify (depth xs < 5) "shallow" $
    classify (5 <= depth xs && depth xs < 20) "medium" $
    classify (20 <= depth xs && depth xs < 100) "deep" $
    classify (100 <= depth xs) "very deep"
    (case all_machines xs of
        Right _ -> True
        Left  _ -> True)

properties = do
        r <- quickCheckResult prop_parser_exc_free
        case r of
            Success _ _ _ -> return True
            x -> putStrLn ("failed: " ++ show x) >> return False

depth xs = maximum $ 0:map f xs
    where
        f (Env _ _ xs _)    = 1 + depth xs
        f (Bracket _ _ xs _)  = 1 + depth xs
        f (Text _)          = 0

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
                    return $ Env name (0,0) xs (0,0)
            else if n == 2
                then do
                    b  <- arbitrary :: Gen Bool
                    m    <- choose (0,6) :: Gen Int
                    xs   <- forM [1..m] (\_ -> arbitrary :: Gen LatexDoc)
                    return $ Bracket b (0,0) xs (0,0)
            else if 2 < n
                then do
                    xs <- arbitrary :: Gen String
                    let ys = if L.null xs 
                        then "x"
                        else xs
                    n <- choose (0,length cmd+1)
                    let xs = if n < length cmd
                        then ys ++ cmd !! n
                        else ys
                    case read_lines tex_tokens ys of
                        Right x -> return $ Text $ map fst x
                        Left _  -> return $ Text $ [TextBlock "x" (0,0)]
            else error ""
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
            cmd =
                [   "\\newset"
                ,   "\\hint"
                ,   "\\ref"
                ,   "\\eqref"
                ]

all_properties = Case "the parser is exception free" 
    (return (all_machines tree) >> return ()) ()

tree0 =         [   Env "machine" (0,0) 
                    [   Bracket False (0,0) [] (0,0)
                    ,   Bracket True (0,0) 
                        [   Text 
                            [   TextBlock "\FS1" (0,0)
                            ,   Blank "\n" (1,2)
                            ,   TextBlock "7\130\220.1\169" (1,3)
                            ,   Blank "\n" (2,6)
                            ]
                        ,   Text 
                            [   TextBlock "N\183T\241N" (0,0)
                            ,   Blank "\n" (1,5)
                            ]
                        ,   Bracket True (0,0) [] (0,0)
                        ,   Env "=F\129\216\RS\DC3\USG!0\150`\b\DC2I=}'\DC10\\\196-e9\STX\168\166Nt" (0,0) 
                            [   Env "\239\n\132\&0\DC4X\nNr>#a\EOT;\183\188\162\231!l\DC1\STXf\FS" (0,0) 
                                [] (0,0)
                            ,   Text 
                                [   TextBlock "9\"" (0,0)
                                ,   Open False (1,2)
                                ,   TextBlock "\178\179\&6\190s\155\ETB`" (1,3)
                                ,   Blank "\n" (1,11)
                                ]
                            ] (0,0)
                        ,   Text 
                            [   TextBlock "\252\NUL0Sz,\215\255S\235\248\RSAu\251\217" (0,0)
                            ,   Blank "\n" (1,16)
                            ]
                        ] (0,0)
                    ,   Text 
                        [   TextBlock "\198\&6fH\231e" (0,0)
                        ,   Command "\\\203" (1,6)
                        ,   TextBlock "#" (1,8)
                        ,   Open False (1,9)
                        ,   TextBlock "\167\SOH\242\&7\137iS" (1,10)
                        ,   Blank "\n" (1,17)
                        ]
                    ] (0,0)
                ]

tree = 
    [   Env "fschedule" (0,0) 
        [   Text 
            [   TextBlock "ZK\DC3^\EOT<+\202\&0\144Ny\141;\129\242" (0,0)
            ,   Blank "\n" (1,16)
            ]
        ,   Text 
            [   Blank "\v" (0,0)
            ,   TextBlock "@\252l\EOT\183\128\SOH\199" (1,1)
            ,   Blank "\f" (1,9)
            ,   TextBlock "\DC20\ETB\btT\199p9\248Q&\144\207\221u" (1,10)
            ,   Blank "\n" (1,26)
            ]
        ,   Text 
            [   TextBlock "\SOH\169\138H\168\&5Z;\EMs\243ddQV\193.\201\184zv\191T\DELm;" (0,0)
            ,   Blank "\n" (1,26)
            ]
        ,   Text 
            [   TextBlock "\198\&7\230m'\SIq7" (0,0)
            ,   Close False (1,8)
            ,   TextBlock "\177" (1,9)
            ,   Close True (1,10)
            ,   TextBlock "1\173\180Bu\aHBJ\SI\ETX" (1,11)
            ,   Blank "\n" (1,22)
            ]
        ,   Bracket False (0,0) 
        [   Text 
            [   TextBlock "\FSI" (0,0)
            ,   Blank " " (1,2)
            ,   TextBlock "\175HD\US!0\174\242\DC2Nhx\199Z\143\238+\253?\181k\204?X" (1,3)
            ,   Blank "\n" (1,27)
            ]
        ,   Text 
            [   Blank "\t" (0,0)
            ,   TextBlock "pL/5\212\SOH\164\152),\SUBD\213\US~\199" (1,1)
            ,   Close True (1,17)
            ,   TextBlock "s\209\184\228\239m\DC4" (1,18)
            ,   Blank "\n" (1,25)
            ]
        ,   Env "fschedule" (0,0) 
            [   Text 
                [   TextBlock "x" (0,0)
                ,   Blank "\n" (1,1)]
                ,   Text 
                    [   TextBlock "/\SYNu\203%/6\221Q\249\193" (0,0)
                    ,   Blank " " (1,11)
                    ,   TextBlock "gt\DC2\141" (1,12)
                    ,   Blank "\n" (1,16)
                    ]
                ,   Text 
                    [   TextBlock "\214\162h\DC4!B5p\227\NUL9" (0,0)
                    ,   Blank "\n" (1,11)
                    ]
                ,   Text 
                    [   TextBlock "c8\136\230\&3H%\SOHi\154wyu\143pc" (0,0)
                    ,   Close False (1,16)
                    ,   TextBlock "9\147" (1,17)
                    ,   Blank "\r" (1,19)
                    ,   TextBlock "\224iZO\169\223" (1,20)
                    ,   Blank "\n" (1,26)
                    ]
                ,   head tree0
                ] (0,0)
            ,   Text 
                [   TextBlock "\186z;\139\254\SIk1wr\a~\131" (0,0)
                ,   Close False (1,13)
                ,   TextBlock "l_\192!\170" (1,14)
                ,   Blank "\n" (1,19)
                ]
            ] (0,0)
        ] (0,0)
    ]