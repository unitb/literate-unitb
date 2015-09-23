{-# LANGUAGE BangPatterns #-}
module Document.Test where

import Control.Monad

import Data.List as L
import Document.Document

-- import qualified Document.Tests.CompCalc as CC
import qualified Document.Tests.Cubes as Cubes
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
import qualified Document.MachineSpec as MSpec 
import qualified Document.Tests.GarbageCollector as Gar
import qualified Document.Tests.Parser as Parser
import qualified Document.Tests.TerminationDetection as Term
import qualified Document.Phase.Test as PhTest

import Latex.Parser
import Latex.Scanner

import Test.QuickCheck

import Tests.UnitTest

import UnitB.PO

    -- Libraries
import Control.Applicative

import Utilities.Syntactic

test_case :: TestCase
test_case = test

test :: TestCase
test = test_cases 
        "Unit-B Document" 
        [ StringCase "basic syntax and scopes" case1 result1
        , StringCase "Contextual predicate visibility rules" case2 result2
        , PhTest.test_case
        , Puz.test_case
        , UE.test_case
        , LFD.test_case
        -- , CC.test_case
        -- , Ind.test_case
        , SMch.test_case
        , Cubes.test_case
        , Train.test_case
        , Lambdas.test_case
        , Phase.test_case
        , Ref.test_case
        , Set.test_case
        , Gar.test_case
        , Term.test_case
        , Parser.test_case
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
    , "  o  m/enter/WD/GRD/goal"
    , "  o  m/enter/WD/GRD/hypotheses"
    , "  o  m/enter/WD/GRD/relation"
    , "  o  m/enter/WD/GRD/step 1"
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

instance Arbitrary LatexNode where
    arbitrary = do
            n <- choose (1,7) :: Gen Int
            if n == 1 
                then do
                    n <- choose (0,length kw+2)
                    name <- if length kw <= n
                        then arbitrary :: Gen String
                        else return (kw !! n)
                    m    <- choose (0,6) :: Gen Int
                    xs   <- (`Doc` li 0 0) <$> forM [1..m] 
                        (\_ -> arbitrary :: Gen LatexNode)
                    return $ Env name (li 0 0) xs (li 0 0)
            else if n == 2
                then do
                    b  <- elements [Curly,Square]
                    m    <- choose (0,6) :: Gen Int
                    xs   <- (`Doc` li 0 0) <$> forM [1..m] 
                        (\_ -> arbitrary :: Gen LatexNode)
                    return $ Bracket b (li 0 0) xs (li 0 0)
            else if 2 < n
                then do
                    xs <- arbitrary :: Gen String
                    let ys = if L.null xs 
                        then "x"
                        else xs
--                    n <- choose (0,length cmd+1)
                    case read_lines tex_tokens "" ys of
                        Right x -> return $ Text (map fst x) (li 0 0)
                        Left _  -> return $ Text [TextBlock "x" (li 0 0)] (li 0 0)
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

tree0' :: T LatexNode
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
