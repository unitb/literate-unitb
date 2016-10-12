{-# LANGUAGE OverloadedStrings #-}
module Document.Tests.LockFreeDeque 
    -- ( test_case, test, path4, result4 )
where

    -- Modules
import Document.Tests.Suite as S
import Document.Tests.LockFreeDeque.Stable

import Logic.Proof

import UnitB.Expr
import UnitB.QuasiQuote

    -- Libraries
import Control.Lens hiding (indices)
import Control.Precondition ((!))

import Data.Graph.Bipartite
import Data.List as L
import Data.Map as M hiding ((!))
import Data.Set  as S

import Test.UnitTest hiding (name)

test_case :: TestCase
test_case = test

test :: TestCase
test = test_cases
            "Specification and refinement of a lock-free algorithm"
            [ (poCase "test 0, verification, specification with intervals" 
                (verify path0 0) result0)
            , (poCase "test 1, verification, failed proof with intervals" 
                (verify path1 0) result1)
            , (stringCase "test 2, error message name clash in guards" 
                case2 result2)
            , (poCase "test 3, verification, looking up function outside of domain" 
                (verify path3 0) result3)
            , (poCase "test 4, m1, liveness implemented with conditional behavior"
                (verify path4 1) result4)
            , (stringCase "test 5, transient, two branches, enablement of non-empty"
                (proof_obligation path4 "m1/LIVE/m1:prog3/ensure/TR/m0:pop:left:non:empty/EN" 1)
                result5)
            , (stringCase "test 6, transient, two branches, enablement of empty"
                (proof_obligation path4 "m1/LIVE/m1:prog3/ensure/TR/m0:pop:left:empty/EN" 1)
                result6)
            , (stringCase "test 7, transient, two branches, negation of empty"
                (proof_obligation path4 "m1/LIVE/m1:prog3/ensure/TR/m0:pop:left:empty/NEG" 1)
                result7)
            , (stringCase "test 8, transient, two branches, negation of non-empty"
                (proof_obligation path4 "m1/LIVE/m1:prog3/ensure/TR/m0:pop:left:non:empty/NEG" 1)
                result8)
            , (stringCase "test 9, transient, two branches, follow and disjunction"
                (proof_obligation path4 "m1/LIVE/m1:prog3/ensure/TR/leadsto" 1)
                result9)
            , (stringCase "test 10, duplicate refinement of liveness properties"
                (find_errors path10)
                result10)
            , stringCase "test 11, missing witness"
                (find_errors path11)
                result11
            , poCase "test 12, carrier sets without using sets"
                case12 result12
            , poCase "test 13, event splitting"
                case13 result13
            , aCase "test 14, event splitting, event sets"
                case14 result14                
            , aCase "test 15, event splitting, expression sets"
                case15 result15
            , aCase "test 16, event splitting, index decl"
                case16 result16
            , stringCase "test 17, empty parameter list"
                case17 result17
            , stringCase "test 18, empty list in VarScope"
                case18 result18
            , stringCase "test 19, splitting POs"
                case19 result19
            , poCase "test 20, Lamport proofs"
                case20 result20
            , aCase "test 21, new index witness"
                case21 result21
            , aCase "test 22, new index proof obligation part a"
                case22 result22
            , aCase "test 23, new index proof obligation part b"
                case23 result23
            , poCase "test 24, scoping in index witness feasibility"
                case24 result24
            , poCase "test 25, parameter promotion and inheritance"
                case25 result25
            , poCase "test 26, scoping problem in sequents"
                case26 result26
            -- , POCase "test 27, problem: failure in WD-checking"
            --     case27 result27
            , stringCase "test 28, large WD-condition"
                case28 result28
            , stringCase "test 29, weakening and splitting / disjunction"
                case29 result29
            , stringCase "test 30, weakening and splitting / safety"
                case30 result30
            , stringCase "test 31, INIT/fis"
                case31 result31
            , stringCase "test 32, inferring used record types"
                case32 result32
            , poCase "test 33, verifying with inferred records"
                case33 result33
            , stringCase "test 34, using coarse schedules in proofs of safety of new events"
                case34 result34
            , poCase "test 35, weakened coarse schedule replacement leads-to"
                case35 result35
            , aCase "test 36, deleting indices - AST"
                case36 result36
            , stringCase "test 37, deleting indices - PO"
                case37 result37
            , poCase "test 38, deleting indices - verify"
                case38 result38
            , stringCase "test 39, deleting indices - Wit FIS"
                case39 result39
            , poCase "test 40, deleting indices - Wit FIS - verify"
                case40 result40
            , poCase "test 41, deleting indices - verify all"
                case41 result41
            , poCase "test 42, use new schedules in proofs of weakening"
                case42 result42
            , stringCase "test 43, use new schedules in proofs of weakening, PO"
                case43 result43
            -- , stringCase "test 44, weird error with merging"
            --     case44 result44
            , stringCase "test 45, weird error with merging"
                case45 result45
            , stringCase "test 46, inconsistent merge event"
                case46 result46
            , stringCase "test 47, deleting indices of non-existant event"
                case47 result47
            , stringCase "test 48, invariant violation upon index deletion"
                case48 result48
            , stringCase "test 49, guard strengthening / merging with index deletion"
                case49 result49
            , stringCase "test 50, improper error message"
                case50 result50
            , stringCase "test 51, invalid goal for liveness proof"
                case51 result51
            , stringCase "test 52, deleted variables are not primed"
                case52 result52
            , stringCase "test 53, bad rendering of expressions"
                case53 result53
            ]            

path0 :: FilePath
path0 = [path|Tests/lock-free deque/main.tex|]

path1 :: FilePath
path1 = [path|Tests/lock-free deque/main2.tex|]

path2 :: FilePath
path2 = [path|Tests/lock-free deque/main3.tex|]

case2 :: IO String
case2 = find_errors path2

path3 :: FilePath
path3 = [path|Tests/lock-free deque/main4.tex|]

path4 :: FilePath
path4 = [path|Tests/lock-free deque/main6.tex|]

path10 :: FilePath 
path10 = [path|Tests/lock-free deque/main6-err0.tex|]

path11 :: FilePath 
path11 = [path|Tests/lock-free deque/main6-err1.tex|]

path12 :: FilePath
path12 = [path|Tests/lock-free deque/main7-err0.tex|]

case12 :: IO (String, Map Label Sequent)
case12 = verify path12 0

path13 :: FilePath
path13 = [path|Tests/lock-free deque/main7.tex|]

case13 :: IO (String, Map Label Sequent)
case13 = verify path13 0

case14 :: IO (Either String ([SkipOrEvent],[SkipOrEvent],[SkipOrEvent]))
case14 = runEitherT $ do
    ms <- view' machines <$> get_system path13
    let m0 = ms ! "m0"
        m1 = ms ! "m1"
        m2 = ms ! "m2"
    return $ (m0,m1,m2) & each %~ (M.keys . rightMap . view' events)

result14 :: Either String ([SkipOrEvent],[SkipOrEvent],[SkipOrEvent])
result14 = Right $ ([Left SkipEvent,"evt"],[Left SkipEvent,"evt0","evt1","evt2"],[Left SkipEvent,"evt0","evt1","evt2"])

type ExprSet = [(SkipOrEvent,[Label])]

case15 :: IO (Either String (ExprSet,ExprSet,ExprSet))
case15 = runEitherT $ do
    ms <- view' machines <$> get_system path13
    let m0 = ms ! "m0"
        m1 = ms ! "m1"
        m2 = ms ! "m2"
        exprs e = S.toList $ keysSet (view actions e) `S.union` keysSet (view guards e)
    return $ (m0,m1,m2) & each %~ (M.toAscList . M.map exprs . rightMap . view' events)

result15 :: Either String (ExprSet,ExprSet,ExprSet)
result15 = Right   ( [(Left SkipEvent,[]),("evt",["act0"])]
                   , [(Left SkipEvent,[]),("evt0",["act0"]),("evt1",["act0","grd0"]),("evt2",["act0"])]
                   , [(Left SkipEvent,[]),("evt0",["act0"]),("evt1",["act0","grd0"]),("evt2",["act0"])])

case16 :: IO (Either String (ExprSet,ExprSet,ExprSet))
case16 = runEitherT $ do
    ms <- view' machines <$> get_system path13
    let m0 = ms ! "m0"
        m1 = ms ! "m1"
        m2 = ms ! "m2"
        decls e = L.map as_label $ M.keys (view indices e)
    return $ (m0,m1,m2) & each %~ (M.toAscList . M.map decls . rightMap . view' events)

result16 :: Either String (ExprSet,ExprSet,ExprSet)
result16 = Right   ( [(Left SkipEvent,[]),("evt",["p"])]
                   , [(Left SkipEvent,[]),("evt0",["p"]),("evt1",["p"]),("evt2",["p","q"])]
                   , [(Left SkipEvent,[]),("evt0",["p"]),("evt1",["p"]),("evt2",["p","q"])])

path17 :: FilePath
path17 = [path|Tests/lock-free deque/main8-err0.tex|]

case17 :: IO String
case17 = find_errors path17

path18 :: FilePath
path18 = [path|Tests/lock-free deque/main8-err1.tex|]

case18 :: IO String
case18 = find_errors path18

path19 :: FilePath
path19 = [path|Tests/lock-free deque/main8.tex|]

case19 :: IO String
case19 = proof_obligation path19 "m1/resp:pop:left/F_SCH/replace/eqv" 1

path20 :: FilePath
path20 = [path|Tests/lock-free deque/main9.tex|]

case20 :: IO POResult
case20 = verify path20 0

result21 :: Either [Error] (Map Name Witness)
result21 = Right $ symbol_table' witVar [(WitSuch b $ c [expr| b = ch |])]
    where
        b = z3Var "b" bool
        c = ctx $ do
            [var| b,ch : \Bool |]

case21 :: IO (Either [Error] (Map Name Witness))
case21 = runEitherT $ do
    m <- parse_machine' path20 1
    view ind_witness <$> S.lookup "handle" (m!.events.to leftMap)

case23 :: IO String
case23 = proof_obligation path20 "m1/handle/C_SCH/delay/0/prog/m1:prog1/lhs" 1

case22 :: IO String
case22 = proof_obligation path20 "m1/handle/C_SCH/delay/0/prog/m1:prog1/rhs/m1:sch0" 1

path24 :: FilePath
path24 = [path|Tests/lock-free deque/main10.tex|]

case24 :: IO POResult
case24 = verify path24 1

path25 :: FilePath
path25 = [path|Tests/lock-free deque/main11.tex|]

case25 :: IO POResult
case25 = verify path25 2

path26 :: FilePath
path26 = [path|Tests/lock-free deque/main12.tex|]

case26 :: IO POResult
case26 = verify path26 3

path27 :: FilePath
path27 = [path|Tests/lock-free deque/main13.tex|]

case27 :: IO POResult
case27 = verifyWith (timeout .= 5000 >> resource .= 2) path27 5

case28 :: IO String
case28 = proof_obligation path27 "m5/INV/WD" 5

path29 :: FilePath
path29 = [path|Tests/lock-free deque/main16.tex|]

case29 :: IO String
case29 = proof_obligation path29 "m5/handle:pushR/C_SCH/weaken" 5

case30 :: IO String
case30 = proof_obligation path29 "m5/handle:pushR/C_SCH/weaken/saf/add:popL/SAF/handle:pushR:empty" 5

case31 :: IO String
case31 = proof_obligation path27 "m5/INIT/FIS/item" 5

path32 :: FilePath
path32 = [path|Tests/pop-left.tex|]

case32 :: IO String
case32 = proof_obligation path32 "m0/add:popL/SCH/m0:grd0" 0

case33 :: IO POResult
case33 = verify path32 0 

path34 :: FilePath
path34 = [path|Tests/pop-left-t0.tex|]

case34 :: IO String
case34 = proof_obligation path34 "m1/read:LH/SKIP/EQL/ver" 1 

path35 :: FilePath
path35 = [path|Tests/pop-left-t1.tex|]

case35 :: IO POResult
case35 = verifyOnly path35 "m1/hdl:popL:more/C_SCH/delay/0/prog/m1:prog0/rhs/m1:sch0" 1
            -- m1/hdl:popL:more/C_SCH/delay/0/prog/m1:prog0/rhs/m1:sch0

path36 :: FilePath
path36 = [path|Tests/pop-left-t2.tex|]

case36 :: IO (Either [Error] [[Map Name Var]])
case36 = runEitherT $ do 
    rs <- parse' path36
    let getIndices :: (HasEvent' event Expr)
                   => Machine 
                   -> (BiGraph' SkipOrEvent AbstrEvent SkipOrEvent ConcrEvent () -> Map SkipOrEvent event)
                   -> [Map Name Var]
        getIndices r get = r!.partsOf (events.to get.ix (Right "hdl:popL:one").event'.indices)
    return $ concat [ [getIndices r leftMap,getIndices r rightMap] | r <- rs ]

result36 :: Either [Error] [[Map Name Var]]
result36 = Right [[],[v],[v],[M.empty]]
    where
        v = symbol_table [Var [smt|v|] int]

case37 :: IO String
case37 = proof_obligation path36 "m1/hdl:popL:more/GRD/str/m0:sch0" 1

case38 :: IO POResult
case38 = verifyOnly path36 "m1/hdl:popL:more/GRD/str/m0:sch0" 1

result38 :: String
result38 = unlines
    [ "  o  m1/hdl:popL:more/GRD/str/m0:sch0"
    , "passed 1 / 1"
    ]

case39 :: IO String
case39 = proof_obligation path36 "m1/hdl:popL:more/WFIS/v" 1

case40 :: IO POResult
case40 = verifyOnly path36 "m1/hdl:popL:more/WFIS/v" 1

result40 :: String
result40 = unlines
    [ "  o  m1/hdl:popL:more/WFIS/v"
    , "passed 1 / 1"
    ]

case41 :: IO POResult
case41 = verifyOnly path36 "m1/ext:popL:more/INV/m1:inv7" 1

result41 :: String
result41 = unlines
    [ "  o  m1/ext:popL:more/INV/m1:inv7"
    , "passed 1 / 1"
    ]

path42 :: FilePath
path42 = [path|Tests/pop-left-t3.tex|]

case42 :: IO POResult
case42 = verifyOnly path42 "m1/hdl:popL:more/C_SCH/weaken/m1:sch2" 1

result42 :: String
result42 = unlines
    [ "  o  m1/hdl:popL:more/C_SCH/weaken/m1:sch2"
    , "passed 1 / 1"
    ]

case43 :: IO String
case43 = proof_obligation path42 "m1/hdl:popL:more/C_SCH/weaken/m1:sch2" 1

path44 :: FilePath
path44 = [path|Tests/pop-left-t5.tex|]

case44 :: IO String
case44 = fmap (either id id) . runEitherT $ unlines . concatMap (L.map pretty.M.keys) <$> all_proof_obligations' path44 

result44 :: String
result44 = ""

path45 :: FilePath
path45 = [path|Tests/pop-left-t6.tex|]

case45 :: IO String
case45 = find_errors path45 

result45 :: String
result45 = unlines
    [ "Multiple expressions with the label m0:sch0"
    , "error 484:1:"
    , "\tdeleted coarse schedule (event 'hdl:popL:more')"
    , ""
    , "error 599:5:"
    , "\tdeleted coarse schedule (event 'hdl:popL:more')"
    , ""
    , ""
    , "Multiple expressions with the label m0:sch0"
    , "error 526:1:"
    , "\tdeleted coarse schedule (event 'hdl:popL:one')"
    , ""
    , "error 600:5:"
    , "\tdeleted coarse schedule (event 'hdl:popL:one')"
    , ""
    ]

path46 :: FilePath
path46 = [path|Tests/pop-left-t7.tex|]

case46 :: IO String
case46 = find_errors path46

result46 :: String
result46 = unlines
    [ "The events merged into read:LH (hdl:popL:empty,read:LH) do not all have an action labelled m0:act0"
    , "error 111:3:"
    , "\tEvent hdl:popL:empty, action m0:act0"
    , ""
    , ""
    , "The events merged into read:LH (hdl:popL:empty,read:LH) do not all have an action labelled m1:act2"
    , "error 427:3:"
    , "\tEvent read:LH, action m1:act2"
    , ""
    ]

path47 :: FilePath
path47 = [path|Tests/pop-left-t8.tex|]

case47 :: IO String
case47 = find_errors path47

result47 :: String
result47 = unlines
    [ "error 615:3:"
    , "    event 'hdl:popL:empty' is undeclared"
    ]

path48 :: FilePath
path48 = [path|Tests/pop-left-t9.tex|]

case48 :: IO String
case48 = find_errors path48

result48 :: String
result48 = unlines
    [ "error 615:3:"
    , "    event 'hdl:popL:empty' is undeclared"
    ]

path49 :: FilePath
path49 = [path|Tests/pop-left-t10.tex|]

case49 :: IO String
case49 = proof_obligation path49 "m2/read:LH/GRD/str" 2

path50 :: FilePath
path50 = [path|Tests/pop-left-t11.tex|]

case50 :: IO String
case50 = find_errors path50

result50 :: String
result50 = unlines
    [ "error 641:1:"
    , "    goal m1:prog1 is not a valid progress property"
    ]

path51 :: FilePath
path51 = [path|Tests/pop-left-t12.tex|]

case51 :: IO String
case51 = find_errors path51

result51 :: String
result51 = unlines
    [ "error 633:1:"
    , "    goal m1:prog2 is not a valid progress property"
    ]

path52 :: FilePath
path52 = [path|Tests/pop-left-t13.tex|]

case52 :: IO String
case52 = proof_obligation path52 "m2/read:LH/SAF/LIVE/m2:prog0/ensure" 2

path53 :: FilePath
path53 = [path|Tests/pop-left-t14.tex|]

case53 :: IO String
case53 = proof_obligation path53 "m1/INIT/FIS/sl$trash" 1
