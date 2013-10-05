module UnitB.Test where 

    -- Modules
import UnitB.AST
import qualified UnitB.TestGenericity as Gen
import UnitB.PO
import UnitB.Label
import UnitB.FunctionTheory

import Z3.Z3

    -- Libraries
import Control.Monad

import           Data.Maybe 
import           Data.Map hiding (map)
import qualified Data.Set as S hiding (map, fromList, insert, empty)

import System.IO
import System.Posix.IO

import Tests.UnitTest

import Utilities.Syntactic

test = test_cases 
        [  Case "'x eventually increases' verifies" (check_mch example0) (result_example0)
        ,  Case "train, model 0, verification" (check_mch train_m0) (result_train_m0)
        ,  Case "train, m0 transient / falsification PO" (get_tr_po train_m0) (result_train_m0_tr_po)
        ,  Gen.test_case
        ]

example0 = do
        let (x,x',x_decl) = prog_var "x" int
        let (y,y',y_decl) = prog_var "y" int
        inv0   <- with_li (0,0) (x `mzeq` (mzint 2 `mztimes` y))
        init0  <- with_li (0,0) (x `mzeq` mzint 0)
        init1  <- with_li (0,0) (y `mzeq` mzint 0)
        tr     <- with_li (0,0) (x `mzeq` mzint 0)
        co     <- with_li (0,0) (x `mzle` x')
        csched <- with_li (0,0) (x `mzeq` y)
        s0     <- with_li (0,0) (x' `mzeq` (x `mzplus` mzint 2))
        s1     <- with_li (0,0) (y' `mzeq` (y `mzplus` mzint 1))
        let tr0 = Transient empty tr (label "evt") 0
            co0 = Co [] co
            ps = empty_property_set {
                transient = 
                    fromList [
                        (label "TR0", tr0)],
                constraint =
                    fromList [
                        (label "CO0", co0)],
                inv = fromList [(label "J0", inv0)] }
            sch_ref0 = (weaken $ label "evt")
                { remove = S.singleton (label "default")
                , add    = S.singleton (label "sch0") }
            evt = empty_event
                    { sched_ref = singleton 0 sch_ref0
                    , c_sched = insert (label "sch0") csched default_schedule
                    , action = fromList [
                        (label "S0", s0),
                        (label "S1", s1) ] }
            m = (empty_machine "m0") 
                { variables = fromList $ map as_pair [x_decl,y_decl]
                , events = singleton (label "evt") evt
                , inits = fromList 
                    [ (label "init0", init0)
                    , (label "init1", init1) ]
                , props = ps }
        return m

train_m0 = do
        let (st,st',st_decl) = prog_var "st" (ARRAY int BOOL)
            (t,t_decl) = var "t" int
        inv0 <- with_li (0,0) (mzforall [t_decl] mztrue $
                   mzall [(zstore st t mzfalse `mzeq` zstore st t mzfalse)])
        c0   <- with_li (0,0) (st `zselect` t)
        a0   <- with_li (0,0) (st' `mzeq` zstore st t mzfalse)
        let inv = fromList [(label "J0",inv0)]
            sch_ref0 = (weaken $ label "evt")
                { remove = S.singleton (label "default")
                , add    = S.singleton (label "C0") }
            enter = (label "enter", empty_event)
            leave = (label "leave", empty_event 
                    {   indices = symbol_table [t_decl]
                    ,   sched_ref = singleton 0 sch_ref0
                    ,   c_sched = insert (label "C0") c0 $ default_schedule
                    ,   action  = fromList [(label "A0", a0)]
                    })
        tr <- with_li (0,0) (st `zselect` t)
        let props = fromList [(label "TR0", Transient (symbol_table [t_decl]) tr (label "leave") 0)] 
            ps    = empty_property_set { transient = props, inv = inv }
            m     = (empty_machine "train_m0") 
                        { props = ps
                        , variables = fromList $ map as_pair [st_decl]
                        , events = fromList [enter, leave] }
        return m

result_example0 = unlines [
    "  o  m0/INIT/FIS",
    "  o  m0/INIT/INV/J0",
    "  o  m0/SKIP/CO/CO0",
    "  o  m0/evt/CO/CO0",
    "  o  m0/evt/FIS",
    "  o  m0/evt/INV/J0",
    "  o  m0/evt/SCH",
    "  o  m0/evt/TR/TR0",
    "passed 8 / 8"]

result_train_m0 = unlines [
    "  o  train_m0/INIT/FIS",
    "  o  train_m0/INIT/INV/J0",
    "  o  train_m0/enter/FIS",
    "  o  train_m0/enter/INV/J0",
    "  o  train_m0/enter/SCH",
    "  o  train_m0/leave/FIS",
    "  o  train_m0/leave/INV/J0",
    "  o  train_m0/leave/SCH",
    "  o  train_m0/leave/TR/TR0",
    "passed 9 / 9"]

result_example0_tr_en_po = unlines [
    " sort: pfun [a,b], set [a]",
    " x: Int",
    " y: Int",
    " (= x (* 2 y))",
    "|----",
    " (=> (= x 0) (= x y))"]

result_train_m0_tr_po = unlines 
    [ " sort: , , , pfun [a,b], set [a]"
    , " st: (Array Int Bool)"
    , " st@prime: (Array Int Bool)"
    , " t: Int"
    , " (forall ((t Int)) (=> true (= (store st t false) (store st t false))))"
    , "|----"
    , " (exists ((t@param Int))"
          ++   " (and true"
          ++   " (and (=> (select st t) (select st t@param))"
          ++        " (=> (and (select st t)"
          ++                 " (select st t@param)"
          ++                 " (= st@prime (store st t@param false)))"
          ++            " (not (select st@prime t))))))"
    ]

test_case = ("Unit-B", test, True)

check_mch :: Either [Error] Machine -> IO String
check_mch em = do
    case em of
        Right m -> do
            (xs,_,_) <- str_verify_machine m
            return xs
        Left x -> return (show_err x)

get_cmd_tr_po em = return (do
        m <- em
        let lbl = composite_label [_name m, label "leave/TR/TR0"]
        pos <- proof_obligation m
        let po = pos ! lbl
        let cmd =  z3_code po
        return $ unlines $ map (show . as_tree) cmd)
    
get_tr_po :: Either [Error] Machine -> IO String
get_tr_po em = case (do
        m <- em
        let lbl = composite_label [_name m, label "leave/TR/TR0"]
        pos <- proof_obligation m
        let po = pos ! lbl
        let cmd = z3_code po
        return $ show po) of
            Right xs -> return xs
            Left xs  -> return $ show_err xs
