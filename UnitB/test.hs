module UnitB.Test where 

import Control.Monad

--import Data.Maybe 
import Data.Map hiding (map)

import System.IO
import System.Posix.IO

import Tests.UnitTest

import UnitB.AST
import qualified UnitB.TestGenericity as Gen
import UnitB.PO
import UnitB.Theory
import UnitB.FunctionTheory

import Z3.Z3

mk_just xs = map fromJust xs
mk_snd_just xs = map (\(x,y) -> (x, fromJust y)) xs

test = test_cases 
        [  Case "'x eventually increases' verifies" (check example0) result_example0
        ,  Case "train, model 0, verification" (check train_m0) result_train_m0
        ,  Case "train, m0 PO" (get_tr_po train_m0) result_train_m0_tr_po
        ,  Case "example0: enabledness PO" (get_en_po example0) result_example0_tr_en_po
        ,  Gen.test_case
        ]

example0 :: Machine
example0 = m
    where
        evt = empty_event { 
            c_sched = Just $ singleton (label "sch0") $ fromJust (x `mzeq` y),   
            action = fromList $ mk_snd_just [
                (label "S0", x' `mzeq` (x `mzplus` mzint 2)),
                (label "S1", y' `mzeq` (y `mzplus` mzint 1)) ] }
        m = (empty_machine "m0") {
            variables = fromList $ map as_pair [x_decl,y_decl],
            events = singleton (label "evt") evt,
            inits = mk_just [x `mzeq` mzint 0, y `mzeq` mzint 0],
            props = ps }
        inv0 = fromJust (x `mzeq` (mzint 2 `mztimes` y))
        tr0 = Transient empty (fromJust (x `mzeq` mzint 0)) (label "evt")
        co0 = Co [] (fromJust (x `mzle` x'))
        (x,x',x_decl) = prog_var "x" INT
        (y,y',y_decl) = prog_var "y" INT
        ps = empty_property_set {
                program_prop = 
                    fromList [
                        (label "TR0", tr0),
                        (label "CO0", co0)],
                inv = fromList [(label "J0", inv0)] }

train_m0 :: Machine
train_m0 = m
    where
        m = (empty_machine "train_m0") {
            props = ps,
            variables = fromList $ map as_pair [st_decl],
            events = fromList [enter, leave] }
        props = fromList [
            (label "TR0", Transient (symbol_table [t_decl]) 
                (fromJust (st `zapply` t) ) $ label "leave")]
        inv = fromList $ mk_snd_just [inv0]
        inv0 = (label "J0", mzforall [t_decl] $
                    mzall [(mzovl st t mzfalse `mzeq` mzovl st t mzfalse)])
        (st,st',st_decl) = prog_var "st" (fun_type INT BOOL)
        (t,t_decl) = var "t" INT
        enter = (label "enter", empty_event)
        leave = (label "leave", empty_event {
                indices = symbol_table [t_decl],
                c_sched = Just $ fromList $ mk_snd_just [(label "C0", (st `zapply` t))],
                action  = fromList $ mk_snd_just [(label "A0", st' `mzeq` mzovl st t mzfalse)]
            })
        ps = empty_property_set { program_prop = props, inv = inv }

catch_output :: (Handle -> IO a) -> IO (a, String)
catch_output act = do
    (i,o) <- createPipe
    iH <- fdToHandle i
    oH <- fdToHandle o
    x <- act oH
    r <- hGetContents iH
--    closeFd i
--    closeFd o
    return (x,r)

result_example0 = unlines [
    "  o  m0/INIT/FIS",
    "  o  m0/INIT/INV/J0",
    "  o  m0/SKIP/CO/CO0",
    "  o  m0/evt/CO/CO0",
    "  o  m0/evt/FIS",
    "  o  m0/evt/INV/J0",
    "  o  m0/evt/SCH",
    "  o  m0/evt/TR/EN/TR0",
    "  o  m0/evt/TR/NEG/TR0",
    "passed 9 / 9"]
--    ""]

result_train_m0 = unlines [
    "  o  train_m0/INIT/FIS",
    "  o  train_m0/INIT/INV/J0",
    "  o  train_m0/enter/FIS",
    "  o  train_m0/enter/INV/J0",
    "  o  train_m0/enter/SCH",
    "  o  train_m0/leave/FIS",
    "  o  train_m0/leave/INV/J0",
    "  o  train_m0/leave/SCH",
    "  o  train_m0/leave/TR/EN/TR0",
    "  o  train_m0/leave/TR/NEG/TR0",
    "passed 10 / 10"]
--    ""]

result_example0_tr_en_po = unlines [
    " sort: pfun [a,b], set [a]",
    " x: Int",
    " y: Int",
    " (= x (* 2 y))",
    "|----",
    " (=> (= x 0) (= x y))"]

result_train_m0_tr_po = unlines [
    " sort: pfun [a,b], set [a]",
    " st: (pfun Int Bool)",
    " st@prime: (pfun Int Bool)",
    " t: Int",
    " (select st t)",
    " (forall ((t Int)) (= (store st t false) (store st t false)))",
    " (select st t)",
    " (= st@prime (store st t false))",
    "|----",
    " (not (select st@prime t))"
    ]

test_case = ("Unit-B", test, True)

check m = do
    (xs,_,_) <- str_verify_machine m
    return xs

main = do
    verify_machine example0
    verify_machine train_m0
    return ()
    
get_tr_po m = do
        let lbl = composite_label [_name m, label "leave/TR/NEG/TR0"]
        let po  = proof_obligation m ! lbl
        return $ show po

get_en_po m = do
        let lbl = composite_label [_name m, label "evt/TR/EN/TR0"]
        let po  = proof_obligation m ! lbl
        return $ show po
