module UnitB.Test where 

import Control.Monad

import Data.Map hiding (map)

import System.IO
import System.Posix.IO

import Tests.UnitTest

import UnitB.AST
import UnitB.PO

import Z3.Z3
import Z3.Const
import Z3.Def

example0 :: PropertySet
example0 = (empty_property_set "") {
                machine = m,
                prog_prop = 
                    fromList [
                        (label "TR0", tr0),
                        (label "CO0", co0)],
                inv = fromList [(label "J0", inv0)] }
    where
        evt = empty_event { 
            c_sched = singleton (label "sch0") (x `zeq` y),   
            action = fromList [
                (label "S0", x' `zeq` (x `zplus` zint 2)),
                (label "S1", y' `zeq` (y `zplus` zint 1)) ] }
        m = (empty_machine "m0") {
            variables = fromList $ map as_pair [x_decl,y_decl],
            events = singleton (label "evt") evt,
            inits = [x `zeq` zint 0, y `zeq` zint 0] }
        inv0 = x `zeq` (zint 2 `ztimes` y)
        tr0 = Transient [] (x `zeq` zint 0) (label "evt")
        co0 = Co [] (x `zle` x')
        (x,x',x_decl) = prog_var "x" INT
        (y,y',y_decl) = prog_var "y" INT

train_m0 = (empty_property_set "") { machine = m, prog_prop = props, inv = inv }
    where
        m = (empty_machine "train_m0") {
            variables = fromList $ map as_pair [st_decl],
            events = fromList [enter, leave] }
        props = fromList [
            (label "TR0", Transient [t_decl] (zapply st t) $ label "leave")]
        inv = fromList [inv0]
        inv0 = (label "J0", zforall [t_decl] $
                    zall [(zovl st t zfalse `zeq` zovl st t zfalse)])
        (st,st',st_decl) = prog_var "st" (ARRAY INT BOOL)
        (t,t_decl) = var "t" INT
        enter = (label "enter", empty_event)
        leave = (label "leave", empty_event {
                indices = [t_decl],
                c_sched = fromList [(label "C0", (zapply st t))],
                action  = fromList [(label "A0", st' `zeq` zovl st t zfalse)]
            })

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
    " o m0/INV/INIT/J0",
    " o m0/SKIP/CO/CO0",
    " o m0/evt/CO/CO0",
    " o m0/evt/FIS",
    " o m0/evt/INV/J0",
    " o m0/evt/SCH",
    " o m0/evt/TR/EN/TR0",
    " o m0/evt/TR/NEG/TR0",
    "passed 8 / 8"]
--    ""]

result_train_m0 = unlines [
    " o train_m0/INV/INIT/J0",
    " o train_m0/enter/FIS",
    " o train_m0/enter/INV/J0",
    " o train_m0/enter/SCH",
    " x train_m0/leave/FIS",
    " o train_m0/leave/INV/J0",
    " o train_m0/leave/SCH",
    " o train_m0/leave/TR/EN/TR0",
    " o train_m0/leave/TR/NEG/TR0",
    "passed 8 / 9"]
--    ""]



test_case = ("unit-B", test, True)

check m = do
    (_,xs) <- catch_output (\h -> h_verify_machine h m)
    return xs

test = test_suite_string [
    ("'x' eventually increases", check example0, result_example0),
    ("train, model 0", check train_m0, result_train_m0) ]

main = do
    verify_machine example0
    verify_machine train_m0
    return ()