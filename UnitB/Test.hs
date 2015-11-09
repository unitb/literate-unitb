{-# LANGUAGE OverloadedStrings, QuasiQuotes #-}
module UnitB.Test where 

    -- Modules
import Document.Tests.Suite (lookupSequent)

import           Logic.Expr
import qualified Logic.Expr.Const as Exp
import           Logic.Expr.QuasiQuote 
import           Logic.Expr.Existential
import qualified Logic.TestGenericity as Gen

import Theories.FunctionTheory

import UnitB.AST
import UnitB.PO 

import Z3.Z3

    -- Libraries
import Control.Monad
import Control.Lens

import           Data.Either
import           Data.List ( sort )
import           Data.Map as M hiding (map)

import Tests.UnitTest

import Utilities.Syntactic

test_case :: TestCase
test_case = test

test :: TestCase
test = test_cases 
        "Unit-B" 
        [  POCase "'x eventually increases' verifies" (check_mch example0) (result_example0)
        ,  POCase "train, model 0, verification" (check_mch train_m0) (result_train_m0)
        ,  Case "train, m0 transient / enablement PO" (get_tr_en_po train_m0) result_train_m0_tr_en_po
        ,  Case "train, m0 transient / falsification PO" (get_tr_neg_po train_m0) result_train_m0_tr_neg_po
        ,  Case "Feasibility and partitioning" case3 result3
        ,  Case "Debugging the partitioning" case4 result4
        ,  Gen.test_case
        ]

example0 :: Either [Error] RawMachine
example0 = do
        let (x,x',x_decl) = prog_var "x" int
            (y,_,y_decl) = prog_var "y" int
            li = LI "" 0 0
        inv0   <- with_li li (x `mzeq` (mzint 2 `mztimes` y))
        init0  <- with_li li (x `mzeq` mzint 0)
        init1  <- with_li li (y `mzeq` mzint 0)
        tr     <- with_li li (x `mzeq` mzint 0)
        co     <- with_li li (x `mzle` x')
        csched <- with_li li (x `mzeq` y)
        s0     <- with_li li (liftM (Assign x_decl) (x `mzplus` mzint 2))
        s1     <- with_li li (liftM (Assign y_decl) (y `mzplus` mzint 1))
        let tr0 = Tr empty tr ["evt"] empty_hint
            co0 = Co [] co
            ps = empty_property_set {
                _transient = 
                    fromList [
                        ("TR0", tr0)],
                _constraint =
                    fromList [
                        ("CO0", co0)],
                _inv = fromList [("J0", inv0)] }
            evt = empty_event
                    { _coarse_sched = singleton "sch0" csched
                    , _actions = fromList [
                        ("S0", s0),
                        ("S1", s1) ] }
            vs = fromList $ map as_pair [x_decl,y_decl]
            m  = (empty_machine "m0") & content assert %~ \m -> m
                & variables .~ vs
                & event_table .~ new_event_set vs (singleton "evt" evt)
                & inits .~ fromList 
                    [ ("init0", init0)
                    , ("init1", init1) ]
                & props .~ ps
        return m 

select :: ExprP -> ExprP -> ExprP
select      = typ_fun2 (mk_fun [] "select" [array gA gB, gA] gB)

train_m0 :: Either [Error] RawMachine
train_m0 = do
        let (st,_,st_decl) = prog_var "st" (array int bool)
            (t,t_decl) = Exp.var "t" int
        let li = LI "" 0 0
        inv0 <- with_li li (mzforall [t_decl] mztrue $
                   mzall [(zstore st t mzfalse `mzeq` zstore st t mzfalse)])
        c0   <- with_li li (st `select` t)
        a0   <- with_li li (liftM (Assign st_decl) $ zstore st t mzfalse)
        let inv = fromList [("J0",inv0)]
            enter = ("enter", empty_event)
            leave = ("leave", empty_event 
                    {   _indices = symbol_table [t_decl]
                    ,   _coarse_sched = singleton "C0" c0
                    ,   _actions   = fromList [("A0", a0)]
                    })
        tr <- with_li li (st `select` t)
        let props' = fromList [("TR0", Tr (symbol_table [t_decl]) tr ["leave"] hint)] 
            hint  = getExpr <$> TrHint (singleton "t" (int,c [expr| t = t' |])) Nothing
            c     = ctx $ do
                    [var| t, t' : \Int |]
            ps    = empty_property_set { _transient = props', _inv = inv }
            vs    = fromList $ map as_pair [st_decl]
            m     = empty_machine "train_m0" & content assert %~ \m -> m
                        & props .~ ps
                        & variables .~ vs
                        & event_table .~ new_event_set vs (fromList [enter, leave])
        return m

result_example0 :: String
result_example0 = unlines 
    [ "  o  m0/CO0/CO/WD"
    , "  o  m0/INIT/FIS/x"
    , "  o  m0/INIT/FIS/y"
    , "  o  m0/INIT/INV/J0"
    , "  o  m0/INIT/WD"
    , "  o  m0/INIT/WWD"
    , "  o  m0/INV/WD"
    , "  o  m0/SKIP/CO/CO0"
    , "  o  m0/TR/TR0/evt/EN"
    , "  o  m0/TR/TR0/evt/NEG"
    , "  o  m0/TR0/TR/WD"
    , "  o  m0/evt/CO/CO0"
    , "  o  m0/evt/FIS/x@prime"
    , "  o  m0/evt/FIS/y@prime"
    , "  o  m0/evt/INV/J0"
    , "  o  m0/evt/WD/ACT/S0"
    , "  o  m0/evt/WD/ACT/S1"
    , "  o  m0/evt/WD/C_SCH"
    , "  o  m0/evt/WD/F_SCH"
    , "  o  m0/evt/WD/GRD"
    , "  o  m0/evt/WWD"
    , "passed 21 / 21"
    ]

result_train_m0 :: String
result_train_m0 = unlines 
    [ "  o  train_m0/INIT/INV/J0"
    , "  o  train_m0/INIT/WD"
    , "  o  train_m0/INIT/WWD"
    , "  o  train_m0/INV/WD"
    , "  o  train_m0/TR/TR0/WFIS/t/t@prime"
    , "  o  train_m0/TR/TR0/leave/EN"
    , "  o  train_m0/TR/TR0/leave/NEG"
    , "  o  train_m0/TR0/TR/WD"
    , "  o  train_m0/TR0/TR/WD/witness/t"
    , "  o  train_m0/enter/FIS/st@prime"
    , "  o  train_m0/enter/INV/J0"
    , "  o  train_m0/enter/WD/C_SCH"
    , "  o  train_m0/enter/WD/F_SCH"
    , "  o  train_m0/enter/WD/GRD"
    , "  o  train_m0/enter/WWD"
    , "  o  train_m0/leave/FIS/st@prime"
    , "  o  train_m0/leave/INV/J0"
    , "  o  train_m0/leave/WD/ACT/A0"
    , "  o  train_m0/leave/WD/C_SCH"
    , "  o  train_m0/leave/WD/F_SCH"
    , "  o  train_m0/leave/WD/GRD"
    , "  o  train_m0/leave/WWD"
    , "passed 22 / 22"
    ]

result_example0_tr_en_po :: String
result_example0_tr_en_po = unlines [
    " sort: pfun [a,b], set [a]",
    " x: Int",
    " y: Int",
    " (= x (* 2 y))",
    "|----",
    " (=> (= x 0) (= x y))"]

result_train_m0_tr_en_po :: String
result_train_m0_tr_en_po = unlines 
    [ " sort: Pair [a,b], set [a]"
    , " const[_a,_b]: b -> (Array a b)"
    , " finite[_t]: (set t) -> Bool"
    , " ident[_a]: (Array a a)"
    , " mk-set[_t]: t -> (set t)"
    , " qsum[_a]: (set a) x (Array a Int) -> Int"
    , " qunion[_a,_b]: (set a) x (Array a (set b)) -> (set b)"
    , " set[_a,_b]: (set a) x (Array a b) -> (set b)"
    , " t@param[]: Int"
    , " all[_t] : (set t)  =  ((as const (set t)) true)"
    , " compl[_t] : (s1 (set _t)) -> (set t)  =  ((_ map not) s1)"
    , " elem[_t] : (x _t) x (s1 (set _t)) -> Bool  =  (select s1 x)"
    , " empty-set[_t] : (set t)  =  ((as const (set t)) false)"
    , " set-diff[_t] : (s1 (set _t)) x (s2 (set _t)) -> (set t)  =  (intersect s1 ((_ map not) s2))"
    , " st-subset[_t] : (s1 (set _t)) x (s2 (set _t)) -> Bool  =  (and (subset s1 s2) (not (= s1 s2)))"
    , " st: (Array Int Bool)"
    , " st@prime: (Array Int Bool)"
    , " t: Int"
    , " (forall ( (t Int) )"
    , "         (=> true (= (store st t false) (store st t false))))"
    , " (forall ( (term (Array _t Int)) )"
    , "         (=> true (= (qsum@@_t empty-set@@_t term) 0)))"
    , " (forall ( (r (set _t))"
    , "           (term (Array _t Int))"
    , "           (x _t) )"
    , "         (=> true"
    , "             (=> (not (elem@@_t x r))"
    , "                 (= (qsum@@_t (union r (mk-set@@_t x)) term)"
    , "                    (+ (qsum@@_t r term) (select term x))))))"
    , " (forall ( (r (set _t))"
    , "           (r0 (set _t))"
    , "           (term (Array _t Int)) )"
    , "         (=> true"
    , "             (=> (= (intersect r r0) empty-set@@_t)"
    , "                 (= (qsum@@_t (union r r0) term)"
    , "                    (+ (qsum@@_t r term) (qsum@@_t r0 term))))))"
    , " (forall ( (r (set _t)) )"
    , "         (=> true"
    , "             (=> (finite@@_t r)"
    , "                 (<= 0 (qsum@@_t r (const@@_t@@Int 1))))))"
    , " (forall ( (r (set _t)) )"
    , "         (=> true"
    , "             (= (= (qsum@@_t r (const@@_t@@Int 1)) 0)"
    , "                (= r empty-set@@_t))))"
    , " (forall ( (x _t) )"
    , "         (=> true"
    , "             (= (qsum@@_t (mk-set@@_t x) (const@@_t@@Int 1)) 1)))"
    , " (forall ( (r (set _t)) )"
    , "         (=> true"
    , "             (= (= (qsum@@_t r (const@@_t@@Int 1)) 1)"
    , "                (exists ( (x _t) ) (and true (= r (mk-set@@_t x)))))))"
    , " (forall ( (r (set _t))"
    , "           (r0 (set _t)) )"
    , "         (=> true"
    , "             (=> (= (intersect r r0) empty-set@@_t)"
    , "                 (= (qsum@@_t (union r r0) (const@@_t@@Int 1))"
    , "                    (+ (qsum@@_t r (const@@_t@@Int 1))"
    , "                       (qsum@@_t r0 (const@@_t@@Int 1)))))))"
    , " (forall ( (x _t0)"
    , "           (y _t1) )"
    , "         (=> true (= (select (const@@_t1@@_t0 x) y) x)))"
    , " (forall ( (x _t0) ) (=> true (= (select ident@@_t0 x) x)))"
    , " (forall ( (x _t)"
    , "           (y _t) )"
    , "         (=> true (= (elem@@_t x (mk-set@@_t y)) (= x y))))"
    , " (forall ( (r1 (set _t0))"
    , "           (term (Array _t0 _t))"
    , "           (y _t) )"
    , "         (=> true"
    , "             (= (elem@@_t y (set@@_t0@@_t r1 term))"
    , "                (exists ( (x _t0) )"
    , "                        (and (elem@@_t0 x r1) (= (select term x) y))))))"
    , " (forall ( (r1 (set _t0))"
    , "           (term (Array _t0 _t))"
    , "           (y _t) )"
    , "         (=> true"
    , "             (= (= (set@@_t0@@_t r1 term) (mk-set@@_t y))"
    , "                (forall ( (x _t0) )"
    , "                        (=> (elem@@_t0 x r1) (= (select term x) y))))))"
    , " (forall ( (s1 (set _t))"
    , "           (s2 (set _t)) )"
    , "         (=> true"
    , "             (=> (finite@@_t s1) (finite@@_t (set-diff@@_t s1 s2)))))"
    , " (forall ( (s1 (set _t))"
    , "           (s2 (set _t)) )"
    , "         (=> true"
    , "             (=> (and (finite@@_t s1) (finite@@_t s2))"
    , "                 (finite@@_t (union s1 s2)))))"
    , " (forall ( (x _t) ) (=> true (finite@@_t (mk-set@@_t x))))"
    , " (finite@@_t empty-set@@_t)"
    , " (forall ( (s1 (set _t))"
    , "           (s2 (set _t)) )"
    , "         (=> true"
    , "             (=> (subset s1 s2)"
    , "                 (=> (finite@@_t s2) (finite@@_t s1)))))"
    , " (forall ( (r1 (set _t0)) )"
    , "         (=> true (= (set@@_t0@@_t0 r1 ident@@_t0) r1)))"
    , " (forall ( (terms (Array _t0 (set _t))) )"
    , "         (=> true"
    , "             (= (qunion@@_t0@@_t empty-set@@_t0 terms)"
    , "                empty-set@@_t)))"
    , " (forall ( (terms (Array _t0 (set _t)))"
    , "           (x _t0) )"
    , "         (=> true"
    , "             (= (qunion@@_t0@@_t (mk-set@@_t0 x) terms)"
    , "                (select terms x))))"
    , " (forall ( (r1 (set _t0))"
    , "           (r2 (set _t0))"
    , "           (terms (Array _t0 (set _t))) )"
    , "         (=> true"
    , "             (= (qunion@@_t0@@_t (union r1 r2) terms)"
    , "                (union (qunion@@_t0@@_t r1 terms)"
    , "                       (qunion@@_t0@@_t r2 terms)))))"
    , " (forall ( (r1 (set _t0))"
    , "           (terms (Array _t0 (set _t)))"
    , "           (terms0 (Array _t0 (set _t))) )"
    , "         (=> true"
    , "             (=> (forall ( (x _t0) )"
    , "                         (=> (elem@@_t0 x r1)"
    , "                             (= (select terms x) (select terms0 x))))"
    , "                 (= (qunion@@_t0@@_t r1 terms)"
    , "                    (qunion@@_t0@@_t r1 terms0)))))"
    , " (= t t@param)"
    , "|----"
    , " (=> (select st t) (select st t@param))"
    ]

result_train_m0_tr_neg_po :: String
result_train_m0_tr_neg_po = unlines 
    [ " sort: Pair [a,b], set [a]"
    , " const[_a,_b]: b -> (Array a b)"
    , " finite[_t]: (set t) -> Bool"
    , " ident[_a]: (Array a a)"
    , " mk-set[_t]: t -> (set t)"
    , " qsum[_a]: (set a) x (Array a Int) -> Int"
    , " qunion[_a,_b]: (set a) x (Array a (set b)) -> (set b)"
    , " set[_a,_b]: (set a) x (Array a b) -> (set b)"
    , " t@param[]: Int"
    , " all[_t] : (set t)  =  ((as const (set t)) true)"
    , " compl[_t] : (s1 (set _t)) -> (set t)  =  ((_ map not) s1)"
    , " elem[_t] : (x _t) x (s1 (set _t)) -> Bool  =  (select s1 x)"
    , " empty-set[_t] : (set t)  =  ((as const (set t)) false)"
    , " set-diff[_t] : (s1 (set _t)) x (s2 (set _t)) -> (set t)  =  (intersect s1 ((_ map not) s2))"
    , " st-subset[_t] : (s1 (set _t)) x (s2 (set _t)) -> Bool  =  (and (subset s1 s2) (not (= s1 s2)))"
    , " st: (Array Int Bool)"
    , " st@prime: (Array Int Bool)"
    , " t: Int"
    , " (= st@prime (store st t@param false))"
    , " (select st t@param)"
    , " (forall ( (t Int) )"
    , "         (=> true (= (store st t false) (store st t false))))"
    , " (forall ( (term (Array _t Int)) )"
    , "         (=> true (= (qsum@@_t empty-set@@_t term) 0)))"
    , " (forall ( (r (set _t))"
    , "           (term (Array _t Int))"
    , "           (x _t) )"
    , "         (=> true"
    , "             (=> (not (elem@@_t x r))"
    , "                 (= (qsum@@_t (union r (mk-set@@_t x)) term)"
    , "                    (+ (qsum@@_t r term) (select term x))))))"
    , " (forall ( (r (set _t))"
    , "           (r0 (set _t))"
    , "           (term (Array _t Int)) )"
    , "         (=> true"
    , "             (=> (= (intersect r r0) empty-set@@_t)"
    , "                 (= (qsum@@_t (union r r0) term)"
    , "                    (+ (qsum@@_t r term) (qsum@@_t r0 term))))))"
    , " (forall ( (r (set _t)) )"
    , "         (=> true"
    , "             (=> (finite@@_t r)"
    , "                 (<= 0 (qsum@@_t r (const@@_t@@Int 1))))))"
    , " (forall ( (r (set _t)) )"
    , "         (=> true"
    , "             (= (= (qsum@@_t r (const@@_t@@Int 1)) 0)"
    , "                (= r empty-set@@_t))))"
    , " (forall ( (x _t) )"
    , "         (=> true"
    , "             (= (qsum@@_t (mk-set@@_t x) (const@@_t@@Int 1)) 1)))"
    , " (forall ( (r (set _t)) )"
    , "         (=> true"
    , "             (= (= (qsum@@_t r (const@@_t@@Int 1)) 1)"
    , "                (exists ( (x _t) ) (and true (= r (mk-set@@_t x)))))))"
    , " (forall ( (r (set _t))"
    , "           (r0 (set _t)) )"
    , "         (=> true"
    , "             (=> (= (intersect r r0) empty-set@@_t)"
    , "                 (= (qsum@@_t (union r r0) (const@@_t@@Int 1))"
    , "                    (+ (qsum@@_t r (const@@_t@@Int 1))"
    , "                       (qsum@@_t r0 (const@@_t@@Int 1)))))))"
    , " (forall ( (x _t0)"
    , "           (y _t1) )"
    , "         (=> true (= (select (const@@_t1@@_t0 x) y) x)))"
    , " (forall ( (x _t0) ) (=> true (= (select ident@@_t0 x) x)))"
    , " (forall ( (x _t)"
    , "           (y _t) )"
    , "         (=> true (= (elem@@_t x (mk-set@@_t y)) (= x y))))"
    , " (forall ( (r1 (set _t0))"
    , "           (term (Array _t0 _t))"
    , "           (y _t) )"
    , "         (=> true"
    , "             (= (elem@@_t y (set@@_t0@@_t r1 term))"
    , "                (exists ( (x _t0) )"
    , "                        (and (elem@@_t0 x r1) (= (select term x) y))))))"
    , " (forall ( (r1 (set _t0))"
    , "           (term (Array _t0 _t))"
    , "           (y _t) )"
    , "         (=> true"
    , "             (= (= (set@@_t0@@_t r1 term) (mk-set@@_t y))"
    , "                (forall ( (x _t0) )"
    , "                        (=> (elem@@_t0 x r1) (= (select term x) y))))))"
    , " (forall ( (s1 (set _t))"
    , "           (s2 (set _t)) )"
    , "         (=> true"
    , "             (=> (finite@@_t s1) (finite@@_t (set-diff@@_t s1 s2)))))"
    , " (forall ( (s1 (set _t))"
    , "           (s2 (set _t)) )"
    , "         (=> true"
    , "             (=> (and (finite@@_t s1) (finite@@_t s2))"
    , "                 (finite@@_t (union s1 s2)))))"
    , " (forall ( (x _t) ) (=> true (finite@@_t (mk-set@@_t x))))"
    , " (finite@@_t empty-set@@_t)"
    , " (forall ( (s1 (set _t))"
    , "           (s2 (set _t)) )"
    , "         (=> true"
    , "             (=> (subset s1 s2)"
    , "                 (=> (finite@@_t s2) (finite@@_t s1)))))"
    , " (forall ( (r1 (set _t0)) )"
    , "         (=> true (= (set@@_t0@@_t0 r1 ident@@_t0) r1)))"
    , " (forall ( (terms (Array _t0 (set _t))) )"
    , "         (=> true"
    , "             (= (qunion@@_t0@@_t empty-set@@_t0 terms)"
    , "                empty-set@@_t)))"
    , " (forall ( (terms (Array _t0 (set _t)))"
    , "           (x _t0) )"
    , "         (=> true"
    , "             (= (qunion@@_t0@@_t (mk-set@@_t0 x) terms)"
    , "                (select terms x))))"
    , " (forall ( (r1 (set _t0))"
    , "           (r2 (set _t0))"
    , "           (terms (Array _t0 (set _t))) )"
    , "         (=> true"
    , "             (= (qunion@@_t0@@_t (union r1 r2) terms)"
    , "                (union (qunion@@_t0@@_t r1 terms)"
    , "                       (qunion@@_t0@@_t r2 terms)))))"
    , " (forall ( (r1 (set _t0))"
    , "           (terms (Array _t0 (set _t)))"
    , "           (terms0 (Array _t0 (set _t))) )"
    , "         (=> true"
    , "             (=> (forall ( (x _t0) )"
    , "                         (=> (elem@@_t0 x r1)"
    , "                             (= (select terms x) (select terms0 x))))"
    , "                 (= (qunion@@_t0@@_t r1 terms)"
    , "                    (qunion@@_t0@@_t r1 terms0)))))"
    , " (= t t@param)"
    , "|----"
    , " (=> (select st t) (not (select st@prime t)))"
    ]

check_mch :: Either [Error] RawMachine -> IO (String, Map Label Sequent)
check_mch em = do
    case em of
        Right m -> do
            let r = head $ rights [proof_obligation m]
            (xs,_,_) <- str_verify_machine m
            return (xs,r)
        Left x -> return (show_err x, empty)

get_cmd_tr_po :: Monad m 
              => Either [Error] RawMachine 
              -> m (Either [Error] String)
get_cmd_tr_po em = return (do
        m <- em
        let lbl = composite_label [as_label $ _name m, "TR/TR0/t@param"]
        pos <- proof_obligation m
        let po = pos ! lbl
            cmd =  z3_code po
        return $ unlines $ map pretty_print' cmd)
    
get_tr_en_po :: Either [Error] RawMachine -> IO String
get_tr_en_po em = either (return . show_err) return $ do
        m   <- em
        pos <- proof_obligation m
        let lbl = composite_label [as_label $ _name m, "TR/TR0/leave/EN"]
            po  = either error id $ lookupSequent lbl pos
        return $ show po

get_tr_neg_po :: Either [Error] RawMachine -> IO String
get_tr_neg_po em = either (return . show_err) return $ do
        m   <- em
        pos <- proof_obligation m
        let lbl = composite_label [as_label $ _name m, "TR/TR0/leave/NEG"]
            po  = either error id $ lookupSequent lbl pos
        return $ show po

case3 :: IO [([Var], [Expr])]
result3 :: [([Var], [Expr])]
case4 :: IO ([(Int, Int)], [(Var, Int)], [(Expr, Int)])
result4 :: ([(Int, Int)], [(Var, Int)], [(Expr, Int)])
(case3, result3, case4, result4) = ($typeCheck) $ do
            e0 <- a
            e1 <- d `mzplus` b
            e2 <- b `mzplus` c
            e3 <- c `mzplus` d
            let arg0 = [a_decl,b_decl,c_decl,d_decl] 
                arg1 = [e0,e1,e2,e3]
            return 
                ( return $ map f $ partition_expr arg0 arg1
                , [([a_decl],[e0]),([b_decl,c_decl,d_decl],[e2,e3,e1])]
                , return $ get_partition arg0 arg1
                , ( [ (0,0), (1,1)
                    , (2,1), (3,1)
                    , (4,0), (5,1)
                    , (6,1), (7,1)]
                , [ (a_decl,0), (b_decl,1)
                  , (c_decl,2), (d_decl,3)]
                , [ (e0,4), (e2,6), (e3,7)
                    , (e1,5)]) )
    where
        (a,a_decl) = Exp.var "a" int
        (b,b_decl) = Exp.var "b" int
        (c,c_decl) = Exp.var "c" int
        (d,d_decl) = Exp.var "d" int
        f (xs,ys) = (sort xs, sort ys)
