module UnitB.Test where 

    -- Modules
import           Logic.Classes
import           Logic.Const
import           Logic.Expr
import           Logic.Label
import qualified Logic.TestGenericity as Gen

import Theories.FunctionTheory

import UnitB.AST
import UnitB.Feasibility
import UnitB.PO

import Z3.Z3

    -- Libraries
import           Data.List ( sort )
import           Data.Map hiding (map)
import qualified Data.Set as S hiding (map, fromList, insert, empty)

import Tests.UnitTest

import Utilities.Syntactic

test :: IO Bool
test = test_cases 
        [  Case "'x eventually increases' verifies" (check_mch example0) (result_example0)
        ,  Case "train, model 0, verification" (check_mch train_m0) (result_train_m0)
        ,  Case "train, m0 transient / falsification PO" (get_tr_po train_m0) (result_train_m0_tr_po)
        ,  Case "Feasibility and partitioning" case3 result3
        ,  Case "Debugging the partitioning" case4 result4
        ,  Gen.test_case
        ]

example0 :: Either [Error] Machine
example0 = do
        let (x,x',x_decl) = prog_var "x" int
        let (y,y',y_decl) = prog_var "y" int
        let li = LI "" 0 0
        inv0   <- with_li li (x `mzeq` (mzint 2 `mztimes` y))
        init0  <- with_li li (x `mzeq` mzint 0)
        init1  <- with_li li (y `mzeq` mzint 0)
        tr     <- with_li li (x `mzeq` mzint 0)
        co     <- with_li li (x `mzle` x')
        csched <- with_li li (x `mzeq` y)
        s0     <- with_li li (x' `mzeq` (x `mzplus` mzint 2))
        s1     <- with_li li (y' `mzeq` (y `mzplus` mzint 1))
        let tr0 = Transient empty tr (label "evt") empty Nothing
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
                    { sched_ref = [sch_ref0]
                    , scheds = insert (label "sch0") csched default_schedule
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

train_m0 :: Either [Error] Machine
train_m0 = do
        let (st,st',st_decl) = prog_var "st" (ARRAY int bool)
            (t,t_decl) = var "t" int
        let li = LI "" 0 0
        inv0 <- with_li li (mzforall [t_decl] mztrue $
                   mzall [(zstore st t mzfalse `mzeq` zstore st t mzfalse)])
        c0   <- with_li li (st `zselect` t)
        a0   <- with_li li (st' `mzeq` zstore st t mzfalse)
        let inv = fromList [(label "J0",inv0)]
            sch_ref0 = (weaken $ label "evt")
                { remove = S.singleton (label "default")
                , add    = S.singleton (label "C0") }
            enter = (label "enter", empty_event)
            leave = (label "leave", empty_event 
                    {   indices = symbol_table [t_decl]
                    ,   sched_ref = [sch_ref0]
                    ,   scheds  = insert (label "C0") c0 $ default_schedule
                    ,   action  = fromList [(label "A0", a0)]
                    })
        tr <- with_li li (st `zselect` t)
        let props = fromList [(label "TR0", Transient (symbol_table [t_decl]) tr (label "leave") empty Nothing)] 
            ps    = empty_property_set { transient = props, inv = inv }
            m     = (empty_machine "train_m0") 
                        { props = ps
                        , variables = fromList $ map as_pair [st_decl]
                        , events = fromList [enter, leave] }
        return m

result_example0 :: String
result_example0 = unlines [
    "  o  m0/INIT/FIS/x",
    "  o  m0/INIT/FIS/y",
    "  o  m0/INIT/INV/J0",
    "  o  m0/SKIP/CO/CO0",
    "  o  m0/evt/CO/CO0",
    "  o  m0/evt/FIS/x@prime",
    "  o  m0/evt/FIS/y@prime",
    "  o  m0/evt/INV/J0",
    "  o  m0/evt/SCH",
    "  o  m0/evt/TR/TR0/EN",
    "  o  m0/evt/TR/TR0/NEG",
    "passed 11 / 11"]

result_train_m0 :: String
result_train_m0 = unlines [
    "  o  train_m0/INIT/FIS/st",
    "  o  train_m0/INIT/INV/J0",
    "  o  train_m0/enter/FIS/st@prime",
    "  o  train_m0/enter/INV/J0",
    "  o  train_m0/enter/SCH",
    "  o  train_m0/leave/FIS/st@prime",
    "  o  train_m0/leave/INV/J0",
    "  o  train_m0/leave/SCH",
    "  o  train_m0/leave/TR/TR0",
    "passed 9 / 9"]
 
result_example0_tr_en_po :: String
result_example0_tr_en_po = unlines [
    " sort: pfun [a,b], set [a]",
    " x: Int",
    " y: Int",
    " (= x (* 2 y))",
    "|----",
    " (=> (= x 0) (= x y))"]

result_train_m0_tr_po :: String
result_train_m0_tr_po = unlines 
    [ -- " sort: , , , pfun [a,b], set [a]"
      " sort: Pair [a,b], , , "
    , " st: (Array Int Bool)"
    , " st@prime: (Array Int Bool)"
    , " t: Int"
    , " (forall ((t Int)) (=> true (= (store st t false) (store st t false))))"
    , "|----"
    , " (exists ((t@param Int))"
          ++   " (and true"
          ++   " (and (=> (select st t) (select st t@param))"
          ++        " (=> (and (select st t)"
          ++                 " (= st@prime (store st t@param false))"
          ++                 " (select st t@param))"
          ++            " (not (select st@prime t))))))"
    ]

test_case :: ([Char], IO Bool, Bool)
test_case = ("Unit-B", test, True)

check_mch :: Either [Error] Machine -> IO String
check_mch em = do
    case em of
        Right m -> do
            (xs,_,_) <- str_verify_machine m
            return xs
        Left x -> return (show_err x)

get_cmd_tr_po :: Monad m 
              => Either [Error] Machine 
              -> m (Either [Error] String)
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
        pos <- proof_obligation m
        let lbl = composite_label [_name m, label "leave/TR/TR0"]
            po = pos ! lbl
        return $ show po) of
            Right xs -> return xs
            Left xs  -> return $ show_err xs

case3 :: IO [([Var], [Expr])]
result3 :: [([Var], [Expr])]
case4 :: IO ([(Int, Int)], [(Var, Int)], [(Expr, Int)])
result4 :: ([(Int, Int)], [(Var, Int)], [(Expr, Int)])
(case3, result3, case4, result4) = fromJust $ do
			e0 <- a
			e1 <- d `mzplus` b
			e2 <- b `mzplus` c
			e3 <- c `mzplus` d
			let arg0 = [a_decl,b_decl,c_decl,d_decl] 
			let arg1 = [e0,e1,e2,e3]
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
		(a,a_decl) = var "a" int
		(b,b_decl) = var "b" int
		(c,c_decl) = var "c" int
		(d,d_decl) = var "d" int
		f (xs,ys) = (sort xs, sort ys)
