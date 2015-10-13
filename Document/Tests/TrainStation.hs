{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TemplateHaskell    #-}
module Document.Tests.TrainStation where

    -- Modules
import Document.Tests.Suite -- (verify,find_errors,proof_obligation)

import Logic.Expr
import Logic.Proof
import Logic.Theory

import UnitB.AST
import qualified UnitB.Expr as UBExpr

import Theories.SetTheory
import Theories.FunctionTheory
import Theories.Arithmetic


    -- Libraries
import Control.Applicative
import Control.Arrow
import Control.Monad.State

import qualified Data.List as L -- ( intercalate, filter )
import           Data.Map hiding ( map )
import qualified Data.Set as S

import Tests.UnitTest
import Test.QuickCheck hiding (label)

import Utilities.Format
import Utilities.Syntactic

brackets :: String -> (Int,Int)
brackets ln = execState 
        (forM_ ln $ \c -> do
            (cl,op) <- get
            if c == '(' then
                put (cl,op+1)
            else if c == ')' then
                if op == 0 
                    then put (cl+1,op)
                    else put (cl,op-1)
            else return ()
        ) (0,0)

combine :: (Int,Int) -> (Int,Int) -> (Int,Int)
combine (o0,c0) (o1,c1) 
    | c0 <= o1  = (o0 + o1 - c0, c1)
    | otherwise = (o0, c1 + c0 - o1)

groupBrack :: [String] -> [String]
groupBrack [] = []
groupBrack [x] = [x]
groupBrack (x0:x1:xs)
        | op == 0    = x0 : groupBrack (x1:xs)
        | otherwise = groupBrack $ (x0 ++ "\n" ++ x1) : xs
    where
        (_,op) = brackets x0

prop_brackets :: BrackString -> BrackString -> Bool
prop_brackets (BrackString xs) (BrackString ys) = combine (brackets xs) (brackets ys) == brackets (xs ++ ys)

prop_open_brack :: Bool
prop_open_brack = brackets ")" == (1,0)

prop_close_brack :: Bool
prop_close_brack = brackets "(" == (0,1)

prop_open_close :: Bool
prop_open_close = brackets ")(" == (1,1)

prop_close_open :: Bool
prop_close_open = brackets "()" == (0,0)

prop_close_close :: Bool
prop_close_close = brackets "))" == (2,0)

prop_open_open :: Bool
prop_open_open = brackets "((" == (0,2)

data BrackString = BrackString String

instance Show BrackString where
    show (BrackString xs) = show xs

instance Arbitrary BrackString where
    arbitrary = do
        liftM BrackString $ listOf $ elements "(x)"

return []

runSpec :: IO Bool
runSpec = $forAllProperties (quickCheckWithResult stdArgs { chatty = False })

test_case :: TestCase
test_case = test

test :: TestCase
test = test_cases
            "train station example"
            [ part0
            , part1
            , part2
            , part3
            , part4
            , part5
            ]
part0 :: TestCase
part0 = test_cases
            "part 0"
            [ (Case "test 0, syntax" case0 $ Right [machine0])
            , (StringCase "test 21, multiple imports of sets" case21 result21)
            ]
part1 :: TestCase
part1 = test_cases
            "part 1"
            [ (POCase "test 1, verification" case1 result1)
            , (StringCase "test 2, proof obligation, INIT/fis, in" case2 result2)
            , (StringCase "test 20, proof obligation, INIT/fis, loc" case20 result20)
            , (StringCase "test 3, proof obligation, leave/fis, in'" case3 result3)
            , (StringCase "test 19, proof obligation, leave/fis, loc'" case19 result19)
            , (StringCase "test 4, proof obligation, leave/sch" case4 result4)
            , (Case "test 19, quickcheck brackets" runSpec True)
            ]
part2 :: TestCase
part2 = test_cases
            "part 2"
            [ (StringCase "test 5, proof obligation, leave/en/tr0/WFIS" case5 result5)
            , (StringCase "test 23, proof obligation, leave/en/tr0/EN" case23 result23)
            , (StringCase "test 24, proof obligation, leave/en/tr0/NEG" case24 result24)
            , (Case "test 7, undeclared symbol" case7 result7)
            , (Case "test 8, undeclared event (wrt transient)" case8 result8)
            , (Case "test 9, undeclared event (wrt c sched)" case9 result9)
            ]
part3 :: TestCase
part3 = test_cases
            "part 3"
            [ (Case "test 10, undeclared event (wrt indices)" case10 result10)
            , (Case "test 11, undeclared event (wrt assignment)" case11 result11)
            , (StringCase "test 12, proof obligation leave/INV/inv2" case12 result12)
            ]
part4 :: TestCase
part4 = test_cases
            "part 4"
            [ (StringCase "test 13, verification, name clash between dummy and index" case13 result13)
            , (POCase "test 14, verification, non-exhaustive case analysis" case14 result14)
            , (POCase "test 15, verification, incorrect new assumption" case15 result15)
            ]

part5 :: TestCase
part5 = test_cases
            "part 5"
            [ (POCase "test 16, verification, proof by parts" case16 result16)
            , (StringCase "test 17, ill-defined types" case17 result17)
            , (StringCase "test 18, assertions have type bool" case18 result18)
            , (StringCase "test 22, missing witness" case22 result22)
            ]

train_sort :: Sort
train_sort = Sort "\\TRAIN" "sl@TRAIN" 0
train_type :: Type
train_type = Gen train_sort []

loc_sort :: Sort
loc_sort = Sort "\\LOC" "sl@LOC" 0
loc_type :: Type
loc_type = Gen loc_sort []

blk_sort :: Sort
blk_sort = Sort "\\BLK" "sl@BLK" 0
blk_type :: Type
blk_type = Gen blk_sort []

universe :: Type -> Expr
train_def :: Def
loc_def :: Def
block_def :: Def

universe t = (zlift (set_type t) ztrue)
train_def = Def [] "sl@TRAIN" [] (set_type train_type) (universe train_type)
loc_def = Def [] "sl@LOC" [] (set_type loc_type) (universe loc_type)
block_def = Def [] "sl@BLK" [] (set_type blk_type) (universe blk_type)

train    :: ExprP
loc_cons :: ExprP
ent      :: ExprP
ext      :: ExprP
plf      :: ExprP
train_var :: Var
loc_var   :: Var
ent_var   :: Var
ext_var   :: Var
plf_var   :: Var

(train,train_var) = (var "sl@TRAIN" $ set_type train_type)
(loc_cons,loc_var)   = (var "sl@LOC" $ set_type loc_type)
(ent,ent_var)   = (var "ent" $ blk_type)
(ext,ext_var)   = (var "ext" $ blk_type)
(plf,plf_var)   = (var "PLF" $ set_type blk_type)

block :: ExprP
block_var :: Var
(block, block_var) = var "sl@BLK" $ set_type blk_type

machine0 :: Machine
machine0 = UBExpr.DispExpr "" <$> (empty_machine "train0") 
    {  _theory = empty_theory 
            {  _extends = fromList
                    [  ("functions", function_theory) -- train_type blk_type
                    ,  ("sets", set_theory) -- blk_type
                    ,  ("basic", basic_theory)
                    ,  ("arithmetic", arithmetic)
                    ]
            ,  _defs = fromList 
                    [  ("\\TRAIN", train_def)
                    ,  ("\\LOC", loc_def)
                    ,  ("\\BLK", block_def) ]
            ,  _types   = symbol_table 
                    [ train_sort
                    , loc_sort
                    , blk_sort
                    ]
            ,  _theoryDummies = symbol_table 
                            $ (map (\t -> Var t $ train_type) 
                                [ "t","t_0","t_1","t_2","t_3" ]
                               ++ map (\t -> Var t $ blk_type) 
                                [ "p","q" ])
            ,  _fact   = fromList 
                    [ ("axm0", axm0)
                    , ("asm2", axm2)
                    , ("asm3", axm3) 
                    , ("asm4", axm4) 
                    , ("asm5", axm5) 
                    ]
            ,  _consts  = fromList
                    [  ("ent", ent_var)
                    ,  ("ext", ext_var)
                    ,  ("PLF", plf_var)
                    ]
            }
    ,  _inits = fromList $ zip (map (label . ("in" ++) . show . (1 -)) [0..])
            $ map ($typeCheck) [loc .= zempty_fun, in_var .= zempty_set]
    ,  _variables = symbol_table [in_decl,loc_decl]
    ,  _event_table = newEvents [("enter", enter_evt), ("leave", leave_evt)]
    ,  _props = props0
    ,  _derivation = fromList []
    }
    where
        axm0 = ($typeCheck) (block .= (zset_enum [ent,ext] `zunion` plf)) 
        axm2 = ($typeCheck) (
               mznot (ent .= ext)
            /\ mznot (ent `zelem` plf)
            /\ mznot (ext `zelem` plf) )
        axm3 = ($typeCheck) $
            mzforall [p_decl] mztrue $ (
                        mznot (p .= ext)
                    .=  (p `zelem` (zmk_set ent `zunion` plf)))
        axm4 = ($typeCheck) $
            mzforall [p_decl] mztrue $ (
                        mznot (p .= ent)
                    .=  (p `zelem` (zmk_set ext `zunion` plf)))
        axm5 = ($typeCheck) $
            mzforall [p_decl] mztrue $ (
                        (mzeq p ent \/ mzeq p ext)
                    .=  mznot (p `zelem` plf) )

props0 :: PropertySet' Expr
props0 = empty_property_set
    {  _constraint = fromList 
            [   ( "co0"
                , Co [t_decl] 
                    $ ($typeCheck) (mzimplies 
                        (mzand (mznot (t `zelem` in_var)) (t `zelem` in_var')) 
                        (mzeq  (zapply loc' t) ent)) )
            ,   ( "co1"
                , Co [t_decl] 
                    $ ($typeCheck) (mzimplies 
                        (mzall [ (t `zelem` in_var), 
                                 (zapply loc t .= ent), 
                                 mznot (zapply loc t `zelem` plf)])
                        (mzand (t `zelem` in_var')
                               ((zapply loc' t `zelem` plf) \/ ((loc' `zapply` t) 
                               .= ent)))) )
            ]
    ,   _transient = fromList
            [   ( "tr0"
                , Tr
                    (symbol_table [t_decl])
                    (($typeCheck) (t `zelem` in_var)) ["leave"] 
                    (TrHint (fromList [("t",(train_type, $typeCheck $ t' .= t))]) Nothing) )
            ]
    ,  _inv = fromList 
            [   ("inv2",($typeCheck) (zdom loc .= in_var))
            ,   ("inv1",($typeCheck) $ mzforall [t_decl] (zelem t in_var)
                        ((zapply loc t `zelem` block)))
            ]
    ,  _proofs = fromList
            [   ( "train0/enter/INV/inv2"
                , ByCalc $ Calc empty_ctx ztrue ztrue [] li)
            ,   ( "train0/leave/INV/inv2"
                , ByCalc $ Calc empty_ctx ztrue ztrue [] li)
            ,   ( "train0/INIT/INV/inv2"
                , ByCalc $ Calc empty_ctx ztrue ztrue [] li)
            ,   ( "train0/enter/CO/co0"
                , ByCalc $ Calc empty_ctx ztrue ztrue [] li)
            ,   ( "train0/enter/CO/co1"
                , ByCalc $ Calc empty_ctx ztrue ztrue [] li)
            ,   ( "train0/leave/CO/co0"
                , ByCalc $ Calc empty_ctx ztrue ztrue [] li)
            ,   ( "train0/leave/CO/co1"
                , ByCalc $ Calc empty_ctx ztrue ztrue [] li)
            ]
    ,  _safety = fromList
            []
    }
    where 
        li = LI "" 0 0

enter_evt :: Event' Expr
enter_evt = empty_event
    {  _indices = symbol_table [t_decl]
    ,  _guards  = fromList
            [  ("grd1", ($typeCheck) $ mznot (t `zelem` in_var))
            ]
    ,  _actions = fromList
            [  ("a1", BcmSuchThat vars
                    (($typeCheck) (in_var' .= (in_var `zunion` zmk_set t))))
            ,  ("a2", BcmSuchThat vars
                    (($typeCheck) (loc' .= (loc `zovl` zmk_fun t ent))))
            ]
    }
    where 
        vars = S.elems $ variableSet machine0

leave_evt :: Event' Expr
leave_evt = empty_event 
    {  _indices   = symbol_table [t_decl]
    ,  _coarse_sched = singleton "c0" (($typeCheck) (t `zelem` in_var))
    ,  _guards = fromList
            [  ("grd0", ($typeCheck) $  
                                       zapply loc t .= ext
                                    /\ (t `zelem` in_var) )
            ]
    ,  _actions = fromList 
            [  ("a0", BcmSuchThat vars
                    (($typeCheck) (in_var' .= (in_var `zsetdiff` zmk_set t))))
            ,  ("a3", BcmSuchThat vars
                    (($typeCheck) (loc' .= (zmk_set t `zdomsubt` loc))))
            ] 
    }
    where
        vars = S.elems $ variableSet machine0

p        :: ExprP
p_decl   :: Var
t'       :: ExprP
t        :: ExprP
t_decl   :: Var
in_var   :: ExprP
in_var'  :: ExprP
in_decl  :: Var
loc      :: ExprP
loc'     :: ExprP
loc_decl :: Var

(p, p_decl) = var "p" blk_type
(t, t_decl) = var "t" train_type
(t', _) = var "t@prime" train_type
(in_var, in_var', in_decl) = prog_var "in" (set_type train_type)
(loc, loc', loc_decl) = prog_var "loc" (fun_type train_type blk_type)

check_sat :: [String]    
check_sat = [ "(check-sat-using (or-else (then qe smt)"
            , "                          (then simplify smt)"
            , "                          (then skip smt)"
            , "                          (then (using-params simplify :expand-power true) smt)))"
            ]


train_decl :: Bool -> Bool -> [String]
train_decl b ind = 
        [ "(declare-datatypes (a) ( (Maybe (Just (fromJust a)) Nothing) ))"
        , "(declare-datatypes () ( (Null null) ))"
        , "(declare-datatypes (a b) ( (Pair (pair (first a) (second b))) ))"
        , "(declare-sort sl@BLK 0)"
        , "; comment: we don't need to declare the sort Bool"
        , "; comment: we don't need to declare the sort Int"
        , "(declare-sort sl@LOC 0)"
        , "; comment: we don't need to declare the sort Real"
        , "(declare-sort sl@TRAIN 0)"
        , "(define-sort pfun (a b) (Array a (Maybe b)))"
        , "(define-sort set (a) (Array a Bool))"
        , "(declare-const PLF (set sl@BLK))"
        , "(declare-const ent sl@BLK)"
        , "(declare-const ext sl@BLK)"
        ] ++ var_decl ++
        if ind then
        [
--        [ "(declare-const p sl@BLK)"
--        , "(declare-const q sl@BLK)"
        "(declare-const t sl@TRAIN)"
--        , "(declare-const t_0 sl@TRAIN)"
--        , "(declare-const t_1 sl@TRAIN)"
--        , "(declare-const t_2 sl@TRAIN)"
--        , "(declare-const t_3 sl@TRAIN)"
        ] 
        else []
    where
        var_decl
            | b         =
                [  "(declare-const in (set sl@TRAIN))"
                ,  "(declare-const in@prime (set sl@TRAIN))"
                ,  "(declare-const loc (pfun sl@TRAIN sl@BLK))"
                ,  "(declare-const loc@prime (pfun sl@TRAIN sl@BLK))"
                ]
            | otherwise = 
                [  "(declare-const in (set sl@TRAIN))"
                ,  "(declare-const loc (pfun sl@TRAIN sl@BLK))"
                ]

set_decl_smt2 :: [AxiomOption] -> [String]
set_decl_smt2 xs = 
        when (WithPFun `elem` xs)
        [ "(declare-fun apply@@sl@TRAIN@@sl@BLK"
        , "             ( (pfun sl@TRAIN sl@BLK)"
        , "               sl@TRAIN )"
        , "             sl@BLK)"]
--        ,  "(declare-fun bunion@Open@@pfun@@sl@TRAIN@@sl@BLK@Close ((set (pfun sl@TRAIN sl@BLK)) (set (pfun sl@TRAIN sl@BLK))) (set (pfun sl@TRAIN sl@BLK)))"
     ++ when (WithPFun `elem` xs)
        [  "(declare-fun dom-rest@@sl@TRAIN@@sl@BLK"
        ,  "             ( (set sl@TRAIN)"
        ,  "               (pfun sl@TRAIN sl@BLK) )"
        ,  "             (pfun sl@TRAIN sl@BLK))"
        ,  "(declare-fun dom-subt@@sl@TRAIN@@sl@BLK"
        ,  "             ( (set sl@TRAIN)"
        ,  "               (pfun sl@TRAIN sl@BLK) )"
        ,  "             (pfun sl@TRAIN sl@BLK))"
        ,  "(declare-fun dom@@sl@TRAIN@@sl@BLK"
        ,  "             ( (pfun sl@TRAIN sl@BLK) )"
        ,  "             (set sl@TRAIN))"]
--        ,  "(declare-fun elem@Open@@pfun@@sl@TRAIN@@sl@BLK@Close ((pfun sl@TRAIN sl@BLK) (set (pfun sl@TRAIN sl@BLK))) Bool)"
     ++ when (WithPFun `elem` xs)
        [  "(declare-fun empty-fun@@sl@TRAIN@@sl@BLK"
        ,  "             ()"
        ,  "             (pfun sl@TRAIN sl@BLK))"]
--        ,  "(declare-fun empty-set@Open@@pfun@@sl@TRAIN@@sl@BLK@Close () (set (pfun sl@TRAIN sl@BLK)))"
     ++ [ "(declare-fun finite@@sl@BLK ( (set sl@BLK) ) Bool)" 
        , "(declare-fun finite@@sl@LOC ( (set sl@LOC) ) Bool)" 
        , "(declare-fun finite@@sl@TRAIN ( (set sl@TRAIN) ) Bool)" ]
     ++ when (WithPFun `elem` xs)
        [  "(declare-fun injective@@sl@TRAIN@@sl@BLK"
        ,  "             ( (pfun sl@TRAIN sl@BLK) )"
        ,  "             Bool)" ]
--        ,  "(declare-fun intersect@Open@@pfun@@sl@TRAIN@@sl@BLK@Close ((set (pfun sl@TRAIN sl@BLK)) (set (pfun sl@TRAIN sl@BLK))) (set (pfun sl@TRAIN sl@BLK)))"
     ++ when (WithPFun `elem` xs)
        [  "(declare-fun mk-fun@@sl@TRAIN@@sl@BLK"
        ,  "             (sl@TRAIN sl@BLK)"
        ,  "             (pfun sl@TRAIN sl@BLK))"]
     ++ [  "(declare-fun mk-set@@sl@BLK (sl@BLK) (set sl@BLK))" 
        ,  "(declare-fun mk-set@@sl@TRAIN (sl@TRAIN) (set sl@TRAIN))"
        ]
--        ,  "(declare-fun mk-set@Open@@pfun@@sl@TRAIN@@sl@BLK@Close ((pfun sl@TRAIN sl@BLK)) (set (pfun sl@TRAIN sl@BLK)))"
     ++ when (WithPFun `elem` xs)
        [ "(declare-fun ovl@@sl@TRAIN@@sl@BLK"
        , "             ( (pfun sl@TRAIN sl@BLK)"
        , "               (pfun sl@TRAIN sl@BLK) )"
        , "             (pfun sl@TRAIN sl@BLK))"
        , "(declare-fun ran@@sl@TRAIN@@sl@BLK"
        , "             ( (pfun sl@TRAIN sl@BLK) )"
        , "             (set sl@BLK))"
        ]
--        ,  "(declare-fun set-diff@Open@@pfun@@sl@TRAIN@@sl@BLK@Close ((set (pfun sl@TRAIN sl@BLK)) (set (pfun sl@TRAIN sl@BLK))) (set (pfun sl@TRAIN sl@BLK)))"
     ++ [ "(define-fun all@@sl@BLK"
        , "            ()"
        , "            (set sl@BLK)"
        , "            ( (as const (set sl@BLK))"
        , "              true ))"
        , "(define-fun all@@sl@LOC"
        , "            ()"
        , "            (set sl@LOC)"
        , "            ( (as const (set sl@LOC))"
        , "              true ))"
        , "(define-fun all@@sl@TRAIN"
        , "            ()"
        , "            (set sl@TRAIN)"
        , "            ( (as const (set sl@TRAIN))"
        , "              true ))"
        , "(define-fun compl@@sl@BLK"
        , "            ( (s1 (set sl@BLK)) )"
        , "            (set sl@BLK)"
        , "            ( (_ map not)"
        , "              s1 ))"
        , "(define-fun compl@@sl@LOC"
        , "            ( (s1 (set sl@LOC)) )"
        , "            (set sl@LOC)"
        , "            ( (_ map not)"
        , "              s1 ))"
        , "(define-fun compl@@sl@TRAIN"
        , "            ( (s1 (set sl@TRAIN)) )"
        , "            (set sl@TRAIN)"
        , "            ( (_ map not)"
        , "              s1 ))"
        , "(define-fun elem@@sl@BLK"
        , "            ( (x sl@BLK)"
        , "              (s1 (set sl@BLK)) )"
        , "            Bool"
        , "            (select s1 x))"
        , "(define-fun elem@@sl@TRAIN"
        , "            ( (x sl@TRAIN)"
        , "              (s1 (set sl@TRAIN)) )"
        , "            Bool"
        , "            (select s1 x))"
        ] ++
        -- when (WithPFun `elem` xs) 
        -- [ "(declare-fun empty-fun@@sl@TRAIN@@sl@BLK"
        -- , "            ()"
        -- , "            (pfun sl@TRAIN sl@BLK)"
        -- , "            ( (as const (pfun sl@TRAIN sl@BLK))"
        -- , "              (as Nothing (Maybe sl@BLK)) ))"
        -- ] ++ 
        [ "(define-fun empty-set@@sl@BLK"
        , "            ()"
        , "            (set sl@BLK)"
        , "            ( (as const (set sl@BLK))"
        , "              false ))"
        , "(define-fun empty-set@@sl@LOC"
        , "            ()"
        , "            (set sl@LOC)"
        , "            ( (as const (set sl@LOC))"
        , "              false ))"
        , "(define-fun empty-set@@sl@TRAIN"
        , "            ()"
        , "            (set sl@TRAIN)"
        , "            ( (as const (set sl@TRAIN))"
        , "              false ))"
        , "(define-fun set-diff@@sl@BLK"
        , "            ( (s1 (set sl@BLK))"
        , "              (s2 (set sl@BLK)) )"
        , "            (set sl@BLK)"
        , "            (intersect s1 ( (_ map not) s2 )))"
        , "(define-fun set-diff@@sl@LOC"
        , "            ( (s1 (set sl@LOC))"
        , "              (s2 (set sl@LOC)) )"
        , "            (set sl@LOC)"
        , "            (intersect s1 ( (_ map not) s2 )))"
        , "(define-fun set-diff@@sl@TRAIN"
        , "            ( (s1 (set sl@TRAIN))"
        , "              (s2 (set sl@TRAIN)) )"
        , "            (set sl@TRAIN)"
        , "            (intersect s1 ( (_ map not) s2 )))"
        , "(define-fun sl@BLK"
        , "            ()"
        , "            (set sl@BLK)"
        , "            ( (as const (set sl@BLK))"
        , "              true ))"
        , "(define-fun sl@LOC"
        , "            ()"
        , "            (set sl@LOC)"
        , "            ( (as const (set sl@LOC))"
        , "              true ))"
        , "(define-fun sl@TRAIN"
        , "            ()"
        , "            (set sl@TRAIN)"
        , "            ( (as const (set sl@TRAIN))"
        , "              true ))"
        , "(define-fun st-subset@@sl@BLK"
        , "            ( (s1 (set sl@BLK))"
        , "              (s2 (set sl@BLK)) )"
        , "            Bool"
        , "            (and (subset s1 s2) (not (= s1 s2))))"
        , "(define-fun st-subset@@sl@LOC"
        , "            ( (s1 (set sl@LOC))"
        , "              (s2 (set sl@LOC)) )"
        , "            Bool"
        , "            (and (subset s1 s2) (not (= s1 s2))))"
        , "(define-fun st-subset@@sl@TRAIN"
        , "            ( (s1 (set sl@TRAIN))"
        , "              (s2 (set sl@TRAIN)) )"
        , "            Bool"
        , "            (and (subset s1 s2) (not (= s1 s2))))"
        ]
--        ,  "(declare-fun subset@Open@@pfun@@sl@TRAIN@@sl@BLK@Close ((set (pfun sl@TRAIN sl@BLK)) (set (pfun sl@TRAIN sl@BLK))) Bool)"
--     ++ when (WithPFun `elem` xs)
--        [  "(declare-fun tfun@@sl@TRAIN@@sl@BLK ((set sl@TRAIN) (set sl@BLK)) (set (pfun sl@TRAIN sl@BLK)))"]
    where
        when b xs = if b then xs else []

splitAll :: (String -> Bool) -> [String] -> [String]
splitAll p (x0:x1:xs) 
    | p x1      = x0 : splitAll p (x1:xs)
    | otherwise = splitAll p ( (x0++"\n"++x1) : xs )
splitAll _ xs = xs

set_facts :: [String] -> [(String,String)]
set_facts xs = concat $ L.transpose [ foo [x] ys | x <- xs ]
  where
    ys =
        [ "(assert (forall ( (x {0})"
        , "                  (y {0}) )"
        , "                (! (= (elem@{1} x (mk-set@{1} y)) (= x y))"
        , "                   :pattern"
        , "                   ( (elem@{1} x (mk-set@{1} y)) ))))"
        , "(assert (forall ( (s1 (set {0}))"
        , "                  (s2 (set {0})) )"
        , "                (! (=> (finite@{1} s1)"
        , "                       (finite@{1} (set-diff@{1} s1 s2)))"
        , "                   :pattern"
        , "                   ( (finite@{1} (set-diff@{1} s1 s2)) ))))"
        , "(assert (forall ( (s1 (set {0}))"
        , "                  (s2 (set {0})) )"
        , "                (! (=> (and (finite@{1} s1) (finite@{1} s2))"
        , "                       (finite@{1} (union s1 s2)))"
        , "                   :pattern"
        , "                   ( (finite@{1} (union s1 s2)) ))))"
        , "(assert (forall ( (x {0}) )"
        , "                (! (finite@{1} (mk-set@{1} x))"
        , "                   :pattern"
        , "                   ( (finite@{1} (mk-set@{1} x)) ))))" 
        , "(assert (finite@{1} empty-set@{1}))"
        , "(assert (forall ( (s1 (set {0}))"
        , "                  (s2 (set {0})) )"
        , "                (! (=> (subset s1 s2)"
        , "                       (=> (finite@{1} s2) (finite@{1} s1)))"
        , "                   :pattern"
        , "                   ( (finite@{1} s2)"
        , "                     (finite@{1} s1) ))))"
        ]

foo :: [String] -> [String] -> [(String,String)]
foo xs' stmts = [ (x, substAll y ys) | (x,y) <- zip tag $ splitAll p stmts ]
    where
        xs = map (id &&& ('@':)) xs'
        p = not . L.isPrefixOf " "
        pad x = replicate (length x) ' '
        ys = concat $ L.transpose [ [x,y,pad y] | (x,y) <- xs ]
        tag = [ format "{0}{1}" (concatMap snd xs) k | k <- [0..] ]

fun_facts :: [(String, String)] -> [(String,String)]
fun_facts xs = concat $ L.transpose [ foo [x,y] ys | (x,y) <- xs ]
    where
        ys = 
            [ "(assert (= (dom@{2}@{3} empty-fun@{2}@{3})"
            , "           empty-set@{2}))"
            , "(assert (forall ( (f1 (pfun {0} {1})) )"
            , "                (! (= (ovl@{2}@{3} f1 empty-fun@{2}@{3})"
            , "                      f1)"
            , "                   :pattern"
            , "                   ( (ovl@{2}@{3} f1 empty-fun@{2}@{3}) ))))"
            , "(assert (forall ( (f1 (pfun {0} {1})) )"
            , "                (! (= (ovl@{2}@{3} empty-fun@{2}@{3} f1)"
            , "                      f1)"
            , "                   :pattern"
            , "                   ( (ovl@{2}@{3} empty-fun@{2}@{3} f1) ))))"
            , "(assert (forall ( (x {0})"
            , "                  (y {1}) )"
            , "                (! (= (dom@{2}@{3} (mk-fun@{2}@{3} x y))"
            , "                      (mk-set@{2} x))"
            , "                   :pattern"
            , "                   ( (dom@{2}@{3} (mk-fun@{2}@{3} x y)) ))))"
            , "(assert (forall ( (f1 (pfun {0} {1}))"
            , "                  (f2 (pfun {0} {1}))"
            , "                  (x {0}) )"
            , "                (! (=> (elem@{2} x (dom@{2}@{3} f2))"
            , "                       (= (apply@{2}@{3} (ovl@{2}@{3} f1 f2) x)"
            , "                          (apply@{2}@{3} f2 x)))"
            , "                   :pattern"
            , "                   ( (apply@{2}@{3} (ovl@{2}@{3} f1 f2) x) ))))"
            , "(assert (forall ( (f1 (pfun {0} {1}))"
            , "                  (f2 (pfun {0} {1}))"
            , "                  (x {0}) )"
            , "                (! (=> (and (elem@{2} x (dom@{2}@{3} f1))"
            , "                            (not (elem@{2} x (dom@{2}@{3} f2))))"
            , "                       (= (apply@{2}@{3} (ovl@{2}@{3} f1 f2) x)"
            , "                          (apply@{2}@{3} f1 x)))"
            , "                   :pattern"
            , "                   ( (apply@{2}@{3} (ovl@{2}@{3} f1 f2) x) ))))"
            , "(assert (forall ( (x {0})"
            , "                  (y {1}) )"
            , "                (! (= (apply@{2}@{3} (mk-fun@{2}@{3} x y) x)"
            , "                      y)"
            , "                   :pattern"
            , "                   ( (apply@{2}@{3} (mk-fun@{2}@{3} x y) x) ))))"
            , "(assert (forall ( (f1 (pfun {0} {1}))"
            , "                  (s1 (set {0}))"
            , "                  (x {0}) )"
            , "                (! (=> (and (elem@{2} x s1)"
            , "                            (elem@{2} x (dom@{2}@{3} f1)))"
            , "                       (= (apply@{2}@{3} (dom-rest@{2}@{3} s1 f1) x)"
            , "                          (apply@{2}@{3} f1 x)))"
            , "                   :pattern"
            , "                   ( (apply@{2}@{3} (dom-rest@{2}@{3} s1 f1) x) ))))"
            , "(assert (forall ( (f1 (pfun {0} {1}))"
            , "                  (s1 (set {0}))"
            , "                  (x {0}) )"
            , "                (! (=> (elem@{2} x"
            , "                             {4} (set-diff@{2} (dom@{2}@{3} f1) s1))"
            , "                       (= (apply@{2}@{3} (dom-subt@{2}@{3} s1 f1) x)"
            , "                          (apply@{2}@{3} f1 x)))"
            , "                   :pattern"
            , "                   ( (apply@{2}@{3} (dom-subt@{2}@{3} s1 f1) x) ))))"
            , "(assert (forall ( (f1 (pfun {0} {1}))"
            , "                  (f2 (pfun {0} {1})) )"
            , "                (! (= (dom@{2}@{3} (ovl@{2}@{3} f1 f2))"
            , "                      (union (dom@{2}@{3} f1)"
            , "                             (dom@{2}@{3} f2)))"
            , "                   :pattern"
            , "                   ( (dom@{2}@{3} (ovl@{2}@{3} f1 f2)) ))))"
            , "(assert (forall ( (f1 (pfun {0} {1}))"
            , "                  (s1 (set {0})) )"
            , "                (! (= (dom@{2}@{3} (dom-rest@{2}@{3} s1 f1))"
            , "                      (intersect s1 (dom@{2}@{3} f1)))"
            , "                   :pattern"
            , "                   ( (dom@{2}@{3} (dom-rest@{2}@{3} s1 f1)) ))))"
            , "(assert (forall ( (f1 (pfun {0} {1}))"
            , "                  (s1 (set {0})) )"
            , "                (! (= (dom@{2}@{3} (dom-subt@{2}@{3} s1 f1))"
            , "                      (set-diff@{2} (dom@{2}@{3} f1) s1))"
            , "                   :pattern"
            , "                   ( (dom@{2}@{3} (dom-subt@{2}@{3} s1 f1)) ))))"
            , "(assert (forall ( (f1 (pfun {0} {1}))"
            , "                  (x {0})"
            , "                  (y {1}) )"
            , "                (! (= (and (elem@{2} x (dom@{2}@{3} f1))"
            , "                           (= (apply@{2}@{3} f1 x) y))"
            , "                      (= (select f1 x) (Just y)))"
            , "                   :pattern"
            , "                   ( (elem@@sl@TRAIN x (dom@@sl@TRAIN@@sl@BLK f1))"
            , "                     (apply@@sl@TRAIN@@sl@BLK f1 x)"
            , "                     (select f1 x)"
            , "                     (Just y) ))))"
            , "(assert (forall ( (f1 (pfun {0} {1}))"
            , "                  (x {0})"
            , "                  (x2 {0})"
            , "                  (y {1}) )"
            , "                (! (=> (not (= x x2))"
            , "                       (= (apply@{2}@{3} (ovl@{2}@{3} f1 (mk-fun@{2}@{3} x y))"
            , "                                 {4} {5} x2)"
            , "                          (apply@{2}@{3} f1 x2)))"
            , "                   :pattern"
            , "                   ( (apply@{2}@{3} (ovl@{2}@{3} f1 (mk-fun@{2}@{3} x y))"
            , "                            {4} {5} x2) ))))"
            , "(assert (forall ( (f1 (pfun {0} {1}))"
            , "                  (x {0})"
            , "                  (y {1}) )"
            , "                (! (= (apply@{2}@{3} (ovl@{2}@{3} f1 (mk-fun@{2}@{3} x y))"
            , "                             {4} {5} x)"
            , "                      y)"
            , "                   :pattern"
            , "                   ( (apply@{2}@{3} (ovl@{2}@{3} f1 (mk-fun@{2}@{3} x y))"
            , "                            {4} {5} x) ))))"
            , "(assert (= (ran@{2}@{3} empty-fun@{2}@{3})"
            , "           empty-set@{3}))"
            , "(assert (forall ( (f1 (pfun {0} {1}))"
            , "                  (y {1}) )"
            , "                (! (= (elem@{3} y (ran@{2}@{3} f1))"
            , "                      (exists ( (x {0}) )"
            , "                              (and true"
            , "                                   (and (elem@{2} x (dom@{2}@{3} f1))"
            , "                                        (= (apply@{2}@{3} f1 x) y)))))"
            , "                   :pattern"
            , "                   ( (elem@{3} y (ran@{2}@{3} f1)) ))))"
            -- , "(assert (forall ( (f1 (pfun {0} {1}))"
            -- , "                  (f2 (pfun {0} {1})) )"
            -- , "                (! (subset (ran@{2}@{3} (ovl@{2}@{3} f1 f2))"
            -- , "                           (union (ran@{2}@{3} f1)"
            -- , "                                  (ran@{2}@{3} f2)))"
            -- , "                   :pattern"
            -- , "                   ( (subset (ran@{2}@{3} (ovl@{2}@{3} f1 f2))"
            -- , "                             (union (ran@{2}@{3} f1)"
            -- , "                                    (ran@{2}@{3} f2))) ))))"
            , "(assert (forall ( (x {0})"
            , "                  (y {1}) )"
            , "                (! (= (ran@{2}@{3} (mk-fun@{2}@{3} x y))"
            , "                      (mk-set@{3} y))"
            , "                   :pattern"
            , "                   ( (ran@{2}@{3} (mk-fun@{2}@{3} x y)) ))))"
            , "(assert (forall ( (f1 (pfun {0} {1})) )"
            , "                (! (= (injective@{2}@{3} f1)"
            , "                      (forall ( (x {0})"
            , "                                (x2 {0}) )"
            , "                              (=> (and (elem@{2} x (dom@{2}@{3} f1))"
            , "                                       (elem@{2} x2 (dom@{2}@{3} f1)))"
            , "                                  (=> (= (apply@{2}@{3} f1 x)"
            , "                                         (apply@{2}@{3} f1 x2))"
            , "                                      (= x x2)))))"
            , "                   :pattern"
            , "                   ( (injective@{2}@{3} f1) ))))"
            -- , "(assert (forall ( (x {0}) )"
            -- , "                (! (= (select empty-fun@{2}@{3} x)"
            -- , "                      (as Nothing (Maybe {1})))"
            -- , "                   :pattern"
            -- , "                   ( (select empty-fun@{2}@{3} x) ))))"
            -- , "(assert (forall ( (x {0})"
            -- , "                  (x2 {0})"
            -- , "                  (y {1}) )"
            -- , "                (! (= (select (mk-fun@{2}@{3} x y) x2)"
            -- , "                      (ite (= x x2) (Just y) (as Nothing (Maybe {1}))))"
            -- , "                   :pattern"
            -- , "                   ( (select (mk-fun@{2}@{3} x y) x2) ))))"
            -- , "(assert (forall ( (x {0})"
            -- , "                  (f1 (pfun {0} {1}))"
            -- , "                  (f2 (pfun {0} {1})) )"
            -- , "                (! (= (select (ovl@{2}@{3} f1 f2) x)"
            -- , "                      (ite (= (select f2 x) (as Nothing (Maybe {1})))"
            -- , "                           (select f1 x)"
            -- , "                           (select f2 x)))"
            -- , "                   :pattern"
            -- , "                   ( (select (ovl@{2}@{3} f1 f2) x) ))))"
            -- , "(assert (forall ( (x {0})"
            -- , "                  (f1 (pfun {0} {1})) )"
            -- , "                (! (= (select (dom@{2}@{3} f1) x)"
            -- , "                      (not (= (select f1 x) (as Nothing (Maybe {1})))))"
            -- , "                   :pattern"
            -- , "                   ( (select (dom@{2}@{3} f1) x) ))))"
            -- , "(assert (forall ( (x {0})"
            -- , "                  (y {1})"
            -- , "                  (f1 (pfun {0} {1})) )"
            -- , "                (! (= (and (elem@{2} x (dom@{2}@{3} f1))"
            -- , "                           (= (apply@{2}@{3} f1 x) y))"
            -- , "                      (= (select f1 x) (Just y)))"
            -- , "                   :pattern"
            -- , "                   ())))"
            , "(assert (injective@{2}@{3} empty-fun@{2}@{3}))"
            -- , "(assert (forall ( (f1 (pfun {0} {1}))"
            -- , "                  (x {0}) )"
            -- , "                (! (=> (and (injective@{2}@{3} f1)"
            -- , "                            (elem@{2} x (dom@{2}@{3} f1)))"
            -- , "                       (= (ran@{2}@{3} (dom-subt@{2}@{3} (mk-set@{2} x) f1))"
            -- , "                          (set-diff@{3} (ran@{2}@{3} f1)"
            -- , "                                    {5} (mk-set@{3} (apply@{2}@{3} f1 x)))))"
            -- , "                   :pattern"
            -- , "                   ( (ran@{2}@{3} (dom-subt@{2}@{3} (mk-set@{2} x) f1)) ))))"
            -- , "(assert (forall ( (f1 (pfun {0} {1}))"
            -- , "                  (x {0})"
            -- , "                  (x2 {0}) )"
            -- , "                (! (=> (and (not (= x x2))"
            -- , "                            (elem@{2} x2 (dom@{2}@{3} f1)))"
            -- , "                       (= (apply@{2}@{3} (dom-subt@{2}@{3} (mk-set@{2} x) f1)"
            -- , "                                 {4} {5} x2)"
            -- , "                          (apply@{2}@{3} f1 x2)))"
            -- , "                   :pattern"
            -- , "                   ( (apply@{2}@{3} (dom-subt@{2}@{3} (mk-set@{2} x) f1)"
            -- , "                            {4} {5} x2) ))))"
            -- , "(assert (forall ( (f1 (pfun {0} {1}))"
            -- , "                  (x {0}) )"
            -- , "                (! (=> (elem@{2} x (dom@{2}@{3} f1))"
            -- , "                       (= (apply@{2}@{3} (dom-rest@{2}@{3} (mk-set@{2} x) f1)"
            -- , "                                 {4} {5} x)"
            -- , "                          (apply@{2}@{3} f1 x)))"
            -- , "                   :pattern"
            -- , "                   ( (apply@{2}@{3} (dom-rest@{2}@{3} (mk-set@{2} x) f1)"
            -- , "                            {4} {5} x) ))))"
            , "(assert (forall ( (f1 (pfun {0} {1}))"
            , "                  (x {0}) )"
            , "                (! (=> (elem@{2} x (dom@{2}@{3} f1))"
            , "                       (elem@{3} (apply@{2}@{3} f1 x)"
            , "                             {5} (ran@{2}@{3} f1)))"
            , "                   :pattern"
            , "                   ( (elem@{3} (apply@{2}@{3} f1 x)"
            , "                           {5} (ran@{2}@{3} f1)) ))))"
            , "(assert (forall ( (f1 (pfun {0} {1}))"
            , "                  (s1 (set {0}))"
            , "                  (x {0}) )"
            , "                (! (=> (elem@{2} x"
            , "                             {4} (set-diff@{2} (dom@{2}@{3} f1) s1))"
            , "                       (elem@{3} (apply@{2}@{3} f1 x)"
            , "                             {5} (ran@{2}@{3} (dom-subt@{2}@{3} s1 f1))))"
            , "                   :pattern"
            , "                   ( (elem@{3} (apply@{2}@{3} f1 x)"
            , "                           {5} (ran@{2}@{3} (dom-subt@{2}@{3} s1 f1))) ))))"
            , "(assert (forall ( (f1 (pfun {0} {1}))"
            , "                  (s1 (set {0}))"
            , "                  (x {0}) )"
            , "                (! (=> (elem@{2} x (intersect (dom@{2}@{3} f1) s1))"
            , "                       (elem@{3} (apply@{2}@{3} f1 x)"
            , "                             {5} (ran@{2}@{3} (dom-rest@{2}@{3} s1 f1))))"
            , "                   :pattern"
            , "                   ( (elem@{3} (apply@{2}@{3} f1 x)"
            , "                           {5} (ran@{2}@{3} (dom-rest@{2}@{3} s1 f1))) ))))"
            , "(assert (forall ( (f1 (pfun {0} {1}))"
            , "                  (x {0})"
            , "                  (y {1}) )"
            , "                (! (=> (and (elem@{2} x (dom@{2}@{3} f1))"
            , "                            (injective@{2}@{3} f1))"
            , "                       (= (ran@{2}@{3} (ovl@{2}@{3} f1 (mk-fun@{2}@{3} x y)))"
            , "                          (union (set-diff@{3} (ran@{2}@{3} f1)"
            , "                                           {5} (mk-set@{3} (apply@{2}@{3} f1 x)))"
            , "                                 (mk-set@{3} y))))"
            , "                   :pattern"
            , "                   ( (ran@{2}@{3} (ovl@{2}@{3} f1 (mk-fun@{2}@{3} x y))) ))))"
            , "(assert (forall ( (f1 (pfun {0} {1}))"
            , "                  (x {0})"
            , "                  (y {1}) )"
            , "                (! (=> (not (elem@{2} x (dom@{2}@{3} f1)))"
            , "                       (= (ran@{2}@{3} (ovl@{2}@{3} f1 (mk-fun@{2}@{3} x y)))"
            , "                          (union (ran@{2}@{3} f1) (mk-set@{3} y))))"
            , "                   :pattern"
            , "                   ( (ran@{2}@{3} (ovl@{2}@{3} f1 (mk-fun@{2}@{3} x y))) ))))"
            ] -- 27

data AxiomOption = WithPFun
    deriving Eq

comp_facts :: [AxiomOption] -> [String]
comp_facts xs = 
           ( map snd    (     (if (WithPFun `elem` xs) then
                               concatMap set_facts 
                                [ --  ("(pfun sl@TRAIN sl@BLK)", "Open@@pfun@@sl@TRAIN@@sl@BLK@Close")
                                ]
                            ++ fun_facts
                                [ ("sl@TRAIN","sl@BLK") ]
                               else [])
                            ++ set_facts 
                                [ "sl@BLK"
                                , "sl@LOC"
                                , "sl@TRAIN"
                                ] ) )
named_facts :: [String]
named_facts = []


path0 :: String
path0 = "Tests/train-station.tex"

case0 :: IO (Either [Error] [Machine])
case0 = parse path0

result1 :: String
result1 = unlines 
    [ "  o  train0/INIT/FIS/in"
    , "  o  train0/INIT/FIS/loc"
    , "  o  train0/INIT/INV/inv1"
    , "  o  train0/INIT/INV/inv2/goal"
    , "  o  train0/INIT/INV/inv2/hypotheses"
    , "  o  train0/INIT/INV/inv2/relation"
    , "  o  train0/INIT/INV/inv2/step 1"
    , "  o  train0/INIT/INV/inv2/step 2"
    , "  o  train0/INIT/INV/inv2/step 3"
    , "  o  train0/INIT/WD"
    , "  o  train0/INIT/WWD"
    , "  o  train0/INV/WD"
    , "  o  train0/SKIP/CO/co0"
    , "  o  train0/SKIP/CO/co1"
    , "  o  train0/TR/tr0/WFIS/t/t@prime"
    , "  o  train0/TR/tr0/leave/EN"
    , "  o  train0/TR/tr0/leave/NEG"
    , "  o  train0/co0/CO/WD"
    , "  o  train0/co1/CO/WD"
    , "  o  train0/enter/CO/co0/case 1/goal"
    , "  o  train0/enter/CO/co0/case 1/hypotheses"
    , "  o  train0/enter/CO/co0/case 1/relation"
    , "  o  train0/enter/CO/co0/case 1/step 1"
    , "  o  train0/enter/CO/co0/case 1/step 2"
    , "  o  train0/enter/CO/co0/case 2/goal"
    , "  o  train0/enter/CO/co0/case 2/hypotheses"
    , "  o  train0/enter/CO/co0/case 2/relation"
    , "  o  train0/enter/CO/co0/case 2/step 1"
    , "  o  train0/enter/CO/co0/case 2/step 2"
    , "  o  train0/enter/CO/co0/case 2/step 3"
    , "  o  train0/enter/CO/co0/case 2/step 4"
    , "  o  train0/enter/CO/co0/completeness"
    , "  o  train0/enter/CO/co1/completeness"
    , "  o  train0/enter/CO/co1/new assumption"
    , "  o  train0/enter/CO/co1/part 1/goal"
    , "  o  train0/enter/CO/co1/part 1/hypotheses"
    , "  o  train0/enter/CO/co1/part 1/relation"
    , "  o  train0/enter/CO/co1/part 1/step 1"
    , "  o  train0/enter/CO/co1/part 1/step 2"
    , "  o  train0/enter/CO/co1/part 2/case 1/goal"
    , "  o  train0/enter/CO/co1/part 2/case 1/hypotheses"
    , "  o  train0/enter/CO/co1/part 2/case 1/relation"
    , "  o  train0/enter/CO/co1/part 2/case 1/step 1"
    , "  o  train0/enter/CO/co1/part 2/case 1/step 2"
    , "  o  train0/enter/CO/co1/part 2/case 2/assertion/hyp6/easy"
    , "  o  train0/enter/CO/co1/part 2/case 2/main goal/goal"
    , "  o  train0/enter/CO/co1/part 2/case 2/main goal/hypotheses"
    , "  o  train0/enter/CO/co1/part 2/case 2/main goal/relation"
    , "  o  train0/enter/CO/co1/part 2/case 2/main goal/step 1"
    , "  o  train0/enter/CO/co1/part 2/case 2/main goal/step 2"
    , "  o  train0/enter/CO/co1/part 2/case 2/main goal/step 3"
    , "  o  train0/enter/CO/co1/part 2/completeness"
    , "  o  train0/enter/FIS/in@prime"
    , "  o  train0/enter/FIS/loc@prime"
    , "  o  train0/enter/INV/inv1"
    , "  o  train0/enter/INV/inv2/goal"
    , "  o  train0/enter/INV/inv2/hypotheses"
    , "  o  train0/enter/INV/inv2/relation"
    , "  o  train0/enter/INV/inv2/step 1"
    , "  o  train0/enter/INV/inv2/step 2"
    , "  o  train0/enter/INV/inv2/step 3"
    , "  o  train0/enter/INV/inv2/step 4"
    , "  o  train0/enter/INV/inv2/step 5"
    , "  o  train0/enter/SCH/grd1"
    , "  o  train0/enter/WD/ACT/a1"
    , "  o  train0/enter/WD/ACT/a2"
    , "  o  train0/enter/WD/C_SCH"
    , "  o  train0/enter/WD/F_SCH"
    , "  o  train0/enter/WD/GRD"
    , "  o  train0/enter/WWD"
    , "  o  train0/leave/CO/co0/assertion/hyp6/goal"
    , "  o  train0/leave/CO/co0/assertion/hyp6/hypotheses"
    , "  o  train0/leave/CO/co0/assertion/hyp6/relation"
    , "  o  train0/leave/CO/co0/assertion/hyp6/step 1"
    , "  o  train0/leave/CO/co0/assertion/hyp6/step 2"
    , "  o  train0/leave/CO/co0/assertion/hyp6/step 3"
    , "  o  train0/leave/CO/co0/main goal/goal"
    , "  o  train0/leave/CO/co0/main goal/hypotheses"
    , "  o  train0/leave/CO/co0/main goal/relation"
    , "  o  train0/leave/CO/co0/main goal/step 1"
    , "  o  train0/leave/CO/co0/main goal/step 2"
    , "  o  train0/leave/CO/co0/main goal/step 3"
    , "  o  train0/leave/CO/co0/main goal/step 4"
    , "  o  train0/leave/CO/co0/new assumption"
    , "  o  train0/leave/CO/co1/goal"
    , "  o  train0/leave/CO/co1/hypotheses"
    , "  o  train0/leave/CO/co1/relation"
    , "  o  train0/leave/CO/co1/step 1"
    , "  o  train0/leave/CO/co1/step 2"
    , "  o  train0/leave/CO/co1/step 3"
    , "  o  train0/leave/CO/co1/step 4"
    , "  o  train0/leave/CO/co1/step 5"
    , "  o  train0/leave/CO/co1/step 6"
    , "  o  train0/leave/CO/co1/step 7"
    , "  o  train0/leave/CO/co1/step 8"
    , "  o  train0/leave/C_SCH/weaken/c0"
    , "  o  train0/leave/FIS/in@prime"
    , "  o  train0/leave/FIS/loc@prime"
    , "  o  train0/leave/INV/inv1"
    , "  o  train0/leave/INV/inv2/goal"
    , "  o  train0/leave/INV/inv2/hypotheses"
    , "  o  train0/leave/INV/inv2/relation"
    , "  o  train0/leave/INV/inv2/step 1"
    , "  o  train0/leave/INV/inv2/step 2"
    , "  o  train0/leave/INV/inv2/step 3"
    , "  o  train0/leave/INV/inv2/step 4"
    , " xxx train0/leave/SCH/grd0"
    , "  o  train0/leave/WD/ACT/a0"
    , "  o  train0/leave/WD/ACT/a3"
    , "  o  train0/leave/WD/C_SCH"
    , "  o  train0/leave/WD/F_SCH"
    , "  o  train0/leave/WD/GRD"
    , "  o  train0/leave/WWD"
    , "  o  train0/tr0/TR/WD"
    , "  o  train0/tr0/TR/WD/witness/t"
    , "passed 114 / 115"
    ]

case1 :: IO (String, Map Label Sequent)
case1 = verify path0 0 
        
result2 :: String
result2 = unlines $
        [ "; train0/INIT/FIS/in"
        , "(set-option :auto-config false)"
        , "(set-option :smt.timeout 3000)"
        ]
     ++ push
     ++ train_decl False False
     ++ filterAssert kw
     (  set_decl_smt2 [] ++
        comp_facts [] ++ -- set_decl_smt2 ++
     [  "(assert (not (exists ( (in (set sl@TRAIN)) )"
     ,  "                     (and true (= in empty-set@@sl@TRAIN)))))" ]
     ++ named_facts ++
     [  "; asm2"
     ,  "(assert (and (not (= ent ext))"
     ,  "             (not (elem@@sl@BLK ent PLF))"
     ,  "             (not (elem@@sl@BLK ext PLF))))"
     ,  "; asm3"
     ,  "(assert (forall ( (p sl@BLK) )"
     ,  "                (! (= (not (= p ext))"
     ,  "                      (elem@@sl@BLK p (union (mk-set@@sl@BLK ent) PLF)))"
     ,  "                   :pattern"
     ,  "                   ( (elem@@sl@BLK p (union (mk-set@@sl@BLK ent) PLF)) ))))"
     ,  "; asm4"
     ,  "(assert (forall ( (p sl@BLK) )"
     ,  "                (! (= (not (= p ent))"
     ,  "                      (elem@@sl@BLK p (union (mk-set@@sl@BLK ext) PLF)))"
     ,  "                   :pattern"
     ,  "                   ( (elem@@sl@BLK p (union (mk-set@@sl@BLK ext) PLF)) ))))"
     ,  "; asm5"
     ,  "(assert (forall ( (p sl@BLK) )"
     ,  "                (! (= (or (= p ent) (= p ext))"
     ,  "                      (not (elem@@sl@BLK p PLF)))"
     ,  "                   :pattern"
     ,  "                   ( (elem@@sl@BLK p PLF) ))))"
     ,  "; axm0"
     ,  "(assert (= sl@BLK"
     ,  "           (union (union (mk-set@@sl@BLK ent) (mk-set@@sl@BLK ext))"
     ,  "                  PLF)))"
     ,  "(assert (not (= empty-set@@sl@TRAIN empty-set@@sl@TRAIN)))"
     ] 
     ++ check_sat
     ++ pop
     ++ ["; train0/INIT/FIS/in"])
    where
        kw = [ "(finite@@sl@LOC (mk-set@@sl@LOC"
             , "(finite@@sl@TRAIN (mk-set@@sl@TRAIN" 
             , "mk-set@@sl@TRAIN"
             , "elem@@sl@TRAIN"
             , "(elem@@sl@LOC x (mk-set@@sl@LOC y))" 
             , "(elem@@sl@TRAIN x (mk-set@@sl@TRAIN y))" ]

pop :: [String]
pop = []

push :: [String]
push = []

case2 :: IO String
case2 = proof_obligation path0 "train0/INIT/FIS/in" 0

filterAssert :: [String] -> [String] -> [String]
filterAssert kw xs = concatMap lines $ L.filter p $ groupBrack xs
    where
        p x = not $ any (`L.isInfixOf` x) kw

sortAssert :: [String] -> [String]
sortAssert = L.sort . groupBrack

result20 :: String
result20 = 
    let f = filterAssert xs 
        xs = [ 
               -- "dom-rest@@sl@TRAIN@@sl@BLK"
             -- , "dom-subt@@sl@TRAIN@@sl@BLK" 
             -- , "dom@@sl@TRAIN@@sl@BLK" 
               "apply@@sl@TRAIN@@sl@BLK"
             , "mk-set@@sl@TRAIN"
             , "mk-fun"
             -- , "compl@@sl@TRAIN"
             , "elem@@sl@TRAIN"
             , "elem@@sl@LOC"
             , "(finite@@sl@LOC (mk-set@@sl@LOC x))"
             -- , "(finite@@sl@TRAIN (mk-set@@sl@TRAIN x))"
             -- , "empty-fun@@sl@TRAIN@@sl@BLK"
             -- , "empty-set@@sl@TRAIN"
             -- , "set-diff@@sl@TRAIN" 
             -- , "finite@@sl@TRAIN" 
             -- , "st-subset@@sl@TRAIN"
             ]
    in
    unlines $
        [ "; train0/INIT/FIS/loc" 
        , "(set-option :auto-config false)"
        , "(set-option :smt.timeout 3000)"
        ]
     ++ push
     ++ train_decl False False
     ++ f (set_decl_smt2 [WithPFun])
     ++ f (comp_facts [WithPFun]) ++ 
     [  "(assert (not (exists ( (loc (pfun sl@TRAIN sl@BLK)) )"
     ,  "                     (and true (= loc empty-fun@@sl@TRAIN@@sl@BLK)))))" ]
     ++ named_facts ++
     [  "; asm2"
     ,  "(assert (and (not (= ent ext))"
     ,  "             (not (elem@@sl@BLK ent PLF))"
     ,  "             (not (elem@@sl@BLK ext PLF))))"
     ,  "; asm3"
     ,  "(assert (forall ( (p sl@BLK) )"
     ,  "                (! (= (not (= p ext))"
     ,  "                      (elem@@sl@BLK p (union (mk-set@@sl@BLK ent) PLF)))"
     ,  "                   :pattern"
     ,  "                   ( (elem@@sl@BLK p (union (mk-set@@sl@BLK ent) PLF)) ))))"
     ,  "; asm4"
     ,  "(assert (forall ( (p sl@BLK) )"
     ,  "                (! (= (not (= p ent))"
     ,  "                      (elem@@sl@BLK p (union (mk-set@@sl@BLK ext) PLF)))"
     ,  "                   :pattern"
     ,  "                   ( (elem@@sl@BLK p (union (mk-set@@sl@BLK ext) PLF)) ))))"
     ,  "; asm5"
     ,  "(assert (forall ( (p sl@BLK) )"
     ,  "                (! (= (or (= p ent) (= p ext))"
     ,  "                      (not (elem@@sl@BLK p PLF)))"
     ,  "                   :pattern"
     ,  "                   ( (elem@@sl@BLK p PLF) ))))"
     ,  "; axm0"
     ,  "(assert (= sl@BLK"
     ,  "           (union (union (mk-set@@sl@BLK ent) (mk-set@@sl@BLK ext))"
     ,  "                  PLF)))"
     ,  "(assert (not (= empty-fun@@sl@TRAIN@@sl@BLK"
     ,  "                empty-fun@@sl@TRAIN@@sl@BLK)))"
     ] 
     ++ check_sat
     ++ pop
     ++ [ "; train0/INIT/FIS/loc" ]

case20 :: IO String
case20 = proof_obligation path0 "train0/INIT/FIS/loc" 0
            
result3 :: String
result3 = unlines $
     [ "; train0/leave/FIS/in@prime" 
     , "(set-option :auto-config false)"
     , "(set-option :smt.timeout 3000)"
     ] ++
     push ++
     train_decl False True ++ 
     filterAssert kw 
     (    set_decl_smt2 [WithPFun] ++ 
          comp_facts [WithPFun] ++
          [  "(assert (not (exists ( (in@prime (set sl@TRAIN)) )"
          ,  "                     (and true"
          ,  "                          (= in@prime"
          ,  "                             (set-diff@@sl@TRAIN in (mk-set@@sl@TRAIN t)))))))" ]
          ++ named_facts ++
          [  "; asm2"
          ,  "(assert (and (not (= ent ext))"
          ,  "             (not (elem@@sl@BLK ent PLF))"
          ,  "             (not (elem@@sl@BLK ext PLF))))"
          ,  "; asm3"
          ,  "(assert (forall ( (p sl@BLK) )"
          ,  "                (! (= (not (= p ext))"
          ,  "                      (elem@@sl@BLK p (union (mk-set@@sl@BLK ent) PLF)))"
          ,  "                   :pattern"
          ,  "                   ( (elem@@sl@BLK p (union (mk-set@@sl@BLK ent) PLF)) ))))"
          ,  "; asm4"
          ,  "(assert (forall ( (p sl@BLK) )"
          ,  "                (! (= (not (= p ent))"
          ,  "                      (elem@@sl@BLK p (union (mk-set@@sl@BLK ext) PLF)))"
          ,  "                   :pattern"
          ,  "                   ( (elem@@sl@BLK p (union (mk-set@@sl@BLK ext) PLF)) ))))"
          ,  "; asm5"
          ,  "(assert (forall ( (p sl@BLK) )"
          ,  "                (! (= (or (= p ent) (= p ext))"
          ,  "                      (not (elem@@sl@BLK p PLF)))"
          ,  "                   :pattern"
          ,  "                   ( (elem@@sl@BLK p PLF) ))))"
          ,  "; axm0"
          ,  "(assert (= sl@BLK"
          ,  "           (union (union (mk-set@@sl@BLK ent) (mk-set@@sl@BLK ext))"
          ,  "                  PLF)))"
          ,  "; grd0"
          ,  "(assert (and (= (apply@@sl@TRAIN@@sl@BLK loc t) ext)"
          ,  "             (elem@@sl@TRAIN t in)))"
          ,  "; inv1"
          ,  "(assert (forall ( (t sl@TRAIN) )"
          ,  "                (! (=> (elem@@sl@TRAIN t in)"
          ,  "                       (elem@@sl@BLK (apply@@sl@TRAIN@@sl@BLK loc t) sl@BLK))"
          ,  "                   :pattern"
          ,  "                   ( (elem@@sl@BLK (apply@@sl@TRAIN@@sl@BLK loc t) sl@BLK) ))))"
          ,  "; inv2"
          ,  "(assert (= (dom@@sl@TRAIN@@sl@BLK loc) in))"
          ,  "(assert (not (= (set-diff@@sl@TRAIN in (mk-set@@sl@TRAIN t))"
          ,  "                (set-diff@@sl@TRAIN in (mk-set@@sl@TRAIN t)))))"
          ] ++ 
          check_sat ++
          pop ++
          [ "; train0/leave/FIS/in@prime" ]  )
    where
        kw = [ "finite@@sl@LOC (mk-set" 
             , "(elem@@sl@LOC x (mk-set@@sl@LOC y))" ]


case3 :: IO String
case3 = proof_obligation path0 "train0/leave/FIS/in@prime" 0

result19 :: String
result19 = unlines $
     [ "; train0/leave/FIS/loc@prime" 
     , "(set-option :auto-config false)"
     , "(set-option :smt.timeout 3000)"
     ] ++
     push ++ 
     train_decl False True ++ 
     filterAssert kw (
          set_decl_smt2 [WithPFun] ++ 
          comp_facts [WithPFun] ++
          [  "(assert (not (exists ( (loc@prime (pfun sl@TRAIN sl@BLK)) )"
          ,  "                     (and true"
          ,  "                          (= loc@prime"
          ,  "                             (dom-subt@@sl@TRAIN@@sl@BLK (mk-set@@sl@TRAIN t) loc))))))" ]
          ++ named_facts ++
          [  "; asm2"
          ,  "(assert (and (not (= ent ext))"
          ,  "             (not (elem@@sl@BLK ent PLF))"
          ,  "             (not (elem@@sl@BLK ext PLF))))"
          ,  "; asm3"
          ,  "(assert (forall ( (p sl@BLK) )"
          ,  "                (! (= (not (= p ext))"
          ,  "                      (elem@@sl@BLK p (union (mk-set@@sl@BLK ent) PLF)))"
          ,  "                   :pattern"
          ,  "                   ( (elem@@sl@BLK p (union (mk-set@@sl@BLK ent) PLF)) ))))"
          ,  "; asm4"
          ,  "(assert (forall ( (p sl@BLK) )"
          ,  "                (! (= (not (= p ent))"
          ,  "                      (elem@@sl@BLK p (union (mk-set@@sl@BLK ext) PLF)))"
          ,  "                   :pattern"
          ,  "                   ( (elem@@sl@BLK p (union (mk-set@@sl@BLK ext) PLF)) ))))"
          ,  "; asm5"
          ,  "(assert (forall ( (p sl@BLK) )"
          ,  "                (! (= (or (= p ent) (= p ext))"
          ,  "                      (not (elem@@sl@BLK p PLF)))"
          ,  "                   :pattern"
          ,  "                   ( (elem@@sl@BLK p PLF) ))))"
          ,  "; axm0"
          ,  "(assert (= sl@BLK"
          ,  "           (union (union (mk-set@@sl@BLK ent) (mk-set@@sl@BLK ext))"
          ,  "                  PLF)))"
          ,  "; grd0"
          ,  "(assert (and (= (apply@@sl@TRAIN@@sl@BLK loc t) ext)"
          ,  "             (elem@@sl@TRAIN t in)))"
          ,  "; inv1"
          ,  "(assert (forall ( (t sl@TRAIN) )"
          ,  "                (! (=> (elem@@sl@TRAIN t in)"
          ,  "                       (elem@@sl@BLK (apply@@sl@TRAIN@@sl@BLK loc t) sl@BLK))"
          ,  "                   :pattern"
          ,  "                   ( (elem@@sl@BLK (apply@@sl@TRAIN@@sl@BLK loc t) sl@BLK) ))))"
          ,  "; inv2"
          ,  "(assert (= (dom@@sl@TRAIN@@sl@BLK loc) in))"
          ,  "(assert (not (= (dom-subt@@sl@TRAIN@@sl@BLK (mk-set@@sl@TRAIN t) loc)"
          ,  "                (dom-subt@@sl@TRAIN@@sl@BLK (mk-set@@sl@TRAIN t) loc))))"
          ] ++ 
          check_sat ++
          pop ++
          [ "; train0/leave/FIS/loc@prime" ])
    where
        kw = [ "finite@@sl@LOC (mk-set" 
             , "(elem@@sl@LOC x (mk-set@@sl@LOC y))" ]

case19 :: IO String
case19 = proof_obligation path0 "train0/leave/FIS/loc@prime" 0

result4 :: String
result4 = unlines $
    [ "; train0/leave/SCH/grd0" 
    , "(set-option :auto-config false)"
    , "(set-option :smt.timeout 3000)"
    ] ++
    push ++
    train_decl False True ++ 
    filterAssert kw (
         set_decl_smt2 [WithPFun] ++ 
         comp_facts [WithPFun] ++
         named_facts ++
         [ "; asm2"
         , "(assert (and (not (= ent ext))"
         , "             (not (elem@@sl@BLK ent PLF))"
         , "             (not (elem@@sl@BLK ext PLF))))"
         , "; asm3"
         , "(assert (forall ( (p sl@BLK) )"
         , "                (! (= (not (= p ext))"
         , "                      (elem@@sl@BLK p (union (mk-set@@sl@BLK ent) PLF)))"
         , "                   :pattern"
         , "                   ( (elem@@sl@BLK p (union (mk-set@@sl@BLK ent) PLF)) ))))"
         , "; asm4"
         , "(assert (forall ( (p sl@BLK) )"
         , "                (! (= (not (= p ent))"
         , "                      (elem@@sl@BLK p (union (mk-set@@sl@BLK ext) PLF)))"
         , "                   :pattern"
         , "                   ( (elem@@sl@BLK p (union (mk-set@@sl@BLK ext) PLF)) ))))"
         , "; asm5"
         , "(assert (forall ( (p sl@BLK) )"
         , "                (! (= (or (= p ent) (= p ext))"
         , "                      (not (elem@@sl@BLK p PLF)))"
         , "                   :pattern"
         , "                   ( (elem@@sl@BLK p PLF) ))))"
         , "; axm0"
         , "(assert (= sl@BLK"
         , "           (union (union (mk-set@@sl@BLK ent) (mk-set@@sl@BLK ext))"
         , "                  PLF)))"
         , "; c0"
         , "(assert (elem@@sl@TRAIN t in))"
         , "; inv1"
         , "(assert (forall ( (t sl@TRAIN) )"
         , "                (! (=> (elem@@sl@TRAIN t in)"
         , "                       (elem@@sl@BLK (apply@@sl@TRAIN@@sl@BLK loc t) sl@BLK))"
         , "                   :pattern"
         , "                   ( (elem@@sl@BLK (apply@@sl@TRAIN@@sl@BLK loc t) sl@BLK) ))))"
         , "; inv2"
         , "(assert (= (dom@@sl@TRAIN@@sl@BLK loc) in))"
         , "(assert (not (and (= (apply@@sl@TRAIN@@sl@BLK loc t) ext)"
         , "                  (elem@@sl@TRAIN t in))))"
         ] ++ 
         check_sat ++
         pop ++
         [ "; train0/leave/SCH/grd0" ] )
    where
        kw = [ "finite@@sl@LOC (mk-set" 
             , "(elem@@sl@LOC x (mk-set@@sl@LOC y))" ]

case4 :: IO String
case4 = proof_obligation path0 "train0/leave/SCH/grd0" 0

result5 :: String
result5 = unlines $
    [ "; train0/TR/tr0/WFIS/t/t@prime" 
    , "(set-option :auto-config false)"
    , "(set-option :smt.timeout 3000)"
    ] ++
    push ++
    train_decl True True ++ 
    filterAssert kw (
        set_decl_smt2 [WithPFun] ++ 
        comp_facts [WithPFun] ++
        [  "(assert (not (exists ( (t@prime sl@TRAIN) ) (and true (= t@prime t)))))" ]
        ++ named_facts ++
        [  "; asm2"
        ,  "(assert (and (not (= ent ext))"
        ,  "             (not (elem@@sl@BLK ent PLF))"
        ,  "             (not (elem@@sl@BLK ext PLF))))"
        ,  "; asm3"
        ,  "(assert (forall ( (p sl@BLK) )"
        ,  "                (! (= (not (= p ext))"
        ,  "                      (elem@@sl@BLK p (union (mk-set@@sl@BLK ent) PLF)))"
        ,  "                   :pattern"
        ,  "                   ( (elem@@sl@BLK p (union (mk-set@@sl@BLK ent) PLF)) ))))"
        ,  "; asm4"
        ,  "(assert (forall ( (p sl@BLK) )"
        ,  "                (! (= (not (= p ent))"
        ,  "                      (elem@@sl@BLK p (union (mk-set@@sl@BLK ext) PLF)))"
        ,  "                   :pattern"
        ,  "                   ( (elem@@sl@BLK p (union (mk-set@@sl@BLK ext) PLF)) ))))"
        ,  "; asm5"
        ,  "(assert (forall ( (p sl@BLK) )"
        ,  "                (! (= (or (= p ent) (= p ext))"
        ,  "                      (not (elem@@sl@BLK p PLF)))"
        ,  "                   :pattern"
        ,  "                   ( (elem@@sl@BLK p PLF) ))))"
        ,  "; axm0"
        ,  "(assert (= sl@BLK"
        ,  "           (union (union (mk-set@@sl@BLK ent) (mk-set@@sl@BLK ext))"
        ,  "                  PLF)))"
        ,  "; inv1"
        ,  "(assert (forall ( (t sl@TRAIN) )"
        ,  "                (! (=> (elem@@sl@TRAIN t in)"
        ,  "                       (elem@@sl@BLK (apply@@sl@TRAIN@@sl@BLK loc t) sl@BLK))"
        ,  "                   :pattern"
        ,  "                   ( (elem@@sl@BLK (apply@@sl@TRAIN@@sl@BLK loc t) sl@BLK) ))))"
        ,  "; inv2"
        ,  "(assert (= (dom@@sl@TRAIN@@sl@BLK loc) in))"
        ,  "; tr0"
        ,  "(assert (elem@@sl@TRAIN t in))"
        ,  "(assert (not (= t t)))"
        ] ++ 
        check_sat ++
        pop ++
        [ "; train0/TR/tr0/WFIS/t/t@prime" ])
    where
        kw = [ "finite@@sl@LOC (mk-set" 
             , "(elem@@sl@LOC x (mk-set@@sl@LOC y))" ]

case5 :: IO String
case5 = proof_obligation path0 "train0/TR/tr0/WFIS/t/t@prime" 0

addDecl :: String -> [String] -> [String]
addDecl y xs = x ++ y : z
    where
        (x,z) = L.span p $ groupBrack xs
        p x   = "(declare-fun " `L.isPrefixOf` x

result23 :: String
result23 = unlines $
    [ "; train0/TR/tr0/leave/EN" 
    , "(set-option :auto-config false)"
    , "(set-option :smt.timeout 3000)"
    ] ++
    push ++
    train_decl True True ++ 
    filterAssert kw (
            "(declare-fun t@param () sl@TRAIN)" `addDecl`
            set_decl_smt2 [WithPFun] ++ 
        comp_facts [WithPFun] ++
        [ "(assert (= t@param t))" ] ++
        named_facts ++
        [  "; asm2"
        ,  "(assert (and (not (= ent ext))"
        ,  "             (not (elem@@sl@BLK ent PLF))"
        ,  "             (not (elem@@sl@BLK ext PLF))))"
        ,  "; asm3"
        ,  "(assert (forall ( (p sl@BLK) )"
        ,  "                (! (= (not (= p ext))"
        ,  "                      (elem@@sl@BLK p (union (mk-set@@sl@BLK ent) PLF)))"
        ,  "                   :pattern"
        ,  "                   ( (elem@@sl@BLK p (union (mk-set@@sl@BLK ent) PLF)) ))))"
        ,  "; asm4"
        ,  "(assert (forall ( (p sl@BLK) )"
        ,  "                (! (= (not (= p ent))"
        ,  "                      (elem@@sl@BLK p (union (mk-set@@sl@BLK ext) PLF)))"
        ,  "                   :pattern"
        ,  "                   ( (elem@@sl@BLK p (union (mk-set@@sl@BLK ext) PLF)) ))))"
        ,  "; asm5"
        ,  "(assert (forall ( (p sl@BLK) )"
        ,  "                (! (= (or (= p ent) (= p ext))"
        ,  "                      (not (elem@@sl@BLK p PLF)))"
        ,  "                   :pattern"
        ,  "                   ( (elem@@sl@BLK p PLF) ))))"
        ,  "; axm0"
        ,  "(assert (= sl@BLK"
        ,  "           (union (union (mk-set@@sl@BLK ent) (mk-set@@sl@BLK ext))"
        ,  "                  PLF)))"
        ,  "; inv1"
        ,  "(assert (forall ( (t sl@TRAIN) )"
        ,  "                (! (=> (elem@@sl@TRAIN t in)"
        ,  "                       (elem@@sl@BLK (apply@@sl@TRAIN@@sl@BLK loc t) sl@BLK))"
        ,  "                   :pattern"
        ,  "                   ( (elem@@sl@BLK (apply@@sl@TRAIN@@sl@BLK loc t) sl@BLK) ))))"
        ,  "; inv2"
        ,  "(assert (= (dom@@sl@TRAIN@@sl@BLK loc) in))"
        ,  "(assert (not (=> (elem@@sl@TRAIN t in) (elem@@sl@TRAIN t@param in))))"
        ] ++ 
        check_sat ++
        pop ++
        [ "; train0/TR/tr0/leave/EN" ] )
    where
        kw = [ "finite@@sl@LOC (mk-set" 
             , "(elem@@sl@LOC x (mk-set@@sl@LOC y))" ]

case23 :: IO String
case23 = proof_obligation path0 "train0/TR/tr0/leave/EN" 0

result24 :: String
result24 = unlines $
    [ "; train0/TR/tr0/leave/NEG" 
    , "(set-option :auto-config false)"
    , "(set-option :smt.timeout 3000)"
    ] ++
    push ++
    train_decl True True ++ 
    filterAssert kw (
            "(declare-fun t@param () sl@TRAIN)" `addDecl`
            set_decl_smt2 [WithPFun] ++ 
        comp_facts [WithPFun] ++
        named_facts ++
        [  "(assert (= t@param t))"
        ,  "; a0"
        ,  "(assert (= in@prime"
        ,  "           (set-diff@@sl@TRAIN in (mk-set@@sl@TRAIN t@param))))"
        ,  "; a3"
        ,  "(assert (= loc@prime"
        ,  "           (dom-subt@@sl@TRAIN@@sl@BLK (mk-set@@sl@TRAIN t@param) loc)))"
        ,  "; asm2"
        ,  "(assert (and (not (= ent ext))"
        ,  "             (not (elem@@sl@BLK ent PLF))"
        ,  "             (not (elem@@sl@BLK ext PLF))))"
        ,  "; asm3"
        ,  "(assert (forall ( (p sl@BLK) )"
        ,  "                (! (= (not (= p ext))"
        ,  "                      (elem@@sl@BLK p (union (mk-set@@sl@BLK ent) PLF)))"
        ,  "                   :pattern"
        ,  "                   ( (elem@@sl@BLK p (union (mk-set@@sl@BLK ent) PLF)) ))))"
        ,  "; asm4"
        ,  "(assert (forall ( (p sl@BLK) )"
        ,  "                (! (= (not (= p ent))"
        ,  "                      (elem@@sl@BLK p (union (mk-set@@sl@BLK ext) PLF)))"
        ,  "                   :pattern"
        ,  "                   ( (elem@@sl@BLK p (union (mk-set@@sl@BLK ext) PLF)) ))))"
        ,  "; asm5"
        ,  "(assert (forall ( (p sl@BLK) )"
        ,  "                (! (= (or (= p ent) (= p ext))"
        ,  "                      (not (elem@@sl@BLK p PLF)))"
        ,  "                   :pattern"
        ,  "                   ( (elem@@sl@BLK p PLF) ))))"
        ,  "; axm0"
        ,  "(assert (= sl@BLK"
        ,  "           (union (union (mk-set@@sl@BLK ent) (mk-set@@sl@BLK ext))"
        ,  "                  PLF)))"
        ,  "; c0"
        ,  "(assert (elem@@sl@TRAIN t@param in))"
        ,  "; grd0"
        ,  "(assert (and (= (apply@@sl@TRAIN@@sl@BLK loc t@param) ext)"
        ,  "             (elem@@sl@TRAIN t@param in)))"
        ,  "; inv1"
        ,  "(assert (forall ( (t sl@TRAIN) )"
        ,  "                (! (=> (elem@@sl@TRAIN t in)"
        ,  "                       (elem@@sl@BLK (apply@@sl@TRAIN@@sl@BLK loc t) sl@BLK))"
        ,  "                   :pattern"
        ,  "                   ( (elem@@sl@BLK (apply@@sl@TRAIN@@sl@BLK loc t) sl@BLK) ))))"
        ,  "; inv2"
        ,  "(assert (= (dom@@sl@TRAIN@@sl@BLK loc) in))"
        ,  "(assert (not (=> (elem@@sl@TRAIN t in)"
        ,  "                 (not (elem@@sl@TRAIN t in@prime)))))"
        ] ++ 
        check_sat ++
        pop ++
        [ "; train0/TR/tr0/leave/NEG" ] )
    where
        kw = [ "finite@@sl@LOC (mk-set" 
             , "(elem@@sl@LOC x (mk-set@@sl@LOC y))" ]

case24 :: IO String
case24 = proof_obligation path0 "train0/TR/tr0/leave/NEG" 0

--result6 = unlines ( 
--        train_decl True ++ 
--        set_decl_smt2 ++ 
--        comp_facts ++
--        [  "(assert (= sl@BLK (bunion@@sl@BLK (bunion@@sl@BLK (mk-set@@sl@BLK ent) (mk-set@@sl@BLK ext)) PLF)))"
--        ,  "(assert (elem@@sl@TRAIN t in))"
--        ,  "(assert (= (dom@@sl@TRAIN@@sl@BLK loc) in))"
--        ,  "(assert (elem@@sl@TRAIN t in))"
--        ,  "(assert (= in@prime (set-diff@@sl@TRAIN in (mk-set@@sl@TRAIN t))))"
--        ,  "(assert (= loc@prime (dom-subt@@sl@TRAIN@@sl@BLK (mk-set@@sl@TRAIN t) loc)))"
--        ,  "(assert (not (not (elem@@sl@TRAIN t in@prime))))"
--        ,  "(check-sat-using (or-else (then qe smt) (then skip smt) (then (using-params simplify :expand-power true) smt)))"
--        ] )
----    where
----        in_prime = ["(declare-const in@prime (set sl@TRAIN))"]
----        loc_prime = ["(declare-const loc@prime (pfun sl@TRAIN sl@BLK))"]
--
--
--case6 = do
--        pos <- list_file_obligations path0
--        case pos of
--            Right [(_,pos)] -> do
--                let po = pos ! "m0/leave/TR/NEG/tr0"
--                    cmd = unlines $ map (show . as_tree) $ z3_code po
--                return cmd
--            x -> return $ show x

result12 :: String
result12 = unlines $
    [ "; train0/leave/INV/inv2" 
    , "(set-option :auto-config false)"
    , "(set-option :smt.timeout 3000)"
    ] ++
    push ++
    train_decl True True ++ 
    filterAssert kw (
        set_decl_smt2 [WithPFun] ++ 
        comp_facts [WithPFun] ++
        named_facts ++
        [  "; a0"
        ,  "(assert (= in@prime"
        ,  "           (set-diff@@sl@TRAIN in (mk-set@@sl@TRAIN t))))"
        ,  "; a3"
        ,  "(assert (= loc@prime"
        ,  "           (dom-subt@@sl@TRAIN@@sl@BLK (mk-set@@sl@TRAIN t) loc)))"
        ,  "; asm2"
        ,  "(assert (and (not (= ent ext))"
        ,  "             (not (elem@@sl@BLK ent PLF))"
        ,  "             (not (elem@@sl@BLK ext PLF))))"
        ,  "; asm3"
        ,  "(assert (forall ( (p sl@BLK) )"
        ,  "                (! (= (not (= p ext))"
        ,  "                      (elem@@sl@BLK p (union (mk-set@@sl@BLK ent) PLF)))"
        ,  "                   :pattern"
        ,  "                   ( (elem@@sl@BLK p (union (mk-set@@sl@BLK ent) PLF)) ))))"
        ,  "; asm4"
        ,  "(assert (forall ( (p sl@BLK) )"
        ,  "                (! (= (not (= p ent))"
        ,  "                      (elem@@sl@BLK p (union (mk-set@@sl@BLK ext) PLF)))"
        ,  "                   :pattern"
        ,  "                   ( (elem@@sl@BLK p (union (mk-set@@sl@BLK ext) PLF)) ))))"
        ,  "; asm5"
        ,  "(assert (forall ( (p sl@BLK) )"
        ,  "                (! (= (or (= p ent) (= p ext))"
        ,  "                      (not (elem@@sl@BLK p PLF)))"
        ,  "                   :pattern"
        ,  "                   ( (elem@@sl@BLK p PLF) ))))"
        ,  "; axm0"
        ,  "(assert (= sl@BLK"
        ,  "           (union (union (mk-set@@sl@BLK ent) (mk-set@@sl@BLK ext))"
        ,  "                  PLF)))"
        ,  "; grd0"
        ,  "(assert (and (= (apply@@sl@TRAIN@@sl@BLK loc t) ext)"
        ,  "             (elem@@sl@TRAIN t in)))"
        ,  "; inv1"
        ,  "(assert (forall ( (t sl@TRAIN) )"
        ,  "                (! (=> (elem@@sl@TRAIN t in)"
        ,  "                       (elem@@sl@BLK (apply@@sl@TRAIN@@sl@BLK loc t) sl@BLK))"
        ,  "                   :pattern"
        ,  "                   ( (elem@@sl@BLK (apply@@sl@TRAIN@@sl@BLK loc t) sl@BLK) ))))"
        ,  "; inv2"
        ,  "(assert (= (dom@@sl@TRAIN@@sl@BLK loc) in))"
        ,  "(assert (not (= (dom@@sl@TRAIN@@sl@BLK loc@prime) in@prime)))"
        ] ++ 
        check_sat ++
        pop ++
        [ "; train0/leave/INV/inv2" ])
    where
        kw = [ "finite@@sl@LOC (mk-set" 
             , "(elem@@sl@LOC x (mk-set@@sl@LOC y))" ]

case12 :: IO String
case12 = raw_proof_obligation path0 "train0/leave/INV/inv2" 0

    --------------------
    -- Error handling --
    --------------------
result7 :: Either [Error] a
result7 = Left [Error "unrecognized term: t" (LI path7 54 3)]

path7 :: String
path7 = "Tests/train-station-err0.tex"

case7 :: IO (Either [Error] [Machine])
case7 = parse path7

result8 :: Either [Error] a
result8 = Left [Error "event 'leave' is undeclared" (LI path8 42 15)]

path8 :: String
path8 = "Tests/train-station-err1.tex"

case8 :: IO (Either [Error] [Machine])
case8 = parse path8

result9 :: Either [Error] a
result9 = Left [Error "event 'leave' is undeclared" (LI path9 51 15)]

path9 :: String
path9 = "Tests/train-station-err2.tex"

case9 :: IO (Either [Error] [Machine])
case9 = parse path9

result10 :: Either [Error] a
result10 = Left [Error "event 'leave' is undeclared" (LI path10 55 15)]

path10 :: String
path10 = "Tests/train-station-err3.tex"

case10 :: IO (Either [Error] [Machine])
case10 = parse path10

result11 :: Either [Error] a
result11 = Left [Error "event 'leave' is undeclared" (LI path11 59 15)]

path11 :: String
path11 = "Tests/train-station-err4.tex"

case11 :: IO (Either [Error] [Machine])
case11 = parse path11

path13 :: String
path13 = "Tests/train-station-err5.tex"

result13 :: String
result13 = unlines
    [ "error 176:3:"
    , "    unrecognized term: t0"
    , "Perhaps you meant:"
    , "t (variable)"
    , ""
    , "error 178:3:"
    , "    unrecognized term: t0"
    , "Perhaps you meant:"
    , "t (variable)"
    , ""
    , "error 180:3:"
    , "    unrecognized term: t0"
    , "Perhaps you meant:"
    , "t (variable)"
    , ""
    , "error 182:3:"
    , "    unrecognized term: t0"
    , "Perhaps you meant:"
    , "t (variable)"
    , ""
    , "error 186:31:"
    , "    unrecognized term: t0"
    , "Perhaps you meant:"
    , "t (variable)"
    , ""
    , "error 251:3:"
    , "    unrecognized term: t0"
    , "Perhaps you meant:"
    , "t (variable)"
    , ""
    , "error 253:3:"
    , "    unrecognized term: t0"
    , "Perhaps you meant:"
    , "t (variable)"
    , ""
    , "error 256:3:"
    , "    unrecognized term: t0"
    , "Perhaps you meant:"
    , "t (variable)"
    , ""
    , "error 261:4:"
    , "    unrecognized term: t0"
    , "Perhaps you meant:"
    , "t (variable)"
    , ""
    , "error 264:3:"
    , "    unrecognized term: t0"
    , "Perhaps you meant:"
    , "t (variable)"
    , ""
    , "error 267:3:"
    , "    unrecognized term: t0"
    , "Perhaps you meant:"
    , "t (variable)"
    , ""
    , "error 269:4:"
    , "    unrecognized term: t0"
    , "Perhaps you meant:"
    , "t (variable)"
    , ""
    , "error 272:4:"
    , "    unrecognized term: t0"
    , "Perhaps you meant:"
    , "t (variable)"
    , ""
    , "error 274:4:"
    , "    unrecognized term: t0"
    , "Perhaps you meant:"
    , "t (variable)"
    , ""
    ]

case13 :: IO String
case13 = find_errors path13


path14 :: String
path14 = "Tests/train-station-err6.tex"

result14 :: String
result14 = unlines
    [ "  o  train0/INIT/FIS/in"
    , "  o  train0/INIT/FIS/loc"
    , "  o  train0/INIT/INV/inv1"
    , "  o  train0/INIT/INV/inv2"
    , "  o  train0/INIT/WD"
    , "  o  train0/INIT/WWD"
    , "  o  train0/INV/WD"
    , "  o  train0/SKIP/CO/co0"
    , "  o  train0/SKIP/CO/co1"
    , "  o  train0/TR/tr0/WFIS/t/t@prime"
    , "  o  train0/TR/tr0/leave/EN"
    , "  o  train0/TR/tr0/leave/NEG"
    , "  o  train0/co0/CO/WD"
    , "  o  train0/co1/CO/WD"
    , "  o  train0/enter/CO/co0/case 1/goal"
    , "  o  train0/enter/CO/co0/case 1/hypotheses"
    , "  o  train0/enter/CO/co0/case 1/relation"
    , "  o  train0/enter/CO/co0/case 1/step 1"
    , "  o  train0/enter/CO/co0/case 1/step 2"
    , " xxx train0/enter/CO/co0/completeness"
    , "  o  train0/enter/CO/co1"
    , "  o  train0/enter/FIS/in@prime"
    , "  o  train0/enter/FIS/loc@prime"
    , "  o  train0/enter/INV/inv1"
    , "  o  train0/enter/INV/inv2/goal"
    , "  o  train0/enter/INV/inv2/hypotheses"
    , "  o  train0/enter/INV/inv2/relation"
    , "  o  train0/enter/INV/inv2/step 1"
    , "  o  train0/enter/INV/inv2/step 2"
    , "  o  train0/enter/INV/inv2/step 3"
    , "  o  train0/enter/INV/inv2/step 4"
    , "  o  train0/enter/INV/inv2/step 5"
    , "  o  train0/enter/SAF/s0"
    , "  o  train0/enter/SAF/s1"
    , "  o  train0/enter/SCH/grd1"
    , "  o  train0/enter/WD/ACT/a1"
    , "  o  train0/enter/WD/ACT/a2"
    , "  o  train0/enter/WD/C_SCH"
    , "  o  train0/enter/WD/F_SCH"
    , "  o  train0/enter/WD/GRD"
    , "  o  train0/enter/WWD"
    , "  o  train0/leave/CO/co0/goal"
    , "  o  train0/leave/CO/co0/hypotheses"
    , "  o  train0/leave/CO/co0/relation"
    , "  o  train0/leave/CO/co0/step 1"
    , "  o  train0/leave/CO/co0/step 2"
    , "  o  train0/leave/CO/co0/step 3"
    , "  o  train0/leave/CO/co0/step 4"
    , "  o  train0/leave/CO/co1/goal"
    , "  o  train0/leave/CO/co1/hypotheses"
    , "  o  train0/leave/CO/co1/relation"
    , "  o  train0/leave/CO/co1/step 1"
    , "  o  train0/leave/CO/co1/step 2"
    , "  o  train0/leave/CO/co1/step 3"
    , "  o  train0/leave/CO/co1/step 4"
    , "  o  train0/leave/CO/co1/step 5"
    , "  o  train0/leave/CO/co1/step 6"
    , "  o  train0/leave/CO/co1/step 7"
    , "  o  train0/leave/CO/co1/step 8"
    , "  o  train0/leave/C_SCH/weaken/c0"
    , "  o  train0/leave/FIS/in@prime"
    , "  o  train0/leave/FIS/loc@prime"
    , "  o  train0/leave/INV/inv1"
    , "  o  train0/leave/INV/inv2/goal"
    , "  o  train0/leave/INV/inv2/hypotheses"
    , "  o  train0/leave/INV/inv2/relation"
    , "  o  train0/leave/INV/inv2/step 1"
    , "  o  train0/leave/INV/inv2/step 2"
    , "  o  train0/leave/INV/inv2/step 3"
    , "  o  train0/leave/INV/inv2/step 4"
    , "  o  train0/leave/SAF/s0"
    , "  o  train0/leave/SAF/s1"
    , " xxx train0/leave/SCH/grd0"
    , "  o  train0/leave/WD/ACT/a0"
    , "  o  train0/leave/WD/ACT/a3"
    , "  o  train0/leave/WD/C_SCH"
    , "  o  train0/leave/WD/F_SCH"
    , "  o  train0/leave/WD/GRD"
    , "  o  train0/leave/WWD"
    , "  o  train0/s0/SAF/WD/lhs"
    , "  o  train0/s0/SAF/WD/rhs"
    , "  o  train0/s1/SAF/WD/lhs"
    , "  o  train0/s1/SAF/WD/rhs"
    , "  o  train0/tr0/TR/WD"
    , "  o  train0/tr0/TR/WD/witness/t"
    , "passed 83 / 85"
    ]
        
case14 :: IO (String, Map Label Sequent)
case14 = verify path14 0
    
path15 :: String
path15 = "Tests/train-station-err7.tex"

result15 :: String
result15 = unlines
    [ "  o  train0/INIT/FIS/in"
    , "  o  train0/INIT/FIS/loc"
    , "  o  train0/INIT/INV/inv1"
    , "  o  train0/INIT/INV/inv2"
    , "  o  train0/INIT/WD"
    , "  o  train0/INIT/WWD"
    , "  o  train0/INV/WD"
    , "  o  train0/SKIP/CO/co0"
    , "  o  train0/SKIP/CO/co1"
    , "  o  train0/TR/tr0/WFIS/t/t@prime"
    , "  o  train0/TR/tr0/leave/EN"
    , "  o  train0/TR/tr0/leave/NEG"
    , "  o  train0/co0/CO/WD"
    , "  o  train0/co1/CO/WD"
    , "  o  train0/enter/CO/co0/case 1/goal"
    , "  o  train0/enter/CO/co0/case 1/hypotheses"
    , "  o  train0/enter/CO/co0/case 1/relation"
    , "  o  train0/enter/CO/co0/case 1/step 1"
    , "  o  train0/enter/CO/co0/case 1/step 2"
    , "  o  train0/enter/CO/co0/case 2/goal"
    , "  o  train0/enter/CO/co0/case 2/hypotheses"
    , "  o  train0/enter/CO/co0/case 2/relation"
    , "  o  train0/enter/CO/co0/case 2/step 1"
    , "  o  train0/enter/CO/co0/case 2/step 2"
    , "  o  train0/enter/CO/co0/case 2/step 3"
    , "  o  train0/enter/CO/co0/case 2/step 4"
    , "  o  train0/enter/CO/co0/completeness"
    , "  o  train0/enter/CO/co1"
    , "  o  train0/enter/FIS/in@prime"
    , "  o  train0/enter/FIS/loc@prime"
    , "  o  train0/enter/INV/inv1"
    , "  o  train0/enter/INV/inv2/goal"
    , "  o  train0/enter/INV/inv2/hypotheses"
    , "  o  train0/enter/INV/inv2/relation"
    , "  o  train0/enter/INV/inv2/step 1"
    , "  o  train0/enter/INV/inv2/step 2"
    , "  o  train0/enter/INV/inv2/step 3"
    , "  o  train0/enter/INV/inv2/step 4"
    , "  o  train0/enter/INV/inv2/step 5"
    , "  o  train0/enter/SAF/s0"
    , "  o  train0/enter/SAF/s1"
    , "  o  train0/enter/SCH/grd1"
    , "  o  train0/enter/WD/ACT/a1"
    , "  o  train0/enter/WD/ACT/a2"
    , "  o  train0/enter/WD/C_SCH"
    , "  o  train0/enter/WD/F_SCH"
    , "  o  train0/enter/WD/GRD"
    , "  o  train0/enter/WWD"
    , "  o  train0/leave/CO/co0/goal"
    , "  o  train0/leave/CO/co0/hypotheses"
    , " xxx train0/leave/CO/co0/new assumption"
    , "  o  train0/leave/CO/co0/relation"
    , "  o  train0/leave/CO/co0/step 1"
    , " xxx train0/leave/CO/co0/step 2"
    , "  o  train0/leave/CO/co1/goal"
    , "  o  train0/leave/CO/co1/hypotheses"
    , "  o  train0/leave/CO/co1/relation"
    , "  o  train0/leave/CO/co1/step 1"
    , "  o  train0/leave/CO/co1/step 2"
    , "  o  train0/leave/CO/co1/step 3"
    , "  o  train0/leave/CO/co1/step 4"
    , "  o  train0/leave/CO/co1/step 5"
    , "  o  train0/leave/CO/co1/step 6"
    , "  o  train0/leave/CO/co1/step 7"
    , "  o  train0/leave/CO/co1/step 8"
    , "  o  train0/leave/C_SCH/weaken/c0"
    , "  o  train0/leave/FIS/in@prime"
    , "  o  train0/leave/FIS/loc@prime"
    , "  o  train0/leave/INV/inv1"
    , "  o  train0/leave/INV/inv2/goal"
    , "  o  train0/leave/INV/inv2/hypotheses"
    , "  o  train0/leave/INV/inv2/relation"
    , "  o  train0/leave/INV/inv2/step 1"
    , "  o  train0/leave/INV/inv2/step 2"
    , "  o  train0/leave/INV/inv2/step 3"
    , "  o  train0/leave/INV/inv2/step 4"
    , "  o  train0/leave/SAF/s0"
    , "  o  train0/leave/SAF/s1"
    , " xxx train0/leave/SCH/grd0"
    , "  o  train0/leave/WD/ACT/a0"
    , "  o  train0/leave/WD/ACT/a3"
    , "  o  train0/leave/WD/C_SCH"
    , "  o  train0/leave/WD/F_SCH"
    , "  o  train0/leave/WD/GRD"
    , "  o  train0/leave/WWD"
    , "  o  train0/s0/SAF/WD/lhs"
    , "  o  train0/s0/SAF/WD/rhs"
    , "  o  train0/s1/SAF/WD/lhs"
    , "  o  train0/s1/SAF/WD/rhs"
    , "  o  train0/tr0/TR/WD"
    , "  o  train0/tr0/TR/WD/witness/t"
    , "passed 88 / 91"
    ]
      
case15 :: IO (String, Map Label Sequent)
case15 = verify path15 0

path16 :: String
path16 = "Tests/train-station-t2.tex"

result16 :: String
result16 = unlines 
    [ "  o  train0/INIT/FIS/in"
    , "  o  train0/INIT/FIS/loc"
    , "  o  train0/INIT/INV/inv1"
    , "  o  train0/INIT/INV/inv2"
    , "  o  train0/INIT/WD"
    , "  o  train0/INIT/WWD"
    , "  o  train0/INV/WD"
    , "  o  train0/SKIP/CO/co0"
    , "  o  train0/SKIP/CO/co1"
    , "  o  train0/TR/tr0/WFIS/t/t@prime"
    , "  o  train0/TR/tr0/leave/EN"
    , "  o  train0/TR/tr0/leave/NEG"
    , "  o  train0/co0/CO/WD"
    , "  o  train0/co1/CO/WD"
    , "  o  train0/enter/CO/co0/case 1/goal"
    , "  o  train0/enter/CO/co0/case 1/hypotheses"
    , "  o  train0/enter/CO/co0/case 1/relation"
    , "  o  train0/enter/CO/co0/case 1/step 1"
    , "  o  train0/enter/CO/co0/case 1/step 2"
    , "  o  train0/enter/CO/co0/case 2/goal"
    , "  o  train0/enter/CO/co0/case 2/hypotheses"
    , "  o  train0/enter/CO/co0/case 2/relation"
    , "  o  train0/enter/CO/co0/case 2/step 1"
    , "  o  train0/enter/CO/co0/case 2/step 2"
    , "  o  train0/enter/CO/co0/case 2/step 3"
    , "  o  train0/enter/CO/co0/case 2/step 4"
    , "  o  train0/enter/CO/co0/completeness"
    , "  o  train0/enter/CO/co1/completeness"
    , "  o  train0/enter/CO/co1/new assumption"
    , "  o  train0/enter/CO/co1/part 1/goal"
    , "  o  train0/enter/CO/co1/part 1/hypotheses"
    , "  o  train0/enter/CO/co1/part 1/relation"
    , "  o  train0/enter/CO/co1/part 1/step 1"
    , "  o  train0/enter/CO/co1/part 1/step 2"
    , "  o  train0/enter/CO/co1/part 2/case 1/goal"
    , "  o  train0/enter/CO/co1/part 2/case 1/hypotheses"
    , "  o  train0/enter/CO/co1/part 2/case 1/relation"
    , "  o  train0/enter/CO/co1/part 2/case 1/step 1"
    , "  o  train0/enter/CO/co1/part 2/case 1/step 2"
    , "  o  train0/enter/CO/co1/part 2/case 2/goal"
    , "  o  train0/enter/CO/co1/part 2/case 2/hypotheses"
    , "  o  train0/enter/CO/co1/part 2/case 2/relation"
    , "  o  train0/enter/CO/co1/part 2/case 2/step 1"
    , "  o  train0/enter/CO/co1/part 2/case 2/step 2"
    , "  o  train0/enter/CO/co1/part 2/case 2/step 3"
    , "  o  train0/enter/CO/co1/part 2/completeness"
    , "  o  train0/enter/FIS/in@prime"
    , "  o  train0/enter/FIS/loc@prime"
    , "  o  train0/enter/INV/inv1"
    , "  o  train0/enter/INV/inv2/goal"
    , "  o  train0/enter/INV/inv2/hypotheses"
    , "  o  train0/enter/INV/inv2/relation"
    , "  o  train0/enter/INV/inv2/step 1"
    , "  o  train0/enter/INV/inv2/step 2"
    , "  o  train0/enter/INV/inv2/step 3"
    , "  o  train0/enter/INV/inv2/step 4"
    , "  o  train0/enter/INV/inv2/step 5"
    , "  o  train0/enter/SAF/s0"
    , "  o  train0/enter/SAF/s1"
    , "  o  train0/enter/SCH/grd1"
    , "  o  train0/enter/WD/ACT/a1"
    , "  o  train0/enter/WD/ACT/a2"
    , "  o  train0/enter/WD/C_SCH"
    , "  o  train0/enter/WD/F_SCH"
    , "  o  train0/enter/WD/GRD"
    , "  o  train0/enter/WWD"
    , "  o  train0/leave/CO/co0/goal"
    , "  o  train0/leave/CO/co0/hypotheses"
    , "  o  train0/leave/CO/co0/relation"
    , "  o  train0/leave/CO/co0/step 1"
    , "  o  train0/leave/CO/co0/step 2"
    , "  o  train0/leave/CO/co0/step 3"
    , "  o  train0/leave/CO/co0/step 4"
    , "  o  train0/leave/CO/co1/goal"
    , "  o  train0/leave/CO/co1/hypotheses"
    , "  o  train0/leave/CO/co1/relation"
    , "  o  train0/leave/CO/co1/step 1"
    , "  o  train0/leave/CO/co1/step 2"
    , "  o  train0/leave/CO/co1/step 3"
    , "  o  train0/leave/CO/co1/step 4"
    , "  o  train0/leave/CO/co1/step 5"
    , "  o  train0/leave/CO/co1/step 6"
    , "  o  train0/leave/CO/co1/step 7"
    , "  o  train0/leave/CO/co1/step 8"
    , "  o  train0/leave/C_SCH/weaken/c0"
    , "  o  train0/leave/FIS/in@prime"
    , "  o  train0/leave/FIS/loc@prime"
    , "  o  train0/leave/INV/inv1"
    , "  o  train0/leave/INV/inv2/goal"
    , "  o  train0/leave/INV/inv2/hypotheses"
    , "  o  train0/leave/INV/inv2/relation"
    , "  o  train0/leave/INV/inv2/step 1"
    , "  o  train0/leave/INV/inv2/step 2"
    , "  o  train0/leave/INV/inv2/step 3"
    , "  o  train0/leave/INV/inv2/step 4"
    , "  o  train0/leave/SAF/s0"
    , "  o  train0/leave/SAF/s1"
    , " xxx train0/leave/SCH/grd0"
    , "  o  train0/leave/WD/ACT/a0"
    , "  o  train0/leave/WD/ACT/a3"
    , "  o  train0/leave/WD/C_SCH"
    , "  o  train0/leave/WD/F_SCH"
    , "  o  train0/leave/WD/GRD"
    , "  o  train0/leave/WWD"
    , "  o  train0/s0/SAF/WD/lhs"
    , "  o  train0/s0/SAF/WD/rhs"
    , "  o  train0/s1/SAF/WD/lhs"
    , "  o  train0/s1/SAF/WD/rhs"
    , "  o  train0/tr0/TR/WD"
    , "  o  train0/tr0/TR/WD/witness/t"
    , "passed 109 / 110"
    ]

case16 :: IO (String, Map Label Sequent)
case16 = verify path16 0

path17 :: String
path17 = "Tests/train-station-err8.tex"

result17 :: String
result17 = unlines 
        [  "error 75:3:\n    type of empty-fun is ill-defined: \\pfun [\\TRAIN,_a]"
        ,  "error 75:3:\n    type of empty-fun is ill-defined: \\pfun [\\TRAIN,_b]"
        ,  "error 77:2:\n    type of empty-fun is ill-defined: \\pfun [\\TRAIN,_a]"
        ]

case17 :: IO String
case17 = find_errors path17

path22 :: String
path22 = "Tests/train-station-err11.tex"

result22 :: String
result22 = unlines 
        [  "error 47:15:\n    event(s) leave have indices and require witnesses"
        ]

case22 :: IO String
case22 = find_errors path22
        
path18 :: String
path18 = "Tests/train-station-err9.tex"

result18 :: String
result18 = unlines 
        [  "error 68:2:\n    expression has type incompatible with its expected type:"
        ,  "  expression: (dom loc)"
        ,  "  actual type: \\set [\\TRAIN]"
        ,  "  expected type: \\Bool "
        ,  ""
        ,  "error 73:3:\n    expression has type incompatible with its expected type:"
        ,  "  expression: (union in (mk-set t))"
        ,  "  actual type: \\set [\\TRAIN]"
        ,  "  expected type: \\Bool "
        ,  ""
        ,  "error 118:3:\n    expression has type incompatible with its expected type:"
        ,  "  expression: t"
        ,  "  actual type: \\TRAIN"
        ,  "  expected type: \\Bool "
        ,  ""
        ,  "error 123:2:\n    expression has type incompatible with its expected type:"
        ,  "  expression: empty-set"
        ,  "  actual type: \\set [_a]"
        ,  "  expected type: \\Bool "
        ,  ""
        ]

case18 :: IO String
case18 = find_errors path18

path21 :: FilePath
path21 = "tests/train-station-err10.tex"

case21 :: IO String
case21 = find_errors path21

result21 :: String
result21 = unlines
    [ "Theory imported multiple times"
    , "error 129:1:\n\t\"sets\"\n"
    , "error 130:12:\n\t\"sets\"\n"
    , "error 131:12:\n\t\"sets\"\n\n"
    ]
