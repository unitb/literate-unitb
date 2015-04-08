{-# LANGUAGE TypeSynonymInstances #-}
module Logic.TestGenericity where

    -- Modules
import Logic.Expr

import Theories.SetTheory

    -- Libraries
import Control.Monad

import Data.Map hiding ( map )
import qualified Data.Set as S

import Test.QuickCheck

import Tests.UnitTest

left :: Type -> Type
left  = suffix_generics "1"

right :: Type -> Type
right = suffix_generics "2"

prop_yield_same_type :: (Type,Type) -> Maybe (Type,Type)
prop_yield_same_type (t0,t1) = 
        maybe (Just (t0,t1)) (const Nothing) (do
            un <- unify t0 t1
            let ct0 = instantiate un $ left t0
                ct1 = instantiate un $ right t1
            return (ct0 == ct1))

prop_unifying_yields_unified_type :: (Type, Type) -> Property
prop_unifying_yields_unified_type (t0,t1) = 
        match ==>
        maybe True (const False) (prop_yield_same_type (t0,t1))
    where
        match = unify t0 t1 /= Nothing

prop_common_symm :: GenericType -> GenericType -> Bool
prop_common_symm t0 t1 = common t0 t1 == common t1 t0 

counter_ex2_common_symm :: Bool
counter_ex2_common_symm = 
        prop_common_symm t0 t1
    where
        _a = GENERIC "a"
        pfun = fun_type
        t0 = array _a _a
        t1 = array _a (pfun (pfun _a int) real)


counter_ex_common_symm :: Bool
counter_ex_common_symm = prop_common_symm t0 t1
    where
        _a = GENERIC "a"
        _b = GENERIC "b"
        _c = GENERIC "c"
        s2 = Sort "D" "D" 2
        _s2 = DefSort "E" "E" ["a","b"] $ array (GENERIC "a") (GENERIC "b")
        empty x y = Gen (USER_DEFINED s2 [x,y])
        t0 = fun_type _b _a
        pfun = fun_type
        set = set_type
        t1 = (pfun (pfun int (pfun _c (set t3))) _c)
        t2 = (array (empty real (array (array bool _b) _c)) bool)
        t3 = (set (pfun real (set (set (array (pfun real t2) bool)))))


prop_type_unifies_with_self :: Type -> Bool
prop_type_unifies_with_self t = unify t t /= Nothing

mapping_acyclic :: (Type,Type) -> Maybe (Type,Type)
mapping_acyclic (t0,t1) =
        maybe (Just (t0,t1)) (const Nothing) (do
            un <- unify t0 t1
            return $ S.null (keysSet un `S.intersection` S.unions (map generics $ elems un)))

prop_type_mapping_acyclic :: (Type, Type) -> Property
prop_type_mapping_acyclic (t0,t1) = 
        match ==>
        maybe True (const False) (mapping_acyclic (t0,t1))
    where
        match = unify t0 t1 /= Nothing
        
check_prop :: Testable prop => prop -> IO Bool
check_prop p = do
        r <- quickCheckResult p
        case r of
            Success _ _ _ -> return True
            _             -> return False

instance Arbitrary Type where
    arbitrary = oneof (
                [ return bool
                , return int
                , return real
                ] ++ concat (take 2 $ repeat
                [ do
                    t0 <- arbitrary
                    t1 <- arbitrary
                    return $ array t0 t1
                , oneof gen_prm
                , do
                    s  <- oneof sorts
                    ts <- case s of
                        Sort _ _ n -> 
                            replicateM n arbitrary
                        DefSort _ _ args _ -> 
                            replicateM (length args) arbitrary
                        IntSort -> 
                            return []
                        RealSort ->
                            return []
                        BoolSort -> 
                            return []
                        Datatype _ _ _ -> error "Type.arbitrary: impossible"
                    return $ Gen $ USER_DEFINED s ts
                , do
                    t <- arbitrary
                    return $ set_type t
                , do
                    t0 <- arbitrary
                    t1 <- arbitrary
                    return $ fun_type t0 t1
                ] ) )
        where
            sorts = map return
                [ Sort "A" "A" 0
                , Sort "B" "B" 1
                , Sort "C" "C" 1
                , Sort "D" "D" 2
                , DefSort "E" "E" ["a","b"] $ array (GENERIC "a") (GENERIC "b")
                , BoolSort
                , IntSort
                , RealSort
                ]
            gen_prm = map return
                [ GENERIC "a"
                , GENERIC "b"
                , GENERIC "c"
                ]
    shrink (GENERIC _)  = []
    shrink (VARIABLE _) = []
    shrink (Gen (USER_DEFINED s ts)) = ts ++ do
            ts <- mapM shrink ts
            return $ t ts
        where
            t ts = (Gen (USER_DEFINED s ts))

unicity_counter_example :: [(Type,Type)]
unicity_counter_example = 
    [   (array real (Gen $ USER_DEFINED (Sort "C" "" 1) [GENERIC "b"]),GENERIC "b")
    ]

test_case :: TestCase
test_case = test

test :: TestCase
test = test_cases "genericity" (
        [ Case "unification, t0" (return $ unify gtype stype0) (Just $ fromList [("c@1",int), ("b@1",real)])
        , Case "unification, t1" (return $ unify gtype stype1) (Just $ fromList [("c@1",set_type int), ("b@1",real)])
        , Case "unification, t2" (return $ unify gtype stype2) Nothing
        , Case "unification, t3" (return $ unify gtype0 gtype1) (Just $ fromList [("a@1",set_type int), ("a@2",real)])
        , Case "unification, t4" (return $ unify gtype1 gtype2) Nothing
        , Case "unification, t5" (return $ unify gtype0 gtype2) (Just $ fromList [("a@2",set_type real), ("a@1",set_type $ set_type real)])
        , Case "unification, t6" (return $ unify int (GENERIC "c")) (Just $ fromList [("c@2",int)])
        , Case "type instantiation" (return $ instantiate (fromList [("c", set_type int),("b",real)]) gtype) stype1
--        ,  Case "type inference 0" case2 result2
        , Case "type inference 1" case3 result3
--        , Case "type inference 2" case4 result4
                -- does not work because we cannot match 
                -- a generic parameter to a generic expression
        , Case "type inference 3" case5 result5
        , Case "type inference 4" case6 result6
        , Case "type inference 5" case7 result7
        , Case "instantiation of unified types is unique" (check_prop prop_unifying_yields_unified_type) True
        , Case "common type is symmetric" (check_prop prop_common_symm) True
        , StringCase "common type is symmetric (counter-example)" (return $ show counter_ex_common_symm) "True"
        , StringCase "common type is symmetric (counter-example 2)" (return $ show counter_ex2_common_symm) "True"
        ] ++
        map (\ce -> Case 
                "instantiation of unified types is unique (counter examples)" 
                (return $ prop_yield_same_type ce) 
                Nothing
            ) unicity_counter_example ++ 
--        [ Case "types unify with self" (check_prop prop_type_unifies_with_self) True
        [ Case "type mapping are acyclic" (check_prop prop_type_mapping_acyclic) True
        , StringCase "one-point rule simplification on existentials" case8 result8
        ] )
    where
        fun_sort = Sort "\\tfun" "fun" 2
        gtype    = Gen $ USER_DEFINED fun_sort [GENERIC "c", set_type $ GENERIC "b"]
        
        stype0   = Gen $ USER_DEFINED fun_sort [int, set_type real]
        stype1   = Gen $ USER_DEFINED fun_sort [set_type int, set_type real]
        stype2   = Gen $ USER_DEFINED fun_sort [set_type int, real]
        
        gtype0   = Gen $ USER_DEFINED fun_sort [gA, set_type real]
        gtype1   = Gen $ USER_DEFINED fun_sort [set_type int, set_type gA]
        gtype2   = Gen $ USER_DEFINED fun_sort [set_type gA, gA]
        gA = GENERIC "a"

case3   :: IO Expr
result3 :: Expr
case5   :: IO Expr
result5 :: Expr
case6   :: IO Expr
result6 :: Expr
( case3,result3,case5,result5,case6,result6 ) = ( 
                    return $ specialize (fromList [("a",GENERIC "b")]) $ FunApp union [x3,x4]
                    , FunApp (mk_fun [gB] "union" [set_type gB,set_type gB] $ set_type gB) [x3,x4] 
                    , return p
                    , q
                    , return pp
                    , qq
                    )
    where
        gA = GENERIC "a"
        gB = GENERIC "b"
        x1 = Word $ Var "x1" (set_type int)
        x2 = Word $ Var "x2" (set_type int)
        x3 = Word $ Var "x3" (set_type $ set_type int)
        x4 = Word $ Var "x3" (set_type $ set_type int)
        -- y  = Word $ Var "y" int
        -- z  = Word $ Var "z" real
        union  = mk_fun [gA] "union" [set_type gA,set_type gA] $ set_type gA
        member = mk_fun [gA] "member" [gA, set_type gA] bool
        pp = FunApp member [FunApp union [x1,x2], specialize (fromList [("a",set_type $ GENERIC "a")]) $ FunApp union [x3,x4]]
        qq = FunApp member [FunApp union [x1,x2], FunApp (mk_fun [set_type gA] "union" [set_type $ set_type gA,set_type $ set_type gA] $ set_type $ set_type gB) [x3,x4]]
        p = FunApp member [FunApp union [x1,x2], specialize (fromList [("a",set_type $ GENERIC "a")]) $ FunApp union [x3,x4]]
        q = FunApp member [FunApp union [x1,x2], FunApp (mk_fun [set_type gA] "union" [set_type gA,set_type gA] $ set_type gA) [x3,x4]]

case7   :: IO ExprP
result7 :: ExprP
(case7, result7) = 
        ( return (x `zelem` zempty_set)
        , Right $ FunApp (mk_fun [train] "elem" [train,set_type train] bool) [either (error "expecting right") id x,empty_set_of_train]
        )
    where
        train = Gen $ USER_DEFINED (Sort "\train" "train" 0) []
        (x,_) = var "x" train
        empty_set_of_train = FunApp (mk_fun [train] "empty-set" [] $ set_type train) []

result8 :: String
result8 = unlines
    [ "(and p q)"
    , "(and p (= 87 87))"
    , "(and (or (and p q)"
    , "         (and p (= 87 87))"
    , "         (and (= 7 7) q)"
    , "         (and (= 7 7) (= 7 87)))"
    , "     q)"
    , "(and (or (and p q)"
    , "         (and p (= 87 87))"
    , "         (and (= 7 7) q)"
    , "         (and (= 7 7) (= 7 87)))"
    , "     (= 87 87))"
    , "(and (= 7 7) q)"
    , "(and (= 7 7) (= 7 87))"
    ]

fromRight :: Either a b -> b
fromRight (Right x) = x
fromRight _ = error "expecting right"

case8 :: IO String
case8 = return $ unlines $ map pretty_print' $ disjuncts e'
    where
        (z,z_decl) = var "z" int
        z7  = mzint 7
        z87 = mzint 87
        (p,_) = var "p" bool
        (q,_) = var "q" bool
        e0 :: ExprP
        e0 = mzexists [z_decl] mztrue $ 
                            (p `mzor` (mzeq z z7)) 
                    `mzand` (q `mzor` (mzeq z z87))
        e = fromRight $ mzexists [z_decl] mztrue $ 
                            (p `mzor` e0 `mzor` (mzeq z z7)) 
                    `mzand` (q `mzor` (mzeq z z87))
        e' = one_point_rule e
