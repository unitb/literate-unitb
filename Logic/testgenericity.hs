module Logic.TestGenericity where

    -- Modules
import Logic.Const
import Logic.Expr
import Logic.Genericity

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
            let ct1 = instantiate un $ right t1
            return (ct0 == ct1))

prop_unifying_yields_unified_type :: (Type, Type) -> Property
prop_unifying_yields_unified_type (t0,t1) = 
        match ==>
        maybe True (const False) (prop_yield_same_type (t0,t1))
    where
        match = unify t0 t1 /= Nothing
        
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
                            forM [1 .. n] (\_ -> arbitrary)
                        DefSort _ _ args _ -> 
                            forM [1 .. length args] (\_ -> arbitrary)
                        IntSort -> 
                            return []
                        RealSort ->
                            return []
                        BoolSort -> 
                            return []
                        Datatype _ _ _ -> error "Type.arbitrary: impossible"
                    return $ USER_DEFINED s ts
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
                [ Sort "A" "" 0
                , Sort "B" "" 1
                , Sort "C" "" 1
                , Sort "D" "" 2
                , DefSort "E" "" ["a","b"] $ array (GENERIC "a") (GENERIC "b")
                , BoolSort
                , IntSort
                , RealSort
                ]
            gen_prm = map return
                [ GENERIC "a"
                , GENERIC "b"
                , GENERIC "c"
                ]

test_case :: TestCase
test_case = Case "genericity" test True

unicity_counter_example :: [(Type,Type)]
unicity_counter_example = 
    [   (array real (USER_DEFINED (Sort "C" "" 1) [GENERIC "b"]),GENERIC "b")
    ]

test :: IO Bool
test = test_cases (
        [  Case "unification, t0" (return $ unify gtype stype0) (Just $ fromList [("c@1",int), ("b@1",real)])
        ,  Case "unification, t1" (return $ unify gtype stype1) (Just $ fromList [("c@1",set_type int), ("b@1",real)])
        ,  Case "unification, t2" (return $ unify gtype stype2) Nothing
        ,  Case "unification, t3" (return $ unify gtype0 gtype1) (Just $ fromList [("a@1",set_type int), ("a@2",real)])
        ,  Case "unification, t4" (return $ unify gtype1 gtype2) Nothing
        ,  Case "unification, t5" (return $ unify gtype0 gtype2) (Just $ fromList [("a@2",set_type real), ("a@1",set_type $ set_type real)])
        ,  Case "unification, t6" (return $ unify int (GENERIC "c")) (Just $ fromList [("c@2",int)])
        ,  Case "type instantiation" (return $ instantiate (fromList [("c", set_type int),("b",real)]) gtype) stype1
--        ,  Case "type inference 0" case2 result2
        ,  Case "type inference 1" case3 result3
--        ,  Case "type inference 2" case4 result4
                -- does not work because we cannot match 
                -- a generic parameter to a generic expression
        ,  Case "type inference 3" case5 result5
        ,  Case "type inference 4" case6 result6
        ,  Case "type inference 5" case7 result7
        , Case "instantiation of unified types is unique" (check_prop prop_unifying_yields_unified_type) True
        ] ++
        map (\ce -> Case 
                "instantiation of unified types is unique (counter examples)" 
                (return $ prop_yield_same_type ce) 
                Nothing
            ) unicity_counter_example ++ 
--        [ Case "types unify with self" (check_prop prop_type_unifies_with_self) True
        [ Case "type mapping are acyclic" (check_prop prop_type_mapping_acyclic) True
        ] )
    where
        fun_sort = Sort "\\tfun" "fun" 2
        gtype    = USER_DEFINED fun_sort [GENERIC "c", set_type $ GENERIC "b"]
        
        stype0   = USER_DEFINED fun_sort [int, set_type real]
        stype1   = USER_DEFINED fun_sort [set_type int, set_type real]
        stype2   = USER_DEFINED fun_sort [set_type int, real]
        
        gtype0   = USER_DEFINED fun_sort [gA, set_type real]
        gtype1   = USER_DEFINED fun_sort [set_type int, set_type gA]
        gtype2   = USER_DEFINED fun_sort [set_type gA, gA]
        gA = GENERIC "a"

case3   :: IO Expr
result3 :: Expr
case5   :: IO Expr
result5 :: Expr
case6   :: IO Expr
result6 :: Expr
( case3,result3,case5,result5,case6,result6 ) = ( 
                    return $ specialize (fromList [("a",GENERIC "b")]) $ FunApp union [x3,x4]
                    , FunApp (Fun [gB] "union" [set_type gB,set_type gB] $ set_type gB) [x3,x4] 
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
        union  = Fun [gA] "union" [set_type gA,set_type gA] $ set_type gA
        member = Fun [gA] "member" [gA, set_type gA] bool
        pp = FunApp member [FunApp union [x1,x2], specialize (fromList [("a",set_type $ GENERIC "a")]) $ FunApp union [x3,x4]]
        qq = FunApp member [FunApp union [x1,x2], FunApp (Fun [set_type gA] "union" [set_type $ set_type gA,set_type $ set_type gA] $ set_type $ set_type gB) [x3,x4]]
        p = FunApp member [FunApp union [x1,x2], specialize (fromList [("a",set_type $ GENERIC "a")]) $ FunApp union [x3,x4]]
        q = FunApp member [FunApp union [x1,x2], FunApp (Fun [set_type gA] "union" [set_type gA,set_type gA] $ set_type gA) [x3,x4]]

case7   :: IO ExprP
result7 :: ExprP
(case7, result7) = 
        ( return (x `zelem` Right zempty_set)
        , Right $ FunApp (Fun [train] "elem" [train,set_type train] bool) [either (error "expecting right") id x,empty_set_of_train]
        )
    where
        train = USER_DEFINED (Sort "\train" "train" 0) []
        (x,_) = var "x" train
        empty_set_of_train = Const [train] "empty-set" $ set_type train