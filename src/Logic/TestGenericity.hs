{-# LANGUAGE OverloadedStrings,TypeFamilies #-}
module Logic.TestGenericity where

    -- Modules
import Logic.Expr
import Logic.Expr.Const
import Logic.Proof ()

import Theories.SetTheory

    -- Libraries
import Control.Lens hiding (lifted,Context,Const)
import Control.Monad

import Data.Hashable
import Data.Map hiding ( map, union, member )
import Data.PartialOrd
import qualified Data.Set as S

import Test.QuickCheck
import Test.QuickCheck.AxiomaticClass
import Test.QuickCheck.Gen
import Test.QuickCheck.Random
import Test.QuickCheck.Regression
import Test.QuickCheck.Report ()

import Tests.UnitTest


left :: Type -> Type
left  = suffix_generics "1"

right :: Type -> Type
right = suffix_generics "2"

prop_yield_same_type :: (GType,GType) -> Maybe (GType,GType)
prop_yield_same_type (GType t0,GType t1) = 
        maybe (Just (GType t0, GType t1)) (const Nothing) (do
            un <- unify t0 t1
            let ct0 = instantiate un $ left t0
                ct1 = instantiate un $ right t1
            return (ct0 == ct1))

prop_unifying_yields_unified_type :: (GType, GType) -> Property
prop_unifying_yields_unified_type (GType t0, GType t1) = 
        match ==>
        maybe True (const False) (prop_yield_same_type (GType t0,GType t1))
    where
        match = unify t0 t1 /= Nothing

prop_common_symm :: GType -> GType -> Bool
prop_common_symm (GType t0) (GType t1) = common t0 t1 == common t1 t0 

counter_ex2_common_symm :: Bool
counter_ex2_common_symm = 
        prop_common_symm t0 t1
    where
        _a = gA
        pfun = fun_type
        t0 = GType $ array _a _a
        t1 = GType $ array _a (pfun (pfun _a int) real)


counter_ex_common_symm :: Bool
counter_ex_common_symm = prop_common_symm (GType t0) (GType t1)
    where
        _a = gA
        _b = gB
        _c = gC
        a = fromString'' "a"
        b = fromString'' "b"
        s2 = Sort (fromString'' "D") (fromString'' "D") 2
        _s2 = DefSort (fromString'' "E") (fromString'' "E") [a,b] $ array gA gB
        empty x y = Gen s2 [x,y]
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

newtype GType = GType { getType :: Type }
    deriving (Show,Eq)

instance Arbitrary GType where
    arbitrary = GType <$> oneof (
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
                    return $ Gen s ts
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
                [ z3Sort "A" "A" 0
                , z3Sort "B" "B" 1
                , z3Sort "C" "C" 1
                , z3Sort "D" "D" 2
                , z3DefSort "E" "E" ["a","b"] $ array gA gB
                , BoolSort
                , IntSort
                , RealSort
                ]
            gen_prm = map return
                [ gA
                , gB
                , gC
                ]
    shrink (GType (GENERIC _))  = []
    shrink (GType (VARIABLE _)) = []
    shrink (GType (Gen s ts)) = map GType ts ++ do
            ts <- mapM (shrink . GType) ts
            let t = Gen s $ map getType ts
            return $ GType t

unicity_counter_example :: [(Type,Type)]
unicity_counter_example = 
    [   (array real (Gen (z3Sort "C" "C" 1) [gB]),gB)
    ]

test_case :: TestCase
test_case = test

test :: TestCase
test = test_cases "genericity" (
        [ Case "unification, t0" (return $ unify gtype stype0) (Just $ fromList [(vC1,int), (vB1,real)])
        , Case "unification, t1" (return $ unify gtype stype1) (Just $ fromList [(vC1,set_type int), (vB1,real)])
        , Case "unification, t2" (return $ unify gtype stype2) Nothing
        , Case "unification, t3" (return $ unify gtype0 gtype1) (Just $ fromList [(vA1,set_type int), (vA2,real)])
        , Case "unification, t4" (return $ unify gtype1 gtype2) Nothing
        , Case "unification, t5" (return $ unify gtype0 gtype2) (Just $ fromList [(vA2,set_type real), (vA1,set_type $ set_type real)])
        , Case "unification, t6" (return $ unify int gC) (Just $ fromList [(vC2,int)])
        , Case "type instantiation" (return $ instantiate (fromList [(c, set_type int),(b,real)]) gtype) stype1
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
                (return $ prop_yield_same_type $ ce & each %~ GType) 
                Nothing
            ) unicity_counter_example ++ 
--        [ Case "types unify with self" (check_prop prop_type_unifies_with_self) True
        [ Case "type mapping are acyclic" (check_prop prop_type_mapping_acyclic) True
        , StringCase "one-point rule simplification on existentials" case8 result8
        , Case "axioms of type classes PreOrd and PartialOrd" case9 True
        ] )
    where
        reserved x n = addSuffix ("@" ++ show n) (fromString'' x)
        vA1 = reserved "a" 1
        vA2 = reserved "a" 2
        vB1 = reserved "b" 1
        vC1 = reserved "c" 1
        vC2 = reserved "c" 2
        fun_sort = z3Sort "\\tfun" "fun" 2
        gtype    = Gen fun_sort [z3GENERIC "c", set_type $ z3GENERIC "b"]
        
        stype0   = Gen fun_sort [int, set_type real]
        stype1   = Gen fun_sort [set_type int, set_type real]
        stype2   = Gen fun_sort [set_type int, real]
        
        gtype0   = Gen fun_sort [gA, set_type real]
        gtype1   = Gen fun_sort [set_type int, set_type gA]
        gtype2   = Gen fun_sort [set_type gA, gA]

case3   :: IO Expr
result3 :: Expr
case5   :: IO Expr
result5 :: Expr
case6   :: IO Expr
result6 :: Expr
case3 = return $ specialize (fromList [(a,gB)]) $ FunApp union [x3,x4]
result3 = FunApp (mk_fun' [gB] "union" [set_type gB,set_type gB] $ set_type gB) [x3,x4] 
case5 = return $ p
result5 = q
case6 = return $ pp
result6 = qq

x1 :: Expr
x1 = Word $ z3Var "x1" (set_type int)
x2 :: Expr
x2 = Word $ z3Var "x2" (set_type int)
x3 :: Expr
x3 = Word $ z3Var "x3" (set_type $ set_type int)
x4 :: Expr
x4 = Word $ z3Var "x3" (set_type $ set_type int)
-- y  = Word $ Var "y" int
-- z  = Word $ Var "z" real
union :: Fun
union  = mk_fun' [gA] "union" [set_type gA,set_type gA] $ set_type gA

member :: Fun
member = mk_fun' [gA] "member" [gA, set_type gA] bool

a :: InternalName
a = fromString'' "a"
b :: InternalName
b = fromString'' "b"
c :: InternalName
c = fromString'' "c"

pp :: Expr
pp = FunApp member [FunApp union [x1,x2], specialize (fromList [(a,set_type gA)]) $ FunApp union [x3,x4]]

qq :: Expr
qq = FunApp member [FunApp union [x1,x2], FunApp (mk_fun' [set_type gA] "union" [set_type $ set_type gA,set_type $ set_type gA] $ set_type $ set_type gA) [x3,x4]]
p :: Expr
p = FunApp member [FunApp union [x1,x2], specialize (fromList [(a,set_type $ gA)]) $ FunApp union [x3,x4]]
q :: Expr
q = FunApp member [FunApp union [x1,x2], FunApp (mk_fun' [set_type gA] "union" [set_type $ set_type gA, set_type $ set_type gA] $ set_type $ set_type gA) [x3,x4]]

case7   :: IO ExprP
result7 :: ExprP
(case7, result7) = 
        ( return (x `zelem` zempty_set)
        , Right $ FunApp (mk_fun' [train] "elem" [train,set_type train] bool) [either (error "expecting right") id x,empty_set_of_train]
        )
    where
        train = Gen (z3Sort "\\train" "train" 0) []
        (x,_) = var "x" train
        empty_set_of_train = FunApp (mk_fun' [train] "empty-set" [] $ set_type train) []

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

case9 :: IO Bool
case9 = $(quickCheckClasses [''PreOrd,''PartialOrd])

instance IsQuantifier Integer where
    merge_range = Str . show
    termType n = unGen arbitrary (mkQCGen $ fromInteger n) (fromInteger n)
    exprType n r t = unGen (oneof [arbitrary,return r,return t]) 
                (mkQCGen $ fromInteger n) (fromInteger n)
    qForall  = 1
    qExists  = 2
instance Tree Integer where
    as_tree' = return . Str . show
instance PrettyPrintable Integer where
    pretty = show
instance TypeSystem Integer where
    make_type s = product . (toInteger (hash s):)
instance Typed Integer where
    type TypeOf Integer = Integer

checkRegression :: Property
checkRegression = regression (uncurry axiom_derived_def_comparable)
                    [(x0,y0)]
    where
        x0 :: GenContext Integer Integer Integer
        x0 = Context {_genContextSorts = fromList [], _genContextConstants = fromList [(-1,Var 0 (-1))], _functions = fromList [], _definitions = fromList [(1,Def [0] 0 [] 0 (Lift (Const (IntVal (-1)) 0) 0))], _genContextDummies = fromList [(1,Var 1 (-1))]}
        y0 = Context {_genContextSorts = fromList [(Name {_backslash = True, _base = 'o' :| "-", _primes = 0, _suffix = "", _encoding = Z3Encoding},Sort (Name {_backslash = False, _base = '.' :| "", _primes = 0, _suffix = "", _encoding = LatexEncoding}) (InternalName "" (Name {_backslash = False, _base = '-' :| "", _primes = 0, _suffix = "", _encoding = Z3Encoding}) "") 1)], _genContextConstants = fromList [(0,Var (-1) 1)], _functions = fromList [(-1,Fun {_annotation = [], _funName = -1, lifted = Unlifted, _arguments = [], _result = 0})], _definitions = fromList [], _genContextDummies = fromList []}
