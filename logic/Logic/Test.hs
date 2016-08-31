{-# LANGUAGE OverloadedStrings,TypeFamilies #-}
module Logic.Test where

    -- Modules
import Logic.Expr hiding (field)
import Logic.Expr.Const
import Logic.Expr.Parser
import Logic.Proof.Monad
import Logic.QuasiQuote hiding (var)
import Logic.Test.Stable
import Logic.Theories
import Logic.Theory
import Logic.Theories.SetTheory

import Z3.Z3

    -- Libraries
import Control.Lens hiding (lifted,Context,Const)
import Control.Monad
import Control.Precondition

import Data.Hashable
import Data.Map hiding ( map, union, member )
import qualified Data.Map as M
import Data.PartialOrd
import qualified Data.Set as S

import Test.QuickCheck
import Test.QuickCheck.AxiomaticClass
import Test.QuickCheck.Gen
import Test.QuickCheck.Random
import Test.QuickCheck.Regression
import Test.QuickCheck.Report

import Test.UnitTest hiding (name)

import Utilities.MapSyntax
import Utilities.Syntactic

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
                        RecordSort m -> 
                            replicateM (size m) arbitrary
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

prop_unicity_counter_example :: Property
prop_unicity_counter_example = regression 
    (isNothing . prop_yield_same_type . (each %~ GType))
    [   (array real (Gen (z3Sort "C" "C" 1) [gB]),gB)
    ]

return []

test_case :: TestCase
test_case = test

test :: TestCase
test = test_cases "genericity" 
        [ aCase "unification, t0" (return $ unify gtype stype0) (Just $ fromList [(vC1,int), (vB1,real)])
        , aCase "unification, t1" (return $ unify gtype stype1) (Just $ fromList [(vC1,set_type int), (vB1,real)])
        , aCase "unification, t2" (return $ unify gtype stype2) Nothing
        , aCase "unification, t3" (return $ unify gtype0 gtype1) (Just $ fromList [(vA1,set_type int), (vA2,real)])
        , aCase "unification, t4" (return $ unify gtype1 gtype2) Nothing
        , aCase "unification, t5" (return $ unify gtype0 gtype2) (Just $ fromList [(vA2,set_type real), (vA1,set_type $ set_type real)])
        , aCase "unification, t6" (return $ unify int gC) (Just $ fromList [(vC2,int)])
        , aCase "type instantiation" (return $ instantiate (fromList [(c, set_type int),(b,real)]) gtype) stype1
--        ,  aCase "type inference 0" case2 result2
        , aCase "type inference 1" case3 result3
--        , aCase "type inference 2" case4 result4
                -- does not work because we cannot match 
                -- a generic parameter to a generic expression
        , aCase "type inference 3" case5 result5
        , aCase "type inference 4" case6 result6
        , aCase "type inference 5" case7 result7
        , QuickCheckProps "instantiation of unified types is unique" $(quickCheckWrap 'prop_unifying_yields_unified_type)
        , QuickCheckProps "common type is symmetric" $(quickCheckWrap 'prop_common_symm)
        , stringCase "common type is symmetric (counter-example)" (return $ show counter_ex_common_symm) "True"
        , stringCase "common type is symmetric (counter-example 2)" (return $ show counter_ex2_common_symm) "True"
        , QuickCheckProps "instantiation of unified types is unique (counter examples)" 
                $(quickCheckWrap 'prop_unicity_counter_example)
--        [ aCase "types unify with self" (check_prop prop_type_unifies_with_self) True
        , QuickCheckProps "type mapping are acyclic" $(quickCheckWrap 'prop_type_mapping_acyclic)
        , stringCase "one-point rule simplification on existentials" case8 result8
        , QuickCheckProps "axioms of type classes PreOrd and PartialOrd" case9
        , stringCase "Record expressions" case10 result10
        , stringCase "Record sets" case11 result11
        , aCase "Record sets in Z3" case12 result12
        , aCase "Syntax for record literals" case13 result13
        , aCase "Syntax for record update" case14 result14
        , aCase "Record syntax: empty record" case15 result15
        , aCase "Records: multiple updates" case16 result16
        , aCase "Records sets syntax" case17 result17
        , aCase "QuasiQuotes with proof monads" case18 result18
        , aCase "QuasiQuotes with proof monads and set theory" case19 result19
        , aCase "QuasiQuotes with proof monads and assumptions" case20 result20
        , aCase "Records lookup syntax" case21 result21
        , aCase "Proofs with record lookup" case22 result22
        , aCase "Testing the parser (\\qforall{x,y}{}{x = y})" case23 result23
        , aCase "Testing the parser (\\neg (-2) = 2)" case24 result24
        ]
    where
        reserved x n = addSuffix ("@" ++ show n) (fromString'' x)
        vA1 = reserved "a" 1
        vA2 = reserved "a" 2
        vB1 = reserved "b" 1
        vC1 = reserved "c" 1
        vC2 = reserved "c" 2
        fun_sort = z3Sort "\\pfun" "fun" 2
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
case3 = return $ specialize (fromList [(a,gB)]) $ funApp union [x3,x4]
result3 = funApp (mk_fun' [gB] "union" [set_type gB,set_type gB] $ set_type gB) [x3,x4] 
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
pp = funApp member [funApp union [x1,x2], specialize (fromList [(a,set_type gA)]) $ funApp union [x3,x4]]

qq :: Expr
qq = funApp member [funApp union [x1,x2], funApp (mk_fun' [set_type gA] "union" [set_type $ set_type gA,set_type $ set_type gA] $ set_type $ set_type gA) [x3,x4]]
p :: Expr
p = funApp member [funApp union [x1,x2], specialize (fromList [(a,set_type $ gA)]) $ funApp union [x3,x4]]
q :: Expr
q = funApp member [funApp union [x1,x2], funApp (mk_fun' [set_type gA] "union" [set_type $ set_type gA, set_type $ set_type gA] $ set_type $ set_type gA) [x3,x4]]

case7   :: IO ExprP
result7 :: ExprP
(case7, result7) = 
        ( return (x `zelem` zempty_set)
        , Right $ funApp (mk_fun' [train] "elem" [train,set_type train] bool) [either (error "expecting right") id x,empty_set_of_train]
        )
    where
        train = Gen (z3Sort "\\train" "train" 0) []
        (x,_) = var "x" train
        empty_set_of_train = funApp (mk_fun' [train] "empty-set" [] $ set_type train) []

result8 :: String
result8 = unlines
    [ "(and p q)"
    , "p"
    , "(and (or (and p q) p q (= 7 87)) q)"
    , "(and p q)"
    , "p"
    , "q"
    , "(= 7 87)"
    , "q"
    , "(= 7 87)"
    ]

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
        e = fromRight' $ mzexists [z_decl] mztrue $ 
                            (p `mzor` e0 `mzor` (mzeq z z7)) 
                    `mzand` (q `mzor` (mzeq z z87))
        e' = one_point_rule e

case9 :: (PropName -> Property -> IO (a, Result))
      -> IO ([a], Bool)
case9 = $(quickCheckClassesWith [''PreOrd,''PartialOrd])

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
instance TypeAnnotationPair Integer Integer where
    strippedType = id
instance TypeSystem Integer where
    make_type s = product . (toInteger (hash s):)
instance Typed Integer where
    type TypeOf Integer = Integer
    type_of = id

case10 :: IO String
case10 = return $ z3_code $ _goal $ runSequent' $ do
        let t = record_type $ runMap' $ do
                x ## int
                b ## bool
            x = [field|x|]
            b = [field|b|]
        v1 <- declare "v1" t
        v2 <- declare "v2" t
        assume "v1: x:=7, b:=true" $ v1 .=. zrecord' (x ## 7 >> b ## mztrue)
        assume "v2: v1[x:=7]" $ v2 .=. zrec_update v1 (x ## 7)
        check $ v1 .=. v2

case11 :: IO String
case11 = return $ z3_code $ _goal $ runSequent' $ do
        include set_theory
        include basic_theory
        let t = record_type $ runMap' $ do
                x ## int
                b ## bool
            x = [field|x|]
            b = [field|b|]
        v1 <- declare "v1" t
        v2 <- declare "v2" t
        assume "v1: x:=7, b:=true" $ v1 .=. zrecord' (x ## 7 >> b ## mztrue)
        assume "v2 \\in ['x : {7}, 'b : (all:\\Bool)]" $ v2 `zelem`
                    mk_zrecord_set (x ## zmk_set 7 >> b ## zcast (set_type bool) zset_all)
        check $ v1 .=. v2

case12 :: IO Validity
case12 = discharge ("case12") $ _goal $ runSequent' $ do
        include set_theory
        include basic_theory
        let t = record_type $ runMap' $ do
                x ## int
                b ## bool
            x = [field|x|]
            b = [field|b|]
        v1 <- declare "v1" t
        v2 <- declare "v2" t
        assume "v1: x:=7, b:=true" $ v1 .=. zrecord' (x ## 7 >> b ## mztrue)
        assume "v2 \\in ['x : {7}, 'b : {true}]" $
                v2 `zelem` mk_zrecord_set (x ## zmk_set 7 >> b ## zmk_set mztrue)
        check $ v1 .=. v2

result12 :: Validity
result12 = Valid

case13 :: IO Expr
case13 = do
        return $ getExpr $ c [expr| [ 'foo := 7, 'bar := \{ 1,2 \} ] |]
    where
        c = ctx $ expected_type .= Nothing

result13 :: Expr
result13 = fromRight' $ zrecord' (foo ## 7 >> bar ## zset_enum [1,2])
    where
        foo = Field [smt|foo|]
        bar = Field [smt|bar|]

case14 :: IO Expr
case14 = return $ getExpr $ c [expr| r [ 'foo := 7, 'bar := \{ 1,2 \} ] |]
    where
        c = ctx $ do
                decls %= M.union (symbol_table [(Var r t)])
                expected_type .= Nothing
        t = record_type $ runMap' $ do
                x ## int
                bar ## bool
        r = [smt|r|]
        x = [field|x|]
        bar = [field|bar|]

result14 :: Expr
result14 = fromRight' $ zrec_update r (foo ## 7 >> bar ## zset_enum [1,2])
    where
        r  = Right $ Word $ Var r' $ record_type $ M.fromList 
                    [ (bar,bool)
                    , (x,int) ]
        r'  = [smt|r|]
        x   = [field|x|]
        foo = [field|foo|]
        bar = [field|bar|]

    -- empty record literal
case15 :: IO Expr
case15 = do
        return $ getExpr $ c [expr| [  ] |]
    where
        c = ctx $ expected_type .= Nothing

result15 :: Expr
result15 = fromRight' $ zrecord' (return ())

    -- multiple record updates
case16 :: IO Expr
case16 = return $ getExpr $ c [expr| r [ 'foo := 7 ] [ 'bar := \{ 1,2 \} ] |]
    where
        c = ctx $ do
                decls %= M.union (symbol_table [(Var r t)])
                expected_type .= Nothing
        t = record_type $ runMap' $ do
                x ## int
                bar ## bool
        r = [smt|r|]
        x = [field|x|]
        bar = [field|bar|]

result16 :: Expr
result16 = fromRight' $ zrec_update (zrec_update r (foo ## 7)) (bar ## zset_enum [1,2])
    where
        r  = Right $ Word $ Var r' $ record_type $ M.fromList 
                    [ (bar,bool)
                    , (x,int) ]
        r'  = [smt|r|]
        x   = [field|x|]
        foo = [field|foo|]
        bar = [field|bar|]

-- field lookup
-- record set

case17 :: IO Expr
case17 = do
        return $ getExpr $ 
            c [expr| r [ 'foo := 7, 'bar := \{ 1,2 \} ] \in [ 'foo : \Int, 'x : \Int, 'bar : \pow.\Int ] |]
    where
        c = ctxWith [set_theory] $ do
                decls %= M.union (symbol_table 
                    [Var r t
                    ,Var intV $ set_type int])
                free_dummies .= True
                dum_ctx %= insert_symbol (Var r t')
        t = record_type $ runMap' $ do
                x ## int
                bar ## bool
        t' = record_type $ runMap' $ do
                x ## int
                foo ## int
                bar ## set_type int
        r = [smt|r|]
        x = [field|x|]
        intV = [tex|\Int|]
        bar = [field|bar|]
        foo = [field|foo|]


result17 :: Expr
result17 = fromRight' $ rec `zelem` set
    where
        rec = zrec_update r (foo ## 7 >> bar ## zset_enum [1,2])
        set = mk_zrecord_set (do foo ## zset_all' int; x ## zset_all' int; bar ## zpow_set (zset_all' int))
        r' = [smt|r|]
        r  = Right $ Word $ Var r' $ record_type $ M.fromList 
                    [ (bar,bool)
                    , (x,int) ]
        x = [field|x|]
        bar = [field|bar|]
        foo = [field|foo|]

case18 :: IO Validity
case18 = discharge("case13") $ _goal $ runSequent' $ do
    declare "x" int
    checkQ $ [expr| x = x |]

result18 :: Validity
result18 = Valid

case19 :: IO Validity
case19 = discharge("case14") $ _goal $ runSequent' $ do
    declare "x" int
    include set_theory
    checkQ $ [expr| x \in \{x\} |]

result19 :: Validity
result19 = Valid

case20 :: IO Validity
case20 = discharge("case15") $ _goal $ runSequent' $ do
    declare "x" int
    assumeQ "x = x" [expr| x = x |]
    checkQ $ [expr| \neg x = x |]

result20 :: Validity
result20 = Invalid

case21 :: IO Expr
case21 = return $ getExpr $ c [expr| r.'x = 7 |]
    where
        c = ctx $ do
                decls %= M.union (symbol_table [(Var r t)])
                expected_type .= Nothing
        t = record_type $ runMap' $ do
                x ## int
                bar ## bool
        r = [smt|r|]
        x = [field|x|]
        bar = [field|bar|]

result21 :: Expr
result21 = Record (FieldLookup r x) int  `zeq` zint 7
    where
        r  = Word $ Var r' $ record_type $ M.fromList 
                    [ (bar,bool)
                    , (x,int) ]
        r'  = [smt|r|]
        x   = [field|x|]
        bar = [field|bar|]

case22 :: IO Validity
case22 = discharge "case22" $ _goal $ runSequent' $ do
    let t = record_type $ runMap' $ do
                x ## bool
                bar ## int
        x   = [field|x|]
        bar = [field|bar|]
    declare "r" t
    assumeQ "r = [ 'x := \true, 'bar := 7 ]" [expr| r = [ 'x := \true, 'bar := 7 ] |]
    checkQ  [expr| r.'bar = 8 |]

result22 :: Validity
result22 = Invalid

case23 :: IO UntypedExpr
case23 = return $ either show_error id $ untypedExpression
    where
        expr = "\\qforall{x,y}{}{x = y}"
        stringLi = asStringLi (mkLI expr) expr
        setting = theory_setting basic_theory
        untypedExpression = parse_expression setting stringLi
        show_error = \x -> error ("couldn't parse expression:\n" ++ show_err x)

result23 :: UntypedExpr
result23 = zforall [x',y'] ztrue (fun2 (zeq_fun gA) x y)
    where
        x' = z3Var "x" ()
        y' = z3Var "y" ()
        x = Word x'
        y = Word y'

case24 :: IO UntypedExpr
case24 = return $ either show_error id $ untypedExpression
    where
        expr = "\\neg (-2) = 2"
        stringLi = asStringLi (mkLI expr) expr
        setting = theory_setting' preludeTheories
        untypedExpression = parse_expression setting stringLi
        show_error = \x -> error ("couldn't parse expression:\n" ++ show_err x)

result24 :: UntypedExpr
result24 = znot (fun2 (zeq_fun gA) (zopp $ zint 2) (zint 2))
