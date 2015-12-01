{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE LambdaCase         #-}
module Logic.Expr.Type where

    -- Modules
import Logic.Expr.Classes

    -- Libraries
import Control.DeepSeq
import Control.Lens hiding (List,elements)
import Control.Monad.Reader

import           Data.Data
import qualified Data.Set as S

import           GHC.Generics hiding (to)

import Language.Haskell.TH.Syntax

import           Test.QuickCheck

import           Utilities.Format
import           Utilities.Instances

class TypeOf a ~ TypeOf (TypeOf a) => Typed a where
    type TypeOf a :: *

referenced_types :: FOType -> S.Set FOType
referenced_types t@(FOT _ ts) = S.insert t $ S.unions $ map referenced_types ts

instance Typed GenericType where
    type TypeOf GenericType = GenericType

class (Ord a, Tree a, Show a, Typed a, TypeOf a ~ a) => TypeSystem a where
    type_cons :: a -> Maybe (TypeCons a)
    make_type :: Sort -> [a] -> a

instance TypeSystem GenericType where
    type_cons (Gen s xs) = Just (USER_DEFINED s xs)
    type_cons _          = Nothing
    make_type    = Gen

instance Typed FOType where
    type TypeOf FOType = FOType

instance TypeSystem FOType where
    type_cons (FOT s xs) = Just (USER_DEFINED s xs)
    make_type = FOT

instance Typed () where
    type TypeOf () = ()

instance TypeSystem () where
    type_cons () = Nothing
    make_type _ _ = ()

type Type = GenericType

data GenericType = 
        Gen Sort [GenericType] 
        | GENERIC String
        | VARIABLE String
    deriving (Eq, Ord, Typeable, Generic, Data)

data FOType      = FOT Sort [FOType]
    deriving (Eq, Ord, Typeable, Generic)

data TypeCons a = USER_DEFINED Sort [a]
    deriving (Eq, Ord, Show, Generic, Typeable)

instance Tree GenericType where
    as_tree' (Gen s ts) = cons_to_tree $ USER_DEFINED s ts
    as_tree' (GENERIC x)   = return $ Str x
    as_tree' (VARIABLE n)  = return $ Str $ "_" ++ n
    rewriteM f (Gen s ts) = do
            Gen s <$> traverse f ts
    rewriteM _ x@(VARIABLE _) = pure x
    rewriteM _ x@(GENERIC _)  = pure x

instance Tree FOType where
    as_tree' (FOT s ts) = cons_to_tree $ USER_DEFINED s ts
    rewriteM f (FOT s ts) = FOT s <$> traverse f ts

instance Lift GenericType where
    lift = defaultLift

as_generic :: FOType -> GenericType
as_generic (FOT s ts) = Gen s (map as_generic ts)

cons_to_tree :: Tree a => TypeCons a -> Reader OutputMode StrList
cons_to_tree (USER_DEFINED s []) = do
    opt <- ask
    let n = case opt of
                ProverOutput -> z3_name s
                UserOutput -> s^.name
    return $ Str n
cons_to_tree (USER_DEFINED s ts) = do
    opt <- ask
    let n = case opt of
                ProverOutput -> z3_name s
                UserOutput -> s^.name
    return $ List (Str n : map as_tree ts)

data Sort =
        BoolSort | IntSort | RealSort 
        | DefSort 
            String      -- Latex name
            String      -- Type name
            [String]    -- Generic Parameter
            GenericType -- Type with variables
        | Sort String String Int --[String]
        | Datatype 
            [String]    -- Parameters
            String      -- type name
            [(String, [(String,GenericType)])] 
                        -- alternatives and named components
    deriving (Eq, Ord, Show, Typeable, Data, Generic)

typeParams :: Sort -> Int
typeParams BoolSort = 0
typeParams IntSort  = 0
typeParams RealSort = 0
typeParams (Sort _ _ n) = n
typeParams (DefSort _ _ ps _) = length ps
typeParams (Datatype xs _ _)  = length xs

instance Show FOType where
    show (FOT s []) = (z3_name s)
    show (FOT s ts) = format "{0} {1}" (z3_name s) ts

instance Show GenericType where
    show (GENERIC n)         = format "_{0}" n 
    show (VARIABLE n)        = format "'{0}" n 
    show (Gen s []) = s^.name
    show (Gen s ts) = format "{0} {1}" (s^.name) ts

instance HasName Sort String where
    name = to $ \case 
        (Sort x _ _) -> x
        (DefSort x _ _ _) -> x
        (Datatype _ x _)  -> x
        BoolSort   -> "\\Bool"
        IntSort    -> "\\Int"
        RealSort   -> "\\Real"

instance Named Sort where
    decorated_name' s = do
        opt <- ask
        case opt of
            ProverOutput -> return $ z3_name s
            UserOutput -> return $ s^.name

    z3_name (Sort _ x _) = x
    z3_name (DefSort _ x _ _) = x
    z3_name (Datatype _ x _)  = x
    z3_name BoolSort   = "Bool"
    z3_name IntSort    = "Int"
    z3_name RealSort   = "Real"

instance Lift Sort where
    lift = defaultLift

pair_sort :: Sort
pair_sort = -- Sort "Pair" "Pair" 2
               Datatype ["a","b"] "Pair" 
                    [ ("pair", 
                        [ ("first",  GENERIC "a")
                        , ("second", GENERIC "b") ]) ]


pair_type :: TypeSystem t => t -> t -> t
pair_type x y = make_type pair_sort [x,y]

null_sort :: Sort
null_sort = Sort "Null" "Null" 2

null_type :: TypeSystem t => t
null_type = make_type null_sort []

maybe_sort :: Sort
maybe_sort   = Sort "\\maybe" "Maybe" 1

maybe_type :: TypeSystem t => t -> t
maybe_type t = make_type maybe_sort [t]

fun_sort :: Sort
fun_sort = DefSort "\\pfun" "pfun" ["a","b"] (array (GENERIC "a") (maybe_type $ GENERIC "b"))

fun_type :: TypeSystem t => t -> t -> t
fun_type t0 t1 = make_type fun_sort [t0,t1] --ARRAY t0 t1

bool :: TypeSystem t => t
bool = make_type BoolSort []
    
array_sort :: Sort
array_sort = Sort "Array" "Array" 2

array :: TypeSystem t => t -> t -> t
array t0 t1 = make_type array_sort [t0,t1]

set_sort :: Sort
set_sort = DefSort "\\set" "set" ["a"] (array (GENERIC "a") bool)

set_type :: TypeSystem t => t -> t
set_type t = make_type set_sort [t]

int :: TypeSystem t => t
int  = make_type IntSort []

real :: TypeSystem t => t
real = make_type RealSort []

instance Arbitrary Sort where
    arbitrary = oneof
        [ pure BoolSort 
        , pure IntSort 
        , pure RealSort 
        , Sort <$> arbitrary <*> arbitrary <*> elements [0..5]
        ]
        -- | Datatype 
        --    [String]    -- Parameters
        --    String      -- type name
        --    [(String, [(String,GenericType)])] 

instance Arbitrary GenericType where
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
    shrink (Gen s ts) = ts ++ do
            ts <- mapM shrink ts
            return $ t ts
        where
            t ts = Gen s ts

instance NFData t => NFData (TypeCons t)
instance NFData FOType
instance NFData GenericType
instance NFData Sort
