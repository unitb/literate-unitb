{-# LANGUAGE TypeFamilies
        , LambdaCase
        , OverloadedStrings  #-}
module Logic.Expr.Type where

    -- Modules
import Logic.Expr.Classes
import Logic.Expr.PrettyPrint
import Logic.Names

    -- Libraries
import Control.DeepSeq
import Control.Lens hiding (List,elements)
import Control.Monad.Reader
import Control.Precondition

import           Data.Data
import           Data.Hashable
import qualified Data.Set as S

import           GHC.Generics.Instances

import Language.Haskell.TH.Syntax hiding (Name)

import           Test.QuickCheck

import           Text.Printf.TH


class TypeOf a ~ TypeOf (TypeOf a) => Typed a where
    type TypeOf a :: *

referenced_types :: FOType -> S.Set FOType
referenced_types t@(FOT _ ts) = S.insert t $ S.unions $ map referenced_types ts

instance Typed GenericType where
    type TypeOf GenericType = GenericType

class (Ord a, Tree a, PrettyPrintable a, Show a
        , Typed a, TypeOf a ~ a, Typeable a
        , Hashable a ) 
        => TypeSystem a where
    make_type :: Sort -> [a] -> a

instance TypeSystem GenericType where
    make_type    = Gen

instance Typed FOType where
    type TypeOf FOType = FOType

instance TypeSystem FOType where
    make_type = FOT

instance Hashable FOType where
instance Hashable GenericType where
instance Hashable Sort where

instance Typed () where
    type TypeOf () = ()

instance TypeSystem () where
    make_type _ _ = ()

type Type = GenericType
type GenericType = AbsType InternalName
type TaggedType  = AbsType TaggedName
type TaggedName  = (Int,InternalName)
type Tag = InternalName -> TaggedName

data AbsType n = 
        Gen Sort [AbsType n] 
        | GENERIC n
        | VARIABLE InternalName
    deriving (Eq,Ord,Typeable,Generic,Data,Show,Functor,Foldable,Traversable)

data FOType      = FOT Sort [FOType]
    deriving (Eq, Ord, Typeable, Generic, Show)

instance Tree GenericType where
    as_tree' (Gen s ts) = cons_to_tree s ts
    as_tree' (GENERIC x)   = return $ Str $ render x
    as_tree' (VARIABLE n)  = return $ Str $ "_" ++ render n
    {-# INLINABLE rewriteM #-}
    rewriteM f (Gen s ts) = do
            Gen s <$> traverse f ts
    rewriteM _ x@(VARIABLE _) = pure x
    rewriteM _ x@(GENERIC _)  = pure x

instance Tree FOType where
    as_tree' (FOT s ts) = cons_to_tree s ts
    {-# INLINABLE rewriteM #-}
    rewriteM f (FOT s ts) = FOT s <$> traverse f ts

instance Lift GenericType where
    lift = genericLift

as_generic :: FOType -> GenericType
as_generic (FOT s ts) = Gen s (map as_generic ts)

cons_to_tree :: Tree a => Sort -> [a] -> Reader (OutputMode n) StrList
cons_to_tree s [] = do
    opt <- ask
    let n = case opt of
                ProverOutput -> render $ z3_name s
                UserOutput -> render $ s^.name
    return $ Str n
cons_to_tree s ts = do
    opt <- ask
    let n = case opt of
                ProverOutput -> render $ z3_name s
                UserOutput -> render $ s^.name
    return $ List (Str n : map as_tree ts)

data Sort =
        BoolSort | IntSort | RealSort 
        | DefSort 
            Name        -- Latex name
            InternalName    -- Type name
            [Name]  -- Generic Parameter
            GenericType -- Type with variables
        | Sort Name InternalName Int
        | Datatype 
            [Name]    -- Parameters
            Name      -- type name
            [(Name, [(Name,GenericType)])] 
                        -- alternatives and named components
    deriving (Eq, Ord, Show, Typeable, Data, Generic)

typeParams :: Sort -> Int
typeParams BoolSort = 0
typeParams IntSort  = 0
typeParams RealSort = 0
typeParams (Sort _ _ n) = n
typeParams (DefSort _ _ ps _) = length ps
typeParams (Datatype xs _ _)  = length xs

instance PrettyPrintable FOType where
    pretty (FOT s []) = (render $ z3_name s)
    pretty (FOT s ts) = [printf|%s %s|] (render $ s^.name) (show $ map Pretty ts)

instance PrettyPrintable GenericType where
    pretty (GENERIC n)         = "_" ++ render n 
    pretty (VARIABLE n)        = "'" ++ render n 
    pretty (Gen s []) = render $ s^.name
    pretty (Gen s ts) = [printf|%s %s|] (render $ s^.name) (show $ map Pretty ts)

instance HasName Sort Name where
    name = to $ \case 
        (Sort x _ _) -> x
        (DefSort x _ _ _) -> x
        (Datatype _ x _)  -> x
        BoolSort   -> makeName assert "\\Bool"
        IntSort    -> makeName assert "\\Int"
        RealSort   -> makeName assert "\\Real"

instance Named Sort where
    type NameOf Sort = Name
    decorated_name' s = do
        opt <- ask
        case opt of
            ProverOutput -> return $ z3_name s
            UserOutput -> return $ s^.name

        -- TODO: make BoolSort, IntSort, RealSort into 
        -- the Sort datatype with a 'builtin' flag
    z3_name (Sort _ x _) = x
    z3_name (DefSort _ x _ _) = x
    z3_name (Datatype _ x _)  = asInternal x
    z3_name BoolSort   = fromString'' "Bool"
    z3_name IntSort    = fromString'' "Int"
    z3_name RealSort   = fromString'' "Real"

instance Lift Sort where
    lift = genericLift

pair_sort :: Sort
pair_sort = -- Sort "Pair" "Pair" 2
               Datatype [fromString'' "a",fromString'' "b"] 
                    (fromString'' "Pair")
                    [ (fromString'' "pair", 
                        [ (fromString'' "first",  gA)
                        , (fromString'' "second", gB) ]) ]


pair_type :: TypeSystem t => t -> t -> t
pair_type x y = make_type pair_sort [x,y]

null_sort :: Sort
null_sort = Datatype [] (fromString'' "Null") [ (fromString'' "null", []) ] 

null_type :: TypeSystem t => t
null_type = make_type null_sort []

maybe_sort :: Sort
maybe_sort   = Datatype [fromString'' "a"] (fromString'' "Maybe")
                    [ (fromString'' "Just", [(fromString'' "fromJust", gA)])
                    , (fromString'' "Nothing", []) ]

maybe_type :: TypeSystem t => t -> t
maybe_type t = make_type maybe_sort [t]

fun_sort :: Sort
fun_sort = make DefSort "\\pfun"
        "pfun" [fromString'' "a",fromString'' "b"] (array gA (maybe_type gB))

fun_type :: TypeSystem t => t -> t -> t
fun_type t0 t1 = make_type fun_sort [t0,t1] --ARRAY t0 t1

bool :: TypeSystem t => t
bool = make_type BoolSort []
    
array_sort :: Sort
array_sort = make Sort "Array" "Array" 2

array :: TypeSystem t => t -> t -> t
array t0 t1 = make_type array_sort [t0,t1]

set_sort :: Sort
set_sort = make DefSort "\\set" "set" [fromString'' "a"] (array gA bool)

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

gA :: GenericType
gA = GENERIC $ fromString'' "a"

gB :: GenericType
gB = GENERIC $ fromString'' "b"

gC :: GenericType
gC = GENERIC $ fromString'' "c"

z3Sort :: (?loc :: CallStack) 
       => String -> String -> Int -> Sort
z3Sort n0 n1 = Sort (fromString'' n0) (z3Name n1)

z3DefSort :: (?loc :: CallStack) 
          => String -> String -> [String] -> GenericType -> Sort
z3DefSort n0 n1 ps = DefSort (fromString'' n0) (fromString'' n1) (fromString'' <$> ps)

z3GENERIC :: (?loc :: CallStack)
          => String -> GenericType
z3GENERIC = GENERIC . fromString''

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
                [ make Sort "A" "A" 0
                , make Sort "B" "B" 1
                , make Sort "C" "C" 1
                , make Sort "D" "D" 2
                , make DefSort "E" "E" 
                            [ fromString'' "a"
                            , fromString'' "b"] $ array gA gB
                , BoolSort
                , IntSort
                , RealSort
                ]
            gen_prm = map return
                [ gA
                , gB
                , gC
                ]
    shrink (GENERIC _)  = []
    shrink (VARIABLE _) = []
    shrink (Gen s ts) = ts ++ do
            ts <- mapM shrink ts
            return $ t ts
        where
            t ts = Gen s ts

instance NFData FOType
instance NFData GenericType
instance NFData Sort
