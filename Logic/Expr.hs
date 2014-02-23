{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, DefaultSignatures #-}
module Logic.Expr where

    -- Module
import Logic.Classes

    -- library
import           GHC.Generics

import           Data.List
import           Data.Map as M hiding (map,filter,foldl)
import qualified Data.Set as S
import           Data.Typeable

import Utilities.Format

data Expr = 
        Word Var 
        | Const [Type] String Type
        | FunApp Fun [Expr]
        | Binder Quantifier [Var] Expr Expr
    deriving (Eq, Ord, Typeable, Generic)

data Quantifier = Forall | Exists | Lambda
    deriving (Eq, Ord, Generic)

type ExprP = Either String Expr 

type_of :: Expr -> Type
type_of (Word (Var _ t))          = t
type_of (Const _ _ t)             = t
type_of (FunApp (Fun _ _ _ t) _) = t
type_of (Binder Lambda vs _ e)   = fun_type (type_of tuple) $ type_of e
    where
        tuple = ztuple $ map Word vs
type_of (Binder _ _ _ e)          = type_of e

ztuple_type :: [Type] -> Type
ztuple_type []          = null_type
ztuple_type [x]         = x
ztuple_type [x0,x1]     = pair_type x0 $ pair_type x1 null_type
ztuple_type (x0:x1:xs)  = pair_type x0 $ ztuple_type (x1:xs)

ztuple :: [Expr] -> Expr
ztuple []           = unit
ztuple [x]          = x
ztuple [x0,x1]      = pair x0 $ pair x1 unit    -- FunApp (Fun [tx, txs] "pair" [tx, txs] pair_type) [x,tail]
ztuple (x0:x1:xs)   = pair x0 $ ztuple (x1:xs)  -- FunApp (Fun [tx, txs] "pair" [tx, txs] pair_type) [x,tail]
--    where
--        tx  = type_of x
--        txs = type_of tail
--        pair_sort = Sort "Pair" "Pair" 2
--        pair_type = USER_DEFINED pair_sort [tx,txs]
--        tail = ztuple xs

pair_sort :: Sort
pair_sort = -- Sort "Pair" "Pair" 2
               Datatype ["a","b"] "Pair" 
                    [ ("pair", 
                        [ ("first",  GENERIC "a")
                        , ("second", GENERIC "b") ]) ]


pair_type :: Type -> Type -> Type
pair_type x y = USER_DEFINED pair_sort [x,y]

null_sort :: Sort
null_sort = Sort "Null" "Null" 2

null_type :: Type
null_type = USER_DEFINED null_sort []

unit :: Expr
unit = Const [] "null" null_type

pair :: Expr -> Expr -> Expr
pair x y = FunApp (Fun [] "pair" [t0,t1] $ pair_type t0 t1) [x,y]
    where
        t0 = type_of x
        t1 = type_of y

maybe_sort :: Sort
maybe_sort   = Sort "\\maybe" "Maybe" 1

maybe_type :: Type -> Type
maybe_type t = USER_DEFINED maybe_sort [t]

fun_sort :: Sort
fun_sort = DefSort "\\pfun" "pfun" ["a","b"] (ARRAY (GENERIC "a") (maybe_type $ GENERIC "b"))

fun_type :: Type -> Type -> Type
fun_type t0 t1 = USER_DEFINED fun_sort [t0,t1] --ARRAY t0 t1

merge_range :: Quantifier -> StrList
merge_range Forall = Str "=>"
merge_range Exists = Str "and"
merge_range Lambda = Str "PRE"

data Type = 
        ARRAY Type Type 
        | GENERIC String 
        | VARIABLE String
        | USER_DEFINED Sort [Type]
    deriving (Eq, Ord, Typeable, Generic)

data Context = Context 
        (Map String Sort) -- sorts
        (Map String Var)  -- constants
        (Map String Fun)  -- functions and operators
        (Map String Def)  -- transparent definitions
        (Map String Var)  -- dummies
    deriving (Show,Eq,Generic)

class Symbol a where
    decl :: a -> [Decl]

instance Show Type where
    show (ARRAY t0 t1)       = format "ARRAY {0}" [t0,t1]
    show (GENERIC n)         = format "_{0}" n 
    show (VARIABLE n)        = format "'{0}" n 
    show (USER_DEFINED s []) = (z3_name s)
    show (USER_DEFINED s ts) = format "{0} {1}" (z3_name s) ts

instance Tree Type where
    as_tree (ARRAY t0 t1) = List [Str "Array", as_tree t0, as_tree t1]
    as_tree (GENERIC x)   = Str x
    as_tree (VARIABLE n)  = Str $ "_" ++ n
    as_tree (USER_DEFINED s []) = Str $ z3_name s
    as_tree (USER_DEFINED s xs) = List (Str (z3_name s) : map as_tree xs)
    rewriteM' f s0 (ARRAY t0 t1) = do
            (s1,t2) <- f s0 t0
            (s2,t3) <- f s1 t1
            return (s2,ARRAY t2 t3)
    rewriteM' _ s x@(VARIABLE _) = return (s,x)
    rewriteM' _ s x@(GENERIC _)  = return (s,x)
    rewriteM' f s0 (USER_DEFINED s xs) = do
            (s1,ys) <- fold_mapM f s0 xs
            return (s1, USER_DEFINED s ys)

z3_decoration :: Type -> String
z3_decoration t = f $ as_tree t :: String
    where
        f (List ys) = format "@Open{0}@Close" xs
            where xs = concatMap f ys :: String
        f (Str y)   = format "@@{0}" y

data Sort =
        BoolSort | IntSort | RealSort 
        | DefSort String String [String] Type
        | Sort String String Int --[String]
        | Datatype 
            [String]    -- Parameters
            String      -- type name
            [(String, [(String,Type)])] -- alternatives and named components
    deriving (Eq, Ord, Show, Generic)

z3_name :: Sort -> String
z3_name (BoolSort) = "Bool"
z3_name (IntSort)  = "Int"
z3_name (RealSort) = "Real"
z3_name (Sort _ x _)       = x
z3_name (DefSort _ x _ _)  = x
z3_name (Datatype _ x _)   = x

    -- replace it everywhere
z3_fun_name :: Fun -> String
z3_fun_name (Fun xs ys _ _) = ys ++ concatMap z3_decoration xs

data Decl = 
        FunDecl [Type] String [Type] Type 
        | ConstDecl String Type
        | FunDef [Type] String [Var] Type Expr
        | SortDecl Sort

data Fun = Fun [Type] String [Type] Type
    deriving (Eq, Ord, Generic)

data Var = Var String Type
    deriving (Eq,Ord,Generic,Typeable)

data Def = Def [Type] String [Var] Type Expr
    deriving (Eq,Generic)

instance Show StrList where
    show (List xs) = "(" ++ intercalate " " (map show xs) ++ ")"
    show (Str s)   = s

instance Show Quantifier where
    show Forall = "forall"
    show Exists = "exists"
    show Lambda = "lambda"

instance Tree Expr where
    as_tree (Word (Var xs _))    = Str xs
    as_tree (Const [] "Nothing" t) = List [Str "as", Str "Nothing", as_tree t]
    as_tree (Const ys xs _)        = Str (xs ++ concatMap z3_decoration ys)
    as_tree (FunApp (Fun xs name _ _) [])  = 
        Str (name ++ concatMap z3_decoration xs)
    as_tree (FunApp (Fun xs name _ _) ts)  = 
        List (Str (name ++ concatMap z3_decoration xs) : (map as_tree ts))
    as_tree (Binder q xs r xp)  = List 
        [ Str $ show q
        , List $ map as_tree xs
        , List 
            [ merge_range q
            , as_tree r
            , as_tree xp ] ]
    rewriteM' _ s x@(Word _)           = return (s,x)
    rewriteM' _ s x@(Const _ _ _)      = return (s,x)
    rewriteM' f s0 (FunApp g@(Fun _ _ _ _) xs)  = do
            (s1,ys) <- fold_mapM f s0 xs
            return (s1,FunApp g ys)
    rewriteM' f s0 (Binder q xs r0 x)  = do
            (s1,r1) <- f s0 r0
            (s2,y)  <- f s1 x
            return (s2,Binder q xs r1 y)

instance Show Expr where
    show e = show $ as_tree e

instance Tree Decl where
    as_tree (FunDecl ts name dom ran) =
            List [ Str "declare-fun", 
                Str $ name ++ concatMap z3_decoration ts, 
                (List $ map as_tree dom), 
                (as_tree ran) ]
    as_tree (ConstDecl n t) =
            List [ Str "declare-const", Str n, as_tree t ]
    as_tree (FunDef _ name dom ran val) =
            List [ Str "define-fun", 
                Str name, 
                (List $ map as_tree dom), 
                (as_tree ran),
                (as_tree val) ]
    as_tree (SortDecl IntSort)  = Str "; comment: we don't need to declare the sort Int"
    as_tree (SortDecl BoolSort) = Str "; comment: we don't need to declare the sort Bool" 
    as_tree (SortDecl RealSort) = Str "; comment: we don't need to declare the sort Real"
    as_tree (SortDecl (Sort _ name n)) = 
            List [ 
                Str "declare-sort",
                Str name,
                Str $ show n ]
    as_tree (SortDecl (DefSort _ name xs def)) = 
            List 
                [ Str "define-sort"
                , Str name
                , List $ map Str xs
                , as_tree def 
                ]
    as_tree (SortDecl (Datatype xs n alt)) =
            List 
                [ Str "declare-datatypes"
                , List $ map Str xs
                , List [List (Str n : map f alt)] ]
        where
            f (x,[])    = Str x
            f (x,xs)    = List (Str x : map g xs)
            g (n,t)     = List [Str n, as_tree t]
    rewriteM' = id
    
instance Tree Var where
    as_tree (Var vn vt) = List [Str vn, as_tree vt]
    rewriteM' = id

-- instance Tree Sort where
	-- as_tree B
    -- as_tree (DefSort _ x xs def) = 
            -- List 
                -- [ Str x
                -- , List $ map Str xs
                -- , as_tree def
                -- ]
    -- as_tree (Sort _ x n) = List [Str x, Str $ show n]
    -- rewriteM' = id

instance Show Var where
    show (Var n t) = n ++ ": " ++ show (as_tree t)

instance Show Fun where
    show (Fun xs n ts t) = n ++ show xs ++ ": " 
        ++ intercalate " x " (map (show . as_tree) ts)
        ++ " -> " ++ show (as_tree t)

instance Show Def where
    show (Def xs n ps t e) = n ++ show xs ++  ": " 
        ++ intercalate " x " (map (show . as_tree) ps)
        ++ " -> " ++ show (as_tree t)
        ++ "  =  " ++ show (as_tree e)

instance Symbol Sort where
    decl s = [SortDecl s]

instance Symbol Fun where
    decl (Fun xs name params ret) = [FunDecl xs name params ret]

instance Symbol Var where
    decl (Var name typ)        = [ConstDecl name typ]

instance Symbol Def where
    decl (Def xs name ps typ ex)  = [FunDef xs name ps typ ex]

instance Symbol Context where
    decl (Context sorts cons fun defs _) = -- dums) = 
                concatMap decl (elems sorts)
--            ++  concatMap decl (elems (cons `merge` dums)) 
            ++  concatMap decl (elems cons) 
            ++  concatMap decl (elems fun) 
            ++  concatMap decl (elems defs) 


merge :: (Ord k, Eq a, Show k, Show a)
          => Map k a -> Map k a -> Map k a
merge m0 m1 = unionWithKey f m0 m1
    where
        f k x y
            | x == y 	= x
			| otherwise = error $ format "conflicting declaration for key {0}: {1} {2}" k x y

merge_all :: (Ord k, Eq a, Show k, Show a)
          => [Map k a] -> Map k a
merge_all ms = foldl (unionWithKey f) empty ms
    where
        f k x y
            | x == y    = x
            | otherwise = error $ format "conflicting declaration for key {0}: {1} {2}" k x y

mk_context :: [Decl] -> Context
mk_context (x:xs) = 
        case mk_context xs of
            Context ss vs fs defs dums -> 
                case x of
                    SortDecl s ->
                        Context
                            (M.insert (z3_name s) s ss) vs
                            fs defs dums
                    ConstDecl n t -> 
                        Context 
                            ss (M.insert n (Var n t) vs) 
                            fs defs dums
                    FunDecl gs n ps t -> 
                        Context 
                            ss vs 
                            (M.insert n (Fun gs n ps t) fs)
                            defs dums
                    FunDef gs n ps t e -> 
                        Context 
                            ss vs fs 
                            (M.insert n (Def gs n ps t e) defs) 
                            dums
--                    Datatype _ _ _ -> error "Z3.Def.mk_context: datatypes are not supported"
mk_context [] = Context empty empty empty empty empty

substitute :: Map Var Expr -> Expr -> Expr
substitute m e = f e
    where
        f e@(Word v) = maybe e id $ M.lookup v m
        f e = rewrite f e

empty_ctx :: Context
empty_ctx = Context empty empty empty empty empty

merge_ctx :: Context -> Context -> Context
merge_ctx (Context ss0 vs0 fs0 ds0 dum0) (Context ss1 vs1 fs1 ds1 dum1) = 
        Context 
            (ss0 `merge` ss1) 
            (vs0 `merge` vs1) 
            (fs0 `merge` fs1) 
            (ds0 `merge` ds1)
            (dum0 `merge` dum1)
merge_all_ctx :: [Context] -> Context
merge_all_ctx cs = Context 
        (merge_all $ map f0 cs) 
        (merge_all $ map f1 cs)
        (merge_all $ map f2 cs)
        (merge_all $ map f3 cs)
        (merge_all $ map f4 cs)
    where
        f0 (Context x _ _ _ _) = x
        f1 (Context _ x _ _ _) = x
        f2 (Context _ _ x _ _) = x
        f3 (Context _ _ _ x _) = x
        f4 (Context _ _ _ _ x) = x

used_var :: Expr -> S.Set Var
used_var (Word v) = S.singleton v
used_var (Binder _ vs r expr) = (used_var expr `S.union` used_var r) `S.difference` S.fromList vs
used_var expr = visit (\x y -> S.union x (used_var y)) S.empty expr

instance Named Fun where
    name (Fun _ x _ _) = x

instance Named Var where
    name (Var x _) = x

instance Named Sort where
    name (Sort x _ _) = x
    name (DefSort x _ _ _) = x
    name (Datatype _ x _)  = x
    name BoolSort   = "\\Bool"
    name IntSort    = "\\Int"
    name RealSort   = "\\Real"

pretty_print' :: Tree t => t -> String
pretty_print' t = unlines $ pretty_print $ as_tree t 

pretty_print :: StrList -> [String]
pretty_print (Str xs) = [xs]
pretty_print (List []) = ["()"]
pretty_print (List ys@(x:xs)) = 
        case x of
            Str y    -> 
                if length one_line <= 50
                then ["(" ++ y ++ one_line ++ ")"]
                else map (uncurry (++)) $ zip
                        (("(" ++ y ++ " "):repeat (margin (length y + 2)))
                        (collapse (concatMap pretty_print xs ++ [")"]))
            List _ -> map (uncurry (++)) $ zip
                ("( ":repeat (margin 2))
                (collapse (concatMap pretty_print ys ++ [" )"]))
    where
        margin n = take n (repeat ' ')
        collapse xs = 
            case reverse xs of
                y0:y1:ys -> reverse ( (y1++y0):ys )
                _        -> xs
        one_line = concatMap (uncurry (++)) $ zip (repeat " ") $ concatMap pretty_print xs
