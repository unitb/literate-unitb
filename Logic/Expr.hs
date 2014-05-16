{-# LANGUAGE DeriveDataTypeable     #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
module Logic.Expr where

    -- Module
import Logic.Classes
import Logic.Type

    -- library
import           GHC.Generics

import           Data.List as L
import           Data.Map as M hiding (map,filter,foldl)
import qualified Data.Set as S
import           Data.Typeable

import Utilities.Format

type Expr = AbsExpr GenericType

type FOExpr = AbsExpr FOType

data AbsExpr t = 
        Word (AbsVar t) 
        | Const [t] String t
        | FunApp (AbsFun t) [AbsExpr t]
        | Binder Quantifier [AbsVar t] (AbsExpr t) (AbsExpr t)
    deriving (Eq, Ord, Typeable, Generic)

data Quantifier = Forall | Exists | Lambda
    deriving (Eq, Ord, Generic)

type ExprP = Either String Expr 

type ExprPG t = Either String (AbsExpr t)

type_of :: TypeSystem t => AbsExpr t -> t
type_of (Word (Var _ t))         = t
type_of (Const _ _ t)            = t
type_of (FunApp (Fun _ _ _ t) _) = t
type_of (Binder Lambda vs _ e)   = fun_type (type_of tuple) $ type_of e
    where
        tuple = ztuple $ map Word vs
type_of (Binder _ _ _ e)          = type_of e

ztuple_type :: TypeSystem t => [t] -> t
ztuple_type []          = null_type
ztuple_type [x]         = x
ztuple_type [x0,x1]     = pair_type x0 $ pair_type x1 null_type
ztuple_type (x0:x1:xs)  = pair_type x0 $ ztuple_type (x1:xs)

ztuple :: TypeSystem t => [AbsExpr t] -> AbsExpr t
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


pair_type :: TypeSystem t => t -> t -> t
pair_type x y = make_type pair_sort [x,y]

null_sort :: Sort
null_sort = Sort "Null" "Null" 2

null_type :: TypeSystem t => t
null_type = make_type null_sort []

unit :: TypeSystem t => AbsExpr t
unit = Const [] "null" null_type

pair :: TypeSystem t => AbsExpr t -> AbsExpr t -> AbsExpr t
pair x y = FunApp (Fun [] "pair" [t0,t1] $ pair_type t0 t1) [x,y]
    where
        t0 = type_of x
        t1 = type_of y

maybe_sort :: Sort
maybe_sort   = Sort "\\maybe" "Maybe" 1

maybe_type :: TypeSystem t => t -> t
maybe_type t = make_type maybe_sort [t]

fun_sort :: Sort
fun_sort = DefSort "\\pfun" "pfun" ["a","b"] (array (GENERIC "a") (maybe_type $ GENERIC "b"))

fun_type :: TypeSystem t => t -> t -> t
fun_type t0 t1 = make_type fun_sort [t0,t1] --ARRAY t0 t1

merge_range :: Quantifier -> StrList
merge_range Forall = Str "=>"
merge_range Exists = Str "and"
merge_range Lambda = Str "PRE"

type Context = AbsContext GenericType

type FOContext = AbsContext FOType

data AbsContext t = Context 
        (Map String Sort) -- sorts
        (Map String (AbsVar t))  -- constants
        (Map String (AbsFun t))  -- functions and operators
        (Map String (AbsDef t))  -- transparent definitions
        (Map String (AbsVar t))  -- dummies
    deriving (Show,Eq,Generic,Typeable)

class Symbol a t where
    decl :: a -> [AbsDecl t]

z3_decoration :: TypeSystem t => t -> String
z3_decoration t = f $ as_tree t :: String
    where
        f (List ys) = format "@Open{0}@Close" xs
            where xs = concatMap f ys :: String
        f (Str y)   = format "@@{0}" y

array_sort :: Sort
array_sort = Sort "Array" "Array" 2

array :: TypeSystem t => t -> t -> t
array t0 t1 = make_type array_sort [t0,t1]

    -- replace it everywhere
z3_fun_name :: Fun -> String
z3_fun_name (Fun xs ys _ _) = ys ++ concatMap z3_decoration xs

type Decl = AbsDecl GenericType

type FODecl = AbsDecl FOType

data AbsDecl t = 
        FunDecl [t] String [t] t
        | ConstDecl String t
        | FunDef [t] String [AbsVar t] t (AbsExpr t)
        | SortDecl Sort

type Fun = AbsFun GenericType

type FOFun = AbsFun FOType

data AbsFun t = Fun [t] String [t] t
    deriving (Eq, Ord, Generic)

type Var = AbsVar GenericType

type FOVar = AbsVar FOType

data AbsVar t = Var String t
    deriving (Eq,Ord,Generic,Typeable)

type FODef = AbsDef FOType

type Def = AbsDef GenericType

data AbsDef t = Def [t] String [AbsVar t] t (AbsExpr t)
    deriving (Eq,Generic)

instance Show StrList where
    show (List xs) = "(" ++ intercalate " " (map show xs) ++ ")"
    show (Str s)   = s

instance Show Quantifier where
    show Forall = "forall"
    show Exists = "exists"
    show Lambda = "lambda"

instance TypeSystem t => Tree (AbsExpr t) where
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

instance TypeSystem t => Show (AbsExpr t) where
    show e = show $ as_tree e

instance TypeSystem t => Tree (AbsDecl t) where
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
    
instance TypeSystem t => Tree (AbsVar t) where
    as_tree (Var vn vt) = List [Str vn, as_tree vt]
    rewriteM' = id

instance TypeSystem t => Show (AbsVar t) where
    show (Var n t) = n ++ ": " ++ show (as_tree t)

instance TypeSystem t => Show (AbsFun t) where
    show (Fun xs n ts t) = n ++ show xs ++ ": " 
        ++ intercalate " x " (map (show . as_tree) ts)
        ++ " -> " ++ show (as_tree t)

instance TypeSystem t => Show (AbsDef t) where
    show (Def xs n ps t e) = n ++ show xs ++  ": " 
        ++ intercalate " x " (map (show . as_tree) ps)
        ++ " -> " ++ show (as_tree t)
        ++ "  =  " ++ show (as_tree e)

instance Symbol Sort t where
    decl s = [SortDecl s]

instance Symbol (AbsFun t) t where
    decl (Fun xs name params ret) = [FunDecl xs name params ret]

instance Symbol (AbsVar t) t where
    decl (Var name typ)        = [ConstDecl name typ]

instance Symbol (AbsDef t) t where
    decl (Def xs name ps typ ex)  = [FunDef xs name ps typ ex]

instance Symbol (AbsContext t) t where
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
            | x == y    = x
            | otherwise = error $ format "conflicting declaration for key {0}: {1} {2}" k x y

merge_all :: (Ord k, Eq a, Show k, Show a)
          => [Map k a] -> Map k a
merge_all ms = foldl (unionWithKey f) empty ms
    where
        f k x y
            | x == y    = x
            | otherwise = error $ format "conflicting declaration for key {0}: {1} {2}" k x y

mk_context :: TypeSystem t => [AbsDecl t] -> AbsContext t
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

used_var :: TypeSystem t => AbsExpr t -> S.Set (AbsVar t)
used_var (Word v) = S.singleton v
used_var (Binder _ vs r expr) = (used_var expr `S.union` used_var r) `S.difference` S.fromList vs
used_var expr = visit (\x y -> S.union x (used_var y)) S.empty expr

used_fun :: TypeSystem t => AbsExpr t -> S.Set (AbsFun t)
used_fun e = visit f s e
    where
        f x y = S.union x (used_fun y)
        s = case e of
                FunApp f _ -> S.singleton f
                Const ts n t -> S.singleton $ Fun ts n [] t
                _          -> S.empty

instance TypeSystem t => Named (AbsFun t) where
    name (Fun _ x _ _) = x
    decorated_name (Fun ts x _ _) = 
            x ++ concatMap z3_decoration ts

instance TypeSystem t => Named (AbsDef t) where
    name (Def _ x _ _ _) = x
    decorated_name (Def ts x _ _ _) = 
            x ++ concatMap z3_decoration ts

instance Named (AbsVar t) where
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

used_types :: TypeSystem t => AbsExpr t -> S.Set t
used_types e = visit (flip $ S.union . used_types) (
        case e of
            Binder _ vs e0 e1 -> S.fromList $ type_of e0 : type_of e1 : L.map f vs
            _ -> S.singleton $ type_of e
            ) e
    where
        f (Var _ t) = t

rename :: String -> String -> Expr -> Expr
rename x y e@(Word (Var vn t))
        | vn == x   = Word (Var y t)
        | otherwise = e
rename x y e@(Binder q vs r xp)
        | x `elem` L.map name vs  = e
        | otherwise             = Binder q vs (rename x y r) $ rename x y xp
rename x y e = rewrite (rename x y) e 
