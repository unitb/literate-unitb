{-# LANGUAGE DeriveDataTypeable     #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
module Logic.Expr.Expr 
    ( Expr, AbsExpr, GenExpr (..), FOExpr
    , UntypedExpr, ExprP, ExprPG, ExprPC
    , Value(..), type_of
    , Quantifier(..)
    , Context, FOContext, AbsContext(..)
    , Decl, FODecl, AbsDecl(..)
    , Fun, FOFun, AbsFun(..)
    , Var, FOVar, AbsVar(..), UntypedVar
    , Def, FODef, AbsDef(..)
    , merge, merge_all
    , merge_ctx, merge_all_ctx
    , mk_context, empty_ctx
    , used_var, used_fun, used_types
    , substitute, rename
    , z3_fun_name
    , z3_decoration
    -- , pretty_print
    , array
    , decl, Symbol
    , ztuple_type, ztuple
    , fun_type, fun_sort
    , maybe_type
    , pair, pair_type, pair_sort
    , pretty_print', free_vars
    , var_decl
    )
where

    -- Module
import Logic.Expr.Label
import Logic.Expr.Classes
import Logic.Expr.Type

    -- Library
import           GHC.Generics

import Control.Applicative ((<|>))
import Control.DeepSeq
import Control.Monad.Reader

import           Data.List as L
import qualified Data.Map as M hiding (map,foldl)
import qualified Data.Set as S
import           Data.Typeable

import Utilities.Format

type Expr = AbsExpr GenericType

type FOExpr = AbsExpr FOType

type AbsExpr t = GenExpr t t

type UntypedExpr = GenExpr () GenericType

data GenExpr t a = 
        Word (AbsVar t) 
        | Const Value t
        | FunApp (AbsFun t) [GenExpr t a]
        | Binder Quantifier [AbsVar t] (GenExpr t a) (GenExpr t a)
        | Cast (GenExpr t a) a
        | Lift (GenExpr t a) a
    deriving (Eq, Ord, Typeable, Generic)

data Value = RealVal Double | IntVal Int
    deriving (Eq,Ord,Generic)

instance Show Value where
    show (RealVal v) = show v
    show (IntVal v)  = show v

data Quantifier = Forall | Exists | Lambda
    deriving (Eq, Ord, Generic)

instance NFData Quantifier where

type ExprP = Either [String] Expr 

type ExprPG t = Either [String] (AbsExpr t)

type ExprPC e = Either [String] e

type_of :: TypeSystem t => AbsExpr t -> t
type_of (Word (Var _ t))         = t
type_of (Const _ t)              = t
type_of (Cast _ t)               = t
type_of (Lift _ t)               = t
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
unit = FunApp (Fun [] "null" [] null_type) []

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
        (M.Map String Sort) -- sorts
        (M.Map String (AbsVar t))  -- constants
        (M.Map String (AbsFun t))  -- functions and operators
        (M.Map String (AbsDef t))  -- transparent definitions
        (M.Map String (AbsVar t))  -- dummies
    deriving (Show,Eq,Generic,Typeable)

instance NFData t => NFData (AbsContext t) where
    rnf (Context a b c d e) = rnf (a,b,c,d,e)

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

instance NFData (AbsDecl FOType) where
    rnf (FunDecl xs n args t) = rnf (xs,n,args,t)
    rnf (ConstDecl n t) = rnf (n,t)
    rnf (FunDef xs n args t e) = rnf (xs,n,args,t,e)
    rnf (SortDecl s) = rnf s

type Fun = AbsFun GenericType

type FOFun = AbsFun FOType

data AbsFun t = Fun [t] String [t] t
    deriving (Eq, Ord, Generic)

instance NFData t => NFData (AbsFun t) where
    rnf (Fun xs n args t) = rnf (xs,n,args,t)

type UntypedVar = AbsVar ()

type Var = AbsVar GenericType

type FOVar = AbsVar FOType

data AbsVar t = Var String t
    deriving (Eq,Ord,Generic,Typeable)

instance NFData t => NFData (AbsVar t) where
    rnf (Var xs t) = rnf (xs,t)

type FODef = AbsDef FOType

type Def = AbsDef GenericType

data AbsDef t = Def [t] String [AbsVar t] t (AbsExpr t)
    deriving (Eq,Ord,Generic)

instance Show StrList where
    show (List xs) = "(" ++ intercalate " " (map show xs) ++ ")"
    show (Str s)   = s

instance Show Quantifier where
    show Forall = "forall"
    show Exists = "exists"
    show Lambda = "lambda"

instance TypeSystem t => Tree (AbsExpr t) where
    as_tree (Cast e t)   = List [Str "as", as_tree e, as_tree t]
    as_tree (Lift e t) = List [ List [Str "as", Str "const", as_tree t]
                                        , as_tree e]
    as_tree (Word (Var xs _))    = Str xs
    -- as_tree (Const [] "Nothing" t) = List [Str "as", Str "Nothing", as_tree t]
    as_tree (Const xs _)         = Str $ show xs
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
    rewriteM' _ s x@(Const _ _)        = return (s,x)
    rewriteM' f s (Lift e t)           = do
            (x,e') <- f s e
            return (x, Lift e' t)
    rewriteM' f s (Cast e t)           = do
            (x,e') <- f s e
            return (x, Cast e' t)
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
    as_tree (FunDef ts name dom ran val) =
            List [ Str "define-fun", 
                Str $ name ++ concatMap z3_decoration ts, 
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
        ++ args ++ show (as_tree t)
        ++ "  =  " ++ show (as_tree e)
        where
            args
                | L.null ps = ""
                | otherwise = intercalate " x " (map (show . as_tree) ps) ++ " -> "

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
                concatMap decl (M.elems sorts)
--            ++  concatMap decl (elems (cons `merge` dums)) 
            ++  concatMap decl (M.elems cons) 
            ++  concatMap decl (M.elems fun) 
            ++  concatMap decl (M.elems defs) 

instance NFData t => NFData (AbsDef t) where
    rnf (Def xs n args t e) = rnf (xs,n,args,t,e)

merge :: (Ord k, Eq a, Show k, Show a)
          => M.Map k a -> M.Map k a -> M.Map k a
merge m0 m1 = M.unionWithKey f m0 m1
    where
        f k x y
            | x == y    = x
            | otherwise = error $ format "conflicting declaration for key {0}: {1} {2}" k x y

merge_all :: (Ord k, Eq a, Show k, Show a)
          => [M.Map k a] -> M.Map k a
merge_all ms = foldl (M.unionWithKey f) M.empty ms
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
mk_context [] = empty_ctx

substitute :: M.Map String Expr -> Expr -> Expr
substitute m e = f e
    where
        f e@(Word v) = maybe e id $ M.lookup (name v) m
        f e@(Binder _ vs _ _) = rewrite (substitute $ subst vs) e
        f e = rewrite f e
        subst vs = m M.\\ symbol_table vs

empty_ctx :: AbsContext t
empty_ctx = Context M.empty M.empty M.empty M.empty M.empty

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

free_vars :: Context -> Expr -> M.Map String Var
free_vars (Context _ _ _ _ dum) e = M.fromList $ f [] e
    where
        f xs (Word v@(Var n _))
            | n `M.member` dum = (n,v):xs
            | otherwise      = xs
        f xs v@(Binder _ vs _ _) = M.toList (M.fromList (visit f xs v) M.\\ symbol_table vs)
        f xs v = visit f xs v

var_decl :: String -> Context -> Maybe Var
var_decl s (Context _ m _ _ d) = 
    M.lookup s m <|> M.lookup s d

used_fun :: TypeSystem t => AbsExpr t -> S.Set (AbsFun t)
used_fun e = visit f s e
    where
        f x y = S.union x (used_fun y)
        s = case e of
                FunApp f _ -> S.singleton f
                -- Const ts n t -> S.singleton $ Fun ts n [] t
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

instance Convert (AbsVar t) (ExprPC (AbsExpr t)) where
    convert_to = Right . Word
    convert_from (Right (Word x)) = Just x
    convert_from _        = Nothing

instance Convert (AbsExpr t) (AbsExpr t) where
    convert_to = id
    convert_from = Just

pretty_print' :: Tree t => t -> String
-- pretty_print' t = unlines $ pretty_print $ as_tree t 
pretty_print' t = unlines $ map toString $ as_list $ fst $ runReader (pretty_print_aux $ as_tree t) ""

data Line = Line String String

toString :: Line -> String
toString (Line xs ys) = xs ++ ys

line :: Line -> String
line (Line _ ys) = ys

type M = Reader String
type X = (List Line,Int)

data List a = Ls [a] a

appendL :: List a -> List a -> List a
appendL (Ls xs x) (Ls ys y) = Ls (xs ++ [x] ++ ys) y

tell' :: String -> M X
tell' xs = do
    ys <- ask
    return $ (Ls [] $ Line ys xs,length xs+1)

appendall :: [(List a, Int)] -> (List a, Int)
appendall ((x0,n):(x1,m):xs) = appendall $ (appendL x0 x1, m+n) : xs
appendall [x] = x
appendall _ = error "appendall: empty list"

cons :: a -> [a] -> List a
cons x xs = Ls (init ys) (last ys)
    where
        ys = x:xs

uncons :: List a -> (a -> [a] -> b) -> b
uncons (Ls xs x) f = f (head zs) (tail zs)
    where
        zs = xs ++ [x]

as_list :: List a -> [a]
as_list (Ls xs x) = xs ++ [x]

pretty_print_aux :: StrList -> M X
pretty_print_aux (Str xs) = tell' xs
pretty_print_aux (List []) = tell' "()"
pretty_print_aux (List ys@(x:xs)) = 
        case x of
            Str y    -> do
                zz <- mapM pretty_print_aux xs
                let one_line' = concatMap (" " ++) $ concatMap (map line . as_list . fst) zz
                    k = sum $ map snd zz
                if k <= 50
                then tell' $ "(" ++ y ++ one_line' ++ ")"
                else do
                    zs <- prefix_first ("(" ++ y ++ " ") $
                        mapM pretty_print_aux xs
                    return $ add_to_last ")" $ appendall zs
            List _ -> do
                zs <- prefix_first "( " $
                    mapM pretty_print_aux ys
                return $ add_to_last " )" $ appendall zs
    where
        prefix_first :: String -> M [X] -> M [X]
        prefix_first xs cmd = do
            let k = length xs
            ys <- indent k cmd 
            case ys of
                [] -> (:[]) `liftM` tell' xs
                (ls, n):ys -> 
                    uncons ls $ \(Line m y) zs ->
                    return $ (cons (Line (take (length m - k) m) (xs ++ y)) zs, n+k):ys
        indent n cmd = do
            local (margin n ++) cmd
        margin n = replicate n ' '
        add_to_last suff (Ls xs (Line x y),k) = (Ls xs (Line x $ y++suff),k)
  
-- pretty_print :: StrList -> [String]
-- pretty_print (Str xs) = [xs]
-- pretty_print (List []) = ["()"]
-- pretty_print (List ys@(x:xs)) = 
--         case x of
--             Str y    -> 
--                 if length one_line <= 50
--                 then ["(" ++ y ++ " " ++ one_line ++ ")"]
--                 else
--                     zipWith (++)
--                         (("(" ++ y ++ " "):repeat (margin (length y + 2)))
--                         (add_to_last ")" zs)
--             List _ -> zipWith (++)
--                 ("( ":repeat (margin 2))
--                 (add_to_last " )" zs')
--     where
--         margin n = replicate n ' '
--         add_to_last suff xs = 
--             case reverse xs of
--                 y:ys -> reverse ( (y++suff):ys )
--                 []        -> [suff]
--         zs = concatMap pretty_print xs
--         zs' = concatMap pretty_print ys
--         one_line = intercalate " " zs

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

instance NFData t => NFData (AbsExpr t) where
    rnf (Word x) = rnf x
    rnf (Const n t) = rnf (n,t)
    rnf (Cast x0 x1) = rnf (x0,x1)
    rnf (Lift x0 x1) = rnf (x0,x1)
    rnf (FunApp f args) = rnf (f,args)
    rnf (Binder q vs e0 e1) = rnf (q,vs,e0,e1)

instance NFData Value where
    rnf (RealVal v) = rnf v
    rnf (IntVal v)  = rnf v