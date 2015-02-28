{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
module Logic.Expr.Const where

    -- Modules   
import Logic.Expr.Classes 
import Logic.Expr.Expr
import Logic.Expr.Genericity
import Logic.Expr.Type

    -- Libraries
import Control.Monad

import           Data.List as L
import qualified Data.Map as M
import           Data.Maybe hiding ( fromJust )
import qualified Data.Set as S

import Utilities.Format
import Utilities.Syntactic

type OneExpr t = forall e0. 
           Convert e0 (AbsExpr t)
        => e0 -> AbsExpr t

type TwoExpr t = forall e0 e1. 
           (Convert e0 (AbsExpr t),Convert e1 (AbsExpr t))
        => e0 -> e1 -> AbsExpr t

fun1 :: ( TypeSystem t 
        , Convert e (AbsExpr t) )
     => AbsFun t 
     -> e -> AbsExpr t
fun1 f x           = FunApp f [convert_to x]
fun2 :: ( TypeSystem t 
        , Convert e0 (AbsExpr t)
        , Convert e1 (AbsExpr t) )
     => AbsFun t -> e0 
     -> e1 -> AbsExpr t
fun2 f x y         = FunApp f [convert_to x,convert_to y]

-- fun1 :: TypeSystem t 
--      => (ExprPG t -> ExprPG t)
--      -> AbsExpr t -> AbsExpr t
-- fun1 f x           = fromJust $ f (Right x)
-- fun2 :: TypeSystem t 
--      => (ExprPG t -> ExprPG t -> ExprPG t)
--      -> AbsExpr t -> AbsExpr t -> AbsExpr t
-- fun2 f x y         = fromJust $ f (Right x) (Right y)

no_errors2 :: TypeSystem t 
           => (TwoExprP t)
           -> (TwoExpr t)
no_errors2 f x y = either (error . unlines) id $ f (Right x) (Right y)

toErrors :: LineInfo -> ExprP -> Either [Error] Expr
toErrors li m = case m of
        Right x -> Right x
        Left xs -> Left $ map (`Error` li) xs

not_fun :: TypeSystem2 t => AbsFun t
not_fun = Fun [] "not" [bool] bool

znot :: TypeSystem2 t => OneExpr t
znot e = case convert_to e of 
            FunApp f [x]
                | f == not_fun -> x
                | otherwise    -> fun1 not_fun e
            e' -> fun1 not_fun e'
    -- znot         = fun1 mznot
zimplies :: TypeSystem2 t => TwoExpr t
zimplies x y = fromJust $ mzimplies (Right x) (Right y)
zand :: TypeSystem2 t => TwoExpr t
zand x y     = zall [convert_to x, convert_to y]
zor :: TypeSystem2 t => TwoExpr t
zor x y      = zsome [convert_to x, convert_to y]

zeq_fun :: Fun
zeq_fun      = Fun [] "="   [gA, gA] bool

zeq_symb :: TwoExpr Type
zeq_symb     = no_errors2 mzeq_symb
mzeq_symb :: TwoExprP Type
mzeq_symb    = typ_fun2 $ Fun [gA] "eq" [gA, gA] bool

zeq :: Expr -> Expr -> Expr
zeq          = no_errors2 mzeq
mzeq :: TwoExprP Type
mzeq         = typ_fun2 zeq_fun
zfollows :: TypeSystem2 t => AbsExpr t -> AbsExpr t -> AbsExpr t
zfollows     = fun2 $ Fun [] "follows" [bool,bool] bool
-- zfollows     = fun2 mzfollows
ztrue :: TypeSystem2 t => AbsExpr t
ztrue        = FunApp (Fun [] "true" [] bool) []
zfalse :: TypeSystem2 t => AbsExpr t
zfalse       = FunApp (Fun [] "false" [] bool) []
zall :: TypeSystem2 t => [AbsExpr t] -> AbsExpr t
zall xs      = 
        case concatMap f xs of
            []  -> ztrue
            [x] -> x
            xs  
                | zfalse `elem` xs -> zfalse
                | otherwise -> FunApp (Fun [] "and" (take n $ repeat bool) bool) xs
    where
        n = length xs
        f (FunApp (Fun [] "and" _ _) xs) = concatMap f xs
        f x
            | x == ztrue = []
            | otherwise   = [x]
zsome :: TypeSystem2 t => [AbsExpr t] -> AbsExpr t
zsome xs      = 
        case concatMap f xs of
            []  -> zfalse
            [x] -> x
            xs
                | ztrue `elem` xs -> ztrue
                | otherwise        -> FunApp (Fun [] "or" (replicate n bool) bool) xs
    where
        n = length xs
        f (FunApp (Fun [] "or" _ _) xs) = concatMap f xs
        f x
            | x == zfalse = []
            | otherwise   = [x]
zforall :: TypeSystem2 t 
        => [AbsVar t] 
        -> AbsExpr t 
        -> AbsExpr t 
        -> AbsExpr t
zforall [] x y  = zimplies x y
zforall vs x w@(Binder Forall us y z) 
    | x == ztrue = zforall (vs ++ us) y z
    | otherwise  = Binder Forall vs x w
zforall vs x w   
    |    x `elem` [ztrue, zfalse]
      && w `elem` [ztrue, zfalse] = zimplies x w
    | otherwise                   = Binder Forall vs x w
-- zforall vs' x w@(Binder Forall us y z) 
--         | x == ztrue = zforall (vs' ++ us') y z
--         | otherwise  = Binder Forall vs x w
--     where
--         vs  = map var_of vs'
--         us' = map Word us
-- zforall vs' x w   
--         |    x `elem` [ztrue, zfalse]
--           && w `elem` [ztrue, zfalse] = zimplies x w
--         | otherwise                   = Binder Forall vs x w
--     where
--         vs = map var_of vs'

zexists :: TypeSystem2 t 
        => [AbsVar t] 
        -> AbsExpr t 
        -> AbsExpr t 
        -> AbsExpr t
zexists [] x y = zand x y
zexists vs x w@(Binder Exists us y z) 
    | x == ztrue = zexists (vs ++ us) y z
    | otherwise  = Binder Exists vs x w
zexists vs x w   
    |    x `elem` [ztrue, zfalse]
      && w `elem` [ztrue, zfalse] = zand x w
    | otherwise                   = Binder Exists vs x w


zite :: ThreeExprP Type
zite       = typ_fun3 (Fun [] "ite" [bool,gA,gA] gA)

zjust :: OneExprP Type
zjust      = typ_fun1 (Fun [] "Just" [gA] (maybe_type gA))
znothing :: ExprP
znothing   = Right $ Cast (FunApp (Fun [] "Nothing" [] $ maybe_type gA) []) (maybe_type gA)

mznot :: TypeSystem2 t => OneExprP t
mznot me       = do
        e <- me
        case convert_to e of
            FunApp f [x] 
                | f == not_fun -> typ_fun1 not_fun (Right x)
            e -> typ_fun1 not_fun (Right e)
mzimplies :: TypeSystem2 t => TwoExprP t
mzimplies mx my = do
        x <- liftM convert_to mx
        y <- liftM convert_to my
        if      x == ztrue  then Right y
        else if y == ztrue  then Right ztrue
        else if x == zfalse then Right ztrue
        else if y == zfalse then Right $ znot x 
        else typ_fun2 (Fun [] "=>"  [bool,bool] bool) 
                (Right x) (Right y)
mzand :: TypeSystem2 t => TwoExprP t
mzand x y     = mzall [liftM convert_to x,liftM convert_to y]
mzor :: TypeSystem2 t => TwoExprP t
mzor x y      = mzsome [liftM convert_to x,liftM convert_to y]
mzfollows :: TypeSystem2 t => TwoExprP t
mzfollows x y = mzimplies y x
mztrue :: TypeSystem2 t
       => ExprPG t
mztrue        = Right ztrue
mzfalse :: TypeSystem2 t
        => ExprPG t
mzfalse       = Right zfalse
mzall :: TypeSystem2 t => [ExprPG t] -> ExprPG t
mzall []      = mztrue
mzall [x]     = x
mzall xs      = do
        xs <- forM xs $ zcast bool 
        return $ zall xs

mzsome :: TypeSystem2 t => [ExprPG t] -> ExprPG t
mzsome []     = mzfalse
mzsome [x]    = x
mzsome xs     = do
        xs <- forM xs $ zcast bool
        return $ zsome xs

mzforall :: TypeSystem2 t => [AbsVar t] 
         -> TwoExprP t
mzforall xs mx my = do
        x <- zcast bool $ liftM convert_to mx
        y <- zcast bool $ liftM convert_to my
        return $ zforall xs x y

mzexists :: TypeSystem2 t => [AbsVar t] 
         -> TwoExprP t
mzexists xs mx my = do
        x <- zcast bool $ liftM convert_to mx
        y <- zcast bool $ liftM convert_to my
        return $ zexists xs x y

zless :: Expr -> Expr -> Expr
zless        = fun2 $ Fun [] "<" [int,int] bool
-- zless        = fun2 mzless
zgreater :: Expr -> Expr -> Expr
zgreater     = fun2 $ Fun [] ">" [int,int] bool
-- zgreater     = fun2 mzgreater
zle :: Expr -> Expr -> Expr
zle          = fun2 $ Fun [] "<=" [int,int] bool
-- zle          = fun2 mzle
zge :: Expr -> Expr -> Expr
zge          = fun2 $ Fun [] ">=" [int,int] bool
-- zge          = fun2 mzge
zplus :: Expr -> Expr -> Expr
zplus        = fun2 $ Fun [] "+" [int,int] int
-- zplus        = fun2 mzplus
zminus :: Expr -> Expr -> Expr
zminus       = fun2 $ Fun [] "-" [int,int] int
-- zminus       = fun2 mzminus
zopp :: Expr -> Expr
zopp         = fun1 $ Fun [] "-" [int] int
-- zopp         = fun1 mzopp
ztimes :: Expr -> Expr -> Expr
ztimes       = fun2 $ Fun [] "*" [int,int] int
-- ztimes       = fun2 mztimes
zpow :: Expr -> Expr -> Expr
zpow         = fun2 $ Fun [] "^" [int,int] int
-- zpow         = fun2 mzpow
zselect :: TwoExprP Type
zselect      = typ_fun2 (Fun [] "select" [fun_type gA gB, gA] $ maybe_type gB)
zint :: Int -> Expr
zint n       = Const (IntVal n) int
zreal :: Double -> Expr
zreal n      = Const (RealVal n) real

int :: TypeSystem2 t => t
int  = make_type IntSort []
real :: TypeSystem2 t => t
real = make_type RealSort []
bool :: TypeSystem2 t => t
bool = make_type BoolSort []

mzless :: TypeSystem2 t => TwoExprP t
mzless        = typ_fun2 $ Fun [] "<" [int,int] bool
mzgreater :: TypeSystem2 t => TwoExprP t
mzgreater        = typ_fun2 $ Fun [] ">" [int,int] bool
mzle :: TypeSystem2 t => TwoExprP t
mzle          = typ_fun2 $ Fun [] "<=" [int,int] bool
mzge :: TypeSystem2 t => TwoExprP t
mzge          = typ_fun2 $ Fun [] ">=" [int,int] bool
mzplus :: TypeSystem2 t => TwoExprP t
mzplus        = typ_fun2 $ Fun [] "+" [int,int] int
mzminus :: TypeSystem2 t => TwoExprP t
mzminus       = typ_fun2 $ Fun [] "-" [int,int] int
mzopp :: TypeSystem2 t => ExprPG t -> ExprPG t
mzopp         = typ_fun1 $ Fun [] "-" [int] int
mztimes :: TypeSystem2 t => TwoExprP t
mztimes       = typ_fun2 $ Fun [] "*" [int,int] int
mzpow :: TypeSystem2 t => TwoExprP t
mzpow         = typ_fun2 $ Fun [] "^" [int,int] int

mzint :: Int -> ExprP
mzint n       = Right $ zint n

mzreal :: Int -> ExprP
mzreal x       = Right $ zreal $ fromIntegral x

mzpair :: ExprP -> ExprP -> ExprP
mzpair = typ_fun2 $ Fun [] "pair" [gA,gB] (pair_type gA gB)

gA :: Type
gA = GENERIC "a"
gB :: Type
gB = GENERIC "b"

var_of :: AbsExpr t -> AbsVar t
var_of (Word v) = v
var_of _ = error "var_of: expecting a variable expression"

var :: String -> Type -> (Either a Expr, Var)
var n t      = (Right $ Word $ v, v)
    where
        v = Var n t

prog_var :: String -> Type -> (Either a Expr, Either a Expr, Var)
prog_var n t = (Right $ Word v, Right $ Word $ prime v, v)
    where
        v = Var n t

prime :: Var -> Var
prime (Var n t) = Var (n ++ "@prime") t

fromJust :: Either [String] a -> a
fromJust (Right x)  = x
fromJust (Left msg) = error $ unlines $ map (format "error: {0}") msg

zapply :: ExprP -> ExprP -> ExprP
zapply  = typ_fun2 (Fun [gA,gB] "apply" [fun_type gA gB, gA] gB)

one_point_rule :: Expr -> Expr
one_point_rule (Binder Exists vs r t) = e
    where
        e  = zsome [ f $ zexists (filter (`S.member` fv) vs \\ M.keys inst) ztrue 
                        $ zall $ map (substitute 
                                        $ M.mapKeys name inst) ts
                   | (inst,ts,fv) <- insts ]
        insts = [ (M.unions $ map subst ts,ts,S.unions $ map used_var ts) | ts <- ts' ]
        subst (FunApp f xs)
                | name f == "=" = M.fromList $ rs
            where
                rs = do (i,j) <- [(0,1),(1,0)]
                        k <- maybeToList 
                            $ (xs !! i) `lookup` zip (map Word vs) vs
                        guard $ S.null $ S.intersection (S.fromList vs) (used_var $ xs !! j)
                        return (k, xs !! j)
        subst _ = M.empty
        f x
            | length ts' == 1   = rewrite one_point_rule x
            | otherwise         = one_point_rule x
        ts = conjuncts r ++ conjuncts t
        ts' = forM (map disjuncts ts) id
one_point_rule e = rewrite one_point_rule e

conjuncts :: TypeSystem t => AbsExpr t -> [AbsExpr t]
conjuncts (FunApp f xs) 
    | name f == "and" = xs
conjuncts x = [x]

disjuncts :: TypeSystem2 t => AbsExpr t -> [AbsExpr t]
disjuncts (FunApp f xs)
    | name f == "or"  = xs
    -- | name f == "=>"  = map znot (take 1 xs) ++ drop 1 xs
disjuncts x = [x]

zlift :: TypeSystem2 t => t -> AbsExpr t -> AbsExpr t
zlift t e = Lift e t
