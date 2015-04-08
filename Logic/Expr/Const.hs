{-# LANGUAGE FlexibleContexts, TemplateHaskell #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
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

import Utilities.Syntactic

infixr 1 .==
infix 2 .=>
infixr 3 \/
infixr 3 /\
infix 4 .=
infix 4 .<=
infix 4 .<
infix 5 .+

type OneExpr t q = AbsExpr t q -> AbsExpr t q

type TwoExpr t q = AbsExpr t q -> AbsExpr t q -> AbsExpr t q

fun1 :: ( TypeSystem t )
     => AbsFun t 
     -> AbsExpr t q -> AbsExpr t q
fun1 f x           = FunApp f [x]
fun2 :: ( TypeSystem t  )
     => AbsFun t -> AbsExpr t q
     -> AbsExpr t q -> AbsExpr t q
fun2 f x y         = FunApp f [x,y]

no_errors2 :: ( TypeSystem t 
              , IsQuantifier q )
           => (TwoExprP t q)
           -> (TwoExpr t q)
no_errors2 f x y = either (error . unlines) id $ f (Right x) (Right y)

toErrors :: LineInfo -> ExprP -> Either [Error] Expr
toErrors li m = case m of
        Right x -> Right x
        Left xs -> Left $ map (`Error` li) xs

not_fun :: TypeSystem2 t => AbsFun t
not_fun = mk_fun [] "not" [bool] bool

znot :: (TypeSystem2 t, IsQuantifier q) => OneExpr t q
znot e = case e of 
            FunApp f [x]
                | f == not_fun -> x
                | otherwise    -> fun1 not_fun e
            e' -> fun1 not_fun e'
    -- znot         = fun1 mznot
zimplies :: (TypeSystem2 t, IsQuantifier q) => TwoExpr t q
zimplies x y = ($fromJust) $ mzimplies (Right x) (Right y)
zand :: (TypeSystem2 t, IsQuantifier q) => TwoExpr t q
zand x y     = zall [x, y]
zor :: (TypeSystem2 t, IsQuantifier q) => TwoExpr t q
zor x y      = zsome [x, y]

zeq_fun :: Fun
zeq_fun      = mk_fun [] "="  [gA, gA] bool

zeq_symb :: (IsQuantifier q) => TwoExpr Type q
zeq_symb     = no_errors2 mzeq_symb
mzeq_symb :: TwoExprP Type q
mzeq_symb    = typ_fun2 $ mk_fun [gA] "eq" [gA, gA] bool

zeq :: Expr -> Expr -> Expr
zeq          = no_errors2 mzeq
mzeq :: TwoExprP Type q
mzeq         = typ_fun2 zeq_fun

(.=) :: TwoExprP Type q
(.=) = mzeq
(.==) :: TwoExprP Type q
(.==) = mzeq

zfollows :: TypeSystem2 t => AbsExpr t q -> AbsExpr t q -> AbsExpr t q
zfollows     = fun2 $ mk_fun [] "follows" [bool,bool] bool
-- zfollows     = fun2 mzfollows
ztrue :: TypeSystem2 t => AbsExpr t q
ztrue        = FunApp (mk_fun [] "true" [] bool) []
zfalse :: TypeSystem2 t => AbsExpr t q
zfalse       = FunApp (mk_fun [] "false" [] bool) []
zall :: (TypeSystem2 t, IsQuantifier q) => [AbsExpr t q] -> AbsExpr t q
zall xs      = 
        case concatMap f xs of
            []  -> ztrue
            [x] -> x
            xs  
                | zfalse `elem` xs -> zfalse
                | otherwise -> FunApp (mk_fun [] "and" (take n $ repeat bool) bool) xs
    where
        n = length xs
        f (FunApp fun@(Fun [] "and" _ _ _) xs)
            | not $ isLifted fun = concatMap f xs
        f x
            | x == ztrue = []
            | otherwise   = [x]
zsome :: (TypeSystem2 t, IsQuantifier q) => [AbsExpr t q] -> AbsExpr t q
zsome xs      = 
        case concatMap f xs of
            []  -> zfalse
            [x] -> x
            xs
                | ztrue `elem` xs -> ztrue
                | otherwise        -> FunApp (mk_fun [] "or" (replicate n bool) bool) xs
    where
        n = length xs
        f (FunApp fun@(Fun [] "or" _ _ _) xs) 
            | not $ isLifted fun = concatMap f xs
        f x
            | x == zfalse = []
            | otherwise   = [x]
zforall :: (TypeSystem2 t, IsQuantifier q)
        => [AbsVar t] 
        -> AbsExpr t q
        -> AbsExpr t q
        -> AbsExpr t q
zforall [] x y  = zimplies x y
zforall vs x w@(Binder q us y z _) 
    | q == qForall = if x == ztrue
            then zforall (vs ++ us) y z
            else Binder qForall vs x w bool
zforall vs x w   
    |    x `elem` [ztrue, zfalse]
      && w `elem` [ztrue, zfalse] = zimplies x w
    | otherwise                   = Binder qForall vs x w bool

zexists :: (TypeSystem2 t, IsQuantifier q)
        => [AbsVar t] 
        -> AbsExpr t q
        -> AbsExpr t q
        -> AbsExpr t q
zexists [] x y = zand x y
zexists vs x w@(Binder q us y z _) 
    | q == qExists = if x == ztrue 
                        then zexists (vs ++ us) y z
                        else Binder qExists vs x w bool
zexists vs x w   
    |    x `elem` [ztrue, zfalse]
      && w `elem` [ztrue, zfalse] = zand x w
    | otherwise                   = Binder qExists vs x w bool

zquantifier :: HOQuantifier -> [Var] -> ExprP -> ExprP -> ExprP
zquantifier q vs r t = do
    r' <- zcast bool r
    t' <- zcast (termType q) t
    let tuple = ztuple_type (map var_type vs)
        rt    = exprType q tuple (type_of t')
    return $ Binder q vs r' t' rt

zite :: ThreeExprP Type q
zite       = typ_fun3 (mk_fun [] "ite" [bool,gA,gA] gA)

zjust :: OneExprP Type q
zjust      = typ_fun1 (mk_fun [] "Just" [gA] (maybe_type gA))

znothing :: ExprPG Type q
znothing   = Right $ Cast (FunApp (mk_fun [] "Nothing" [] $ maybe_type gA) []) (maybe_type gA)

mznot :: TypeSystem2 t => OneExprP t q
mznot me       = do
        e <- me
        case e of
            FunApp f [x] 
                | f == not_fun -> typ_fun1 not_fun (Right x)
            e -> typ_fun1 not_fun (Right e)
mzimplies :: TypeSystem2 t => TwoExprP t q
mzimplies mx my = do
        x <- mx
        y <- my
        if      x == ztrue  then Right y
        else if y == ztrue  then Right ztrue
        else if x == zfalse then Right ztrue
        else if y == zfalse then Right $ znot x
        else typ_fun2 (mk_fun [] "=>" [bool,bool] bool) 
                (Right x) (Right y)

(.=>) :: TypeSystem2 t => TwoExprP t q
(.=>) = mzimplies

mzand :: TypeSystem2 t => TwoExprP t q
mzand x y     = mzall [x,y]
mzor :: TypeSystem2 t => TwoExprP t q
mzor x y      = mzsome [x,y]

(\/) :: TypeSystem2 t => TwoExprP t q
(\/) = mzor

(/\) :: TypeSystem2 t => TwoExprP t q
(/\) = mzand

mzfollows :: TypeSystem2 t => TwoExprP t q
mzfollows x y = mzimplies y x
mztrue :: TypeSystem2 t
       => ExprPG t q
mztrue        = Right ztrue
mzfalse :: TypeSystem2 t
        => ExprPG t q
mzfalse       = Right zfalse
mzall :: (IsQuantifier q, TypeSystem2 t) => [ExprPG t q] -> ExprPG t q
mzall []      = mztrue
mzall [x]     = x
mzall xs      = do
        xs <- forM xs $ zcast bool 
        return $ zall xs

mzsome :: (IsQuantifier q, TypeSystem2 t) => [ExprPG t q] -> ExprPG t q
mzsome []     = mzfalse
mzsome [x]    = x
mzsome xs     = do
        xs <- forM xs $ zcast bool
        return $ zsome xs

mzforall :: (TypeSystem2 t, IsQuantifier q) 
         => [AbsVar t] 
         -> TwoExprP t q
mzforall xs mx my = do
        x <- zcast bool mx
        y <- zcast bool my
        return $ zforall xs x y

mzexists :: (TypeSystem2 t, IsQuantifier q)
         => [AbsVar t] 
         -> TwoExprP t q
mzexists xs mx my = do
        x <- zcast bool mx
        y <- zcast bool my
        return $ zexists xs x y

zless :: TypeSystem2 t => AbsExpr t q -> AbsExpr t q -> AbsExpr t q
zless        = fun2 $ mk_fun [] "<" [int,int] bool

zgreater :: TypeSystem2 t => AbsExpr t q -> AbsExpr t q -> AbsExpr t q
zgreater     = fun2 $ mk_fun [] ">" [int,int] bool

zle :: TypeSystem2 t => AbsExpr t q -> AbsExpr t q -> AbsExpr t q
zle          = fun2 $ mk_fun [] "<=" [int,int] bool

zge :: TypeSystem2 t => AbsExpr t q -> AbsExpr t q -> AbsExpr t q
zge          = fun2 $ mk_fun [] ">=" [int,int] bool

zplus :: TypeSystem2 t => AbsExpr t q -> AbsExpr t q -> AbsExpr t q
zplus        = fun2 $ mk_fun [] "+" [int,int] int

zminus :: TypeSystem2 t => AbsExpr t q -> AbsExpr t q -> AbsExpr t q
zminus       = fun2 $ mk_fun [] "-" [int,int] int

zopp :: TypeSystem2 t => AbsExpr t q -> AbsExpr t q
zopp         = fun1 $ mk_fun [] "-" [int] int

ztimes :: TypeSystem2 t => AbsExpr t q -> AbsExpr t q -> AbsExpr t q
ztimes       = fun2 $ mk_fun [] "*" [int,int] int

zpow :: TypeSystem2 t => AbsExpr t q -> AbsExpr t q -> AbsExpr t q
zpow         = fun2 $ mk_fun [] "^" [int,int] int

zselect :: TwoExprP Type q
zselect      = typ_fun2 (mk_fun [] "select" [array gA gB, gA] gB)

zint :: TypeSystem2 t => Int -> AbsExpr t q
zint n       = Const (IntVal n) int

zreal :: TypeSystem2 t => Double -> AbsExpr t q
zreal n      = Const (RealVal n) real

int :: TypeSystem t => t
int  = make_type IntSort []
real :: TypeSystem t => t
real = make_type RealSort []

mzless :: TypeSystem2 t => TwoExprP t q
mzless        = typ_fun2 $ mk_fun [] "<" [int,int] bool
(.<) :: TypeSystem2 t => TwoExprP t q
(.<) = mzless

mzgreater :: TypeSystem2 t => TwoExprP t q
mzgreater        = typ_fun2 $ mk_fun [] ">" [int,int] bool
mzle :: TypeSystem2 t => TwoExprP t q
mzle          = typ_fun2 $ mk_fun [] "<=" [int,int] bool
(.<=) :: TypeSystem2 t => TwoExprP t q
(.<=) = mzle

mzge :: TypeSystem2 t => TwoExprP t q
mzge          = typ_fun2 $ mk_fun [] ">=" [int,int] bool
mzplus :: TypeSystem2 t => TwoExprP t q
mzplus       = typ_fun2 $ mk_fun [] "+" [int,int] int
(.+) :: TypeSystem2 t => TwoExprP t q
(.+)       = mzplus

mzminus :: TypeSystem2 t => TwoExprP t q
mzminus       = typ_fun2 $ mk_fun [] "-" [int,int] int
mzopp :: (TypeSystem2 t,IsQuantifier q) => ExprPG t q -> ExprPG t q
mzopp         = typ_fun1 $ mk_fun [] "-" [int] int
mztimes :: TypeSystem2 t => TwoExprP t q
mztimes       = typ_fun2 $ mk_fun [] "*" [int,int] int
mzpow :: TypeSystem2 t => TwoExprP t q
mzpow         = typ_fun2 $ mk_fun [] "^" [int,int] int

mzint :: TypeSystem2 t => Int -> ExprPG t q 
mzint n       = Right $ zint n

mzreal :: TypeSystem2 t => Int -> ExprPG t q
mzreal x       = Right $ zreal $ fromIntegral x

mzpair :: ExprP -> ExprP -> ExprP
mzpair = typ_fun2 $ mk_fun [] "pair" [gA,gB] (pair_type gA gB)

gA :: Type
gA = GENERIC "a"
gB :: Type
gB = GENERIC "b"

var_of :: AbsExpr t q -> AbsVar t
var_of (Word v) = v
var_of _ = error "var_of: expecting a variable expression"

var :: String -> t -> (Either a (AbsExpr t q), AbsVar t)
var n t      = (Right $ Word $ v, v)
    where
        v = Var n t

prog_var :: String -> Type -> (Either a Expr, Either a Expr, Var)
prog_var n t = (Right $ Word v, Right $ Word $ prime v, v)
    where
        v = Var n t

prime :: Var -> Var
prime (Var n t) = Var (n ++ "@prime") t

zapply :: ExprP -> ExprP -> ExprP
zapply  = typ_fun2 (mk_fun [gA,gB] "apply" [fun_type gA gB, gA] gB)

one_point_rule :: forall t q. (IsQuantifier q, TypeSystem2 t) 
               => AbsExpr t q -> AbsExpr t q
one_point_rule (Binder q vs r t _) 
        | q == qExists = e
    where
        e  = zsome [ f $ zexists (filter (`S.member` fv) vs \\ M.keys inst) ztrue 
                        $ zall $ map (substitute 
                                        $ M.mapKeys name inst) ts
                   | (inst,ts,fv) <- insts ]
        
        insts :: [ ( M.Map (AbsVar t) (AbsExpr t q)
                   , [AbsExpr t q]
                   , S.Set (AbsVar t)) ]
        insts = [ (M.unions $ map subst ts,ts,S.unions $ map used_var ts) | ts <- ts' ]
        
        subst :: AbsExpr t q -> M.Map (AbsVar t) (AbsExpr t q)
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

conjuncts :: TypeSystem t => AbsExpr t q -> [AbsExpr t q]
conjuncts (FunApp f xs) 
    | name f == "and" = xs
conjuncts x = [x]

disjuncts :: TypeSystem2 t => AbsExpr t q -> [AbsExpr t q]
disjuncts (FunApp f xs)
    | name f == "or"  = xs
    -- | name f == "=>"  = map znot (take 1 xs) ++ drop 1 xs
disjuncts x = [x]

zlift :: TypeSystem2 t => t -> AbsExpr t q -> AbsExpr t q
zlift t e = Lift e t

const_fun :: Fun
const_fun = mk_fun [gA,gB] "const" [gB] (array gA gB)

zconst :: ExprP -> ExprP
zconst = typ_fun1 const_fun

ident_fun :: Fun
ident_fun = mk_fun [gA] "ident" [] (array gA gA)

zident :: ExprP
zident = Right $ FunApp ident_fun []
