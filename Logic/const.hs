module Logic.Const where

    -- Modules    
import Logic.Expr
import Logic.Genericity
import Logic.Type

    -- Libraries
import Control.Monad

import Utilities.Format
import Utilities.Syntactic

fun1 :: TypeSystem t 
     => AbsFun t 
     -> AbsExpr t -> AbsExpr t
fun1 f x           = FunApp f [x]
fun2 :: TypeSystem t 
     => AbsFun t -> AbsExpr t 
     -> AbsExpr t -> AbsExpr t
fun2 f x y         = FunApp f [x,y]

typed_fun1 :: (Type -> Either String Fun) 
           -> ExprP
           -> ExprP
typed_fun1 f mx           = do
        x  <- mx
        fn <- f $ type_of x
        return $ FunApp fn [x]

typed_fun2 :: TypeSystem t 
           => (t -> t -> Either String (AbsFun t)) 
           -> ExprPG t
           -> ExprPG t
           -> ExprPG t
typed_fun2 f mx my         = do
        x  <- mx
        y  <- my
        fn <- f (type_of x) (type_of y)
        return $ FunApp fn [x,y]

maybe1 :: TypeSystem t 
       => (AbsExpr t -> AbsExpr t)
       -> ExprPG t -> ExprPG t
maybe1 f mx = do
        x <- mx
        return $ f x
maybe2 :: TypeSystem t 
       => (AbsExpr t -> AbsExpr t -> AbsExpr t)
       -> ExprPG t -> ExprPG t
       -> ExprPG t
maybe2 f mx my = do
        x <- mx
        y <- my
        return $ f x y
maybe3 :: TypeSystem t
       => (   AbsExpr t -> AbsExpr t 
           -> AbsExpr t -> AbsExpr t)
       -> ExprPG t -> ExprPG t
       -> ExprPG t -> ExprPG t
maybe3 f mx my mz = do
        x <- mx
        y <- my
        z <- mz
        return $ f x y z

no_errors2 :: TypeSystem t 
           => (   ExprPG t -> ExprPG t
               -> ExprPG t )
           -> (AbsExpr t -> AbsExpr t -> AbsExpr t)
no_errors2 f x y = either error id $ f (Right x) (Right y)

toErrors :: LineInfo -> ExprP -> Either [Error] Expr
toErrors li m = case m of
        Right x -> Right x
        Left xs -> Left [Error xs li]

znot :: TypeSystem2 t => AbsExpr t -> AbsExpr t
znot         = fun1 $ Fun [] "not" [bool] bool
zimplies :: TypeSystem2 t => AbsExpr t -> AbsExpr t -> AbsExpr t
zimplies x y
    | x == ztrue  = y
    | y == ztrue  = ztrue
    | x == zfalse = ztrue
    | y == zfalse = znot x 
    | otherwise   = fun2 (Fun [] "=>"  [bool,bool] bool) x y
zand :: TypeSystem2 t => AbsExpr t -> AbsExpr t -> AbsExpr t
zand x y     = zall [x,y]
zor :: TypeSystem2 t => AbsExpr t -> AbsExpr t -> AbsExpr t
zor x y      = zsome [x,y]

zeq_fun :: Fun
zeq_fun      = Fun [] "="   [gA, gA] bool

zeq_symb :: Expr -> Expr -> Expr
zeq_symb     = no_errors2 mzeq_symb
mzeq_symb :: ExprP -> ExprP -> ExprP
mzeq_symb    = typ_fun2 $ Fun [gA] "eq" [gA, gA] bool

zeq :: Expr -> Expr -> Expr
zeq          = no_errors2 mzeq
mzeq :: ExprP -> ExprP -> ExprP
mzeq         = typ_fun2 zeq_fun
zfollows :: TypeSystem2 t => AbsExpr t -> AbsExpr t -> AbsExpr t
zfollows     = fun2 $ Fun [] "follows" [bool,bool] bool
ztrue :: TypeSystem2 t => AbsExpr t
ztrue        = Const [] "true"  bool
zfalse :: TypeSystem2 t => AbsExpr t
zfalse       = Const [] "false" bool
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
            []  -> ztrue
            [x] -> x
            xs
                | ztrue `elem` xs -> ztrue
                | otherwise        -> FunApp (Fun [] "or" (take n $ repeat bool) bool) xs
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
zforall vs x w   = Binder Forall vs x w
zexists :: TypeSystem2 t 
        => [AbsVar t] 
        -> AbsExpr t 
        -> AbsExpr t 
        -> AbsExpr t
zexists [] x y = zand x y
zexists vs x w@(Binder Exists us y z) 
    | x == ztrue = zexists (vs ++ us) y z
    | otherwise  = Binder Exists vs x w
zexists vs x w   = Binder Exists vs x w


zite :: ExprP -> ExprP -> ExprP -> ExprP
zite       = typ_fun3 (Fun [] "ite" [bool,gA,gA] gA)

zjust :: ExprP -> ExprP
zjust      = typ_fun1 (Fun [] "Just" [gA] (maybe_type gA))
znothing :: ExprP
znothing   = Right (Const [] "Nothing" $ maybe_type gA)

mznot :: TypeSystem2 t => ExprPG t -> ExprPG t
mznot         = maybe1 znot
mzimplies :: TypeSystem2 t => ExprPG t -> ExprPG t -> ExprPG t
mzimplies     = maybe2 zimplies
mzand :: TypeSystem2 t => ExprPG t -> ExprPG t -> ExprPG t
mzand x y     = mzall [x,y]
mzor :: TypeSystem2 t => ExprPG t -> ExprPG t -> ExprPG t
mzor x y      = mzsome [x,y]
mzfollows :: TypeSystem2 t => ExprPG t -> ExprPG t -> ExprPG t
mzfollows     = maybe2 zfollows
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
         -> ExprPG t -> ExprPG t -> ExprPG t
mzforall xs mx my = do
        x <- zcast bool mx
        y <- zcast bool my
        return $ zforall xs x y

mzexists :: TypeSystem2 t => [AbsVar t] 
         -> ExprPG t -> ExprPG t -> ExprPG t
mzexists xs mx my = do
        x <- zcast bool mx
        y <- zcast bool my
        return $ zexists xs x y

zless :: Expr -> Expr -> Expr
zless        = fun2 $ Fun [] "<" [int,int] bool
zgreater :: Expr -> Expr -> Expr
zgreater     = fun2 $ Fun [] ">" [int,int] bool
zle :: Expr -> Expr -> Expr
zle          = fun2 $ Fun [] "<=" [int,int] bool
zge :: Expr -> Expr -> Expr
zge          = fun2 $ Fun [] ">=" [int,int] bool
zplus :: Expr -> Expr -> Expr
zplus        = fun2 $ Fun [] "+" [int,int] int
zminus :: Expr -> Expr -> Expr
zminus       = fun2 $ Fun [] "-" [int,int] int
zopp :: Expr -> Expr
zopp         = fun1 $ Fun [] "-" [int] int
ztimes :: Expr -> Expr -> Expr
ztimes       = fun2 $ Fun [] "*" [int,int] int
zpow :: Expr -> Expr -> Expr
zpow         = fun2 $ Fun [] "^" [int,int] int
zselect :: ExprP -> ExprP -> ExprP
zselect      = typ_fun2 (Fun [] "select" [fun_type gA gB, gA] $ maybe_type gB)
zint :: Int -> Expr
zint n       = Const [] (show n) int
 
int :: TypeSystem2 t => t
int  = make_type IntSort []
real :: TypeSystem2 t => t
real = make_type RealSort []
bool :: TypeSystem2 t => t
bool = make_type BoolSort []

mzless :: TypeSystem2 t => ExprPG t -> ExprPG t -> ExprPG t
mzless        = typ_fun2 $ Fun [] "<" [int,int] bool
mzle :: TypeSystem2 t => ExprPG t -> ExprPG t -> ExprPG t
mzle          = typ_fun2 $ Fun [] "<=" [int,int] bool
mzplus :: TypeSystem2 t => ExprPG t -> ExprPG t -> ExprPG t
mzplus        = typ_fun2 $ Fun [] "+" [int,int] int
mzminus :: TypeSystem2 t => ExprPG t -> ExprPG t -> ExprPG t
mzminus       = typ_fun2 $ Fun [] "-" [int,int] int
mzopp :: TypeSystem2 t => ExprPG t -> ExprPG t
mzopp         = typ_fun1 $ Fun [] "-" [int] int
mztimes :: TypeSystem2 t => ExprPG t -> ExprPG t -> ExprPG t
mztimes       = typ_fun2 $ Fun [] "*" [int,int] int
mzpow :: TypeSystem2 t => ExprPG t -> ExprPG t -> ExprPG t
mzpow         = typ_fun2 $ Fun [] "^" [int,int] int

mzint :: Int -> ExprP
mzint n       = Right $ zint n

mzpair :: ExprP -> ExprP -> ExprP
mzpair = typ_fun2 $ Fun [] "pair" [gA,gB] (pair_type gA gB)

gA :: Type
gA = GENERIC "a"
gB :: Type
gB = GENERIC "b"

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

fromJust :: Either String a -> a
fromJust (Right x)  = x
fromJust (Left msg) = error $ format "error: {0}" (msg :: String)

zapply :: ExprP -> ExprP -> ExprP
zapply  = typ_fun2 (Fun [gA,gB] "apply" [fun_type gA gB, gA] gB)

