module Logic.Const
where

    -- Modules    
import Logic.Expr
import Logic.Genericity

    -- Libraries
import Control.Monad

import Utilities.Format

fun1 f x           = FunApp f [x]
fun2 f x y         = FunApp f [x,y]
fun3 f x y z       = FunApp f [x,y,z]
fun4 f x0 x1 x2 x3 = FunApp f [x0,x1,x2,x3]
fun5 f x0 x1 x2 x3 x4 = FunApp f [x0,x1,x2,x3,x4]

typed_fun1 :: (Type -> Either String Fun) 
           -> Either String Expr 
           -> Either String Expr
typed_fun1 f mx           = do
        x  <- mx
        fn <- f $ type_of x
        return $ FunApp fn [x]

typed_fun2 :: (Type -> Type -> Either String Fun) 
           -> Either String Expr 
           -> Either String Expr 
           -> Either String Expr
typed_fun2 f mx my         = do
        x  <- mx
        y  <- my
        fn <- f (type_of x) (type_of y)
        return $ FunApp fn [x,y]

maybe1 f mx = do
        x <- mx :: Either String Expr
        return $ f x
maybe2 f mx my = do
        x <- mx :: Either String Expr
        y <- my :: Either String Expr
        return $ f x y
maybe3 f mx my mz = do
        x <- mx :: Either String Expr
        y <- my :: Either String Expr
        z <- mz :: Either String Expr
        return $ f x y z

znot         = fun1 $ Fun [] "not" [bool] bool
zimplies x y
    | x == ztrue  = y
    | y == ztrue  = ztrue
    | x == zfalse = ztrue
    | y == zfalse = znot x 
    | otherwise   = fun2 (Fun [] "=>"  [bool,bool] bool) x y
zand x y     = zall [x,y]
zor x y      = zsome [x,y]
zeq          = fun2 $ Fun [] "="   [GENERIC "a", GENERIC "a"] bool
mzeq         = typ_fun2 $ Fun [] "="   [GENERIC "a", GENERIC "a"] bool
zfollows     = fun2 $ Fun [] "follows" [bool,bool] bool
ztrue        = Const [] "true"  bool
zfalse       = Const [] "false" bool
zall xs      = 
        case concatMap f xs of
            []  -> ztrue
            [x] -> x
            xs  -> FunApp (Fun [] "and" (take n $ repeat bool) bool) xs
    where
        n = length xs
        f (FunApp (Fun [] "and" _ _) xs) = concatMap f xs
        f x
            | x == ztrue = []
            | otherwise   = [x]
zsome xs      = 
        case concatMap f xs of
            []  -> ztrue
            [x] -> x
            xs  -> FunApp (Fun [] "or" (take n $ repeat bool) bool) xs
    where
        n = length xs
        f (FunApp (Fun [] "or" _ _) xs) = concatMap f xs
        f x
            | x == zfalse = []
            | otherwise   = [x]
zforall [] x y  = zimplies x y
zforall vs x w@(Binder Forall us y z) 
    | x == ztrue = zforall (vs ++ us) y z
    | otherwise  = Binder Forall vs x w
zforall vs x w   = Binder Forall vs x w
zexists [] x y = zand x y
zexists vs x w@(Binder Exists us y z) 
    | x == ztrue = zexists (vs ++ us) y z
    | otherwise  = Binder Exists vs x w
zexists vs x w   = Binder Exists vs x w


zite       = typ_fun3 (Fun [] "ite" [bool,gA,gA] gA)

zjust      = typ_fun1 (Fun [] "Just" [gA] (maybe_type gA))
znothing   = Right (Const [] "Nothing" $ maybe_type gA)

mznot         = maybe1 znot
mzimplies     = maybe2 zimplies
mzand x y     = mzall [x,y]
mzor x y      = mzsome [x,y]
mzfollows     = maybe2 zfollows
mztrue        = Right ztrue
mzfalse       = Right zfalse
mzall []      = mztrue
mzall [x]     = x
mzall xs      = do
        xs <- forM xs id
        return $ zall xs
mzsome []     = mzfalse
mzsome [x]    = x
mzsome xs     = do
        xs <- forM xs id
        return $ zsome xs
mzforall xs mx my = do
        x <- zcast bool mx
        y <- zcast bool my
        return $ zforall xs x y
mzexists xs mx my = do
        x <- zcast bool mx
        y <- zcast bool my
        return $ zexists xs x y

zless        = fun2 $ Fun [] "<" [int,int] bool
zgreater     = fun2 $ Fun [] ">" [int,int] bool
zle          = fun2 $ Fun [] "<=" [int,int] bool
zge          = fun2 $ Fun [] ">=" [int,int] bool
zplus        = fun2 $ Fun [] "+" [int,int] int
zminus       = fun2 $ Fun [] "-" [int,int] int
zopp         = fun1 $ Fun [] "-" [int] int
ztimes       = fun2 $ Fun [] "*" [int,int] int
zpow         = fun2 $ Fun [] "^" [int,int] int
zselect      = typ_fun2 (Fun [] "select" [ARRAY gA gB, gA] gB)
zint n       = Const [] (show n) int
 
int  = USER_DEFINED IntSort []
real = USER_DEFINED RealSort []
bool = USER_DEFINED BoolSort []

mzless        = typ_fun2 $ Fun [] "<" [int,int] bool
mzle          = typ_fun2 $ Fun [] "<=" [int,int] bool
mzplus        = typ_fun2 $ Fun [] "+" [int,int] int
mzminus       = typ_fun2 $ Fun [] "-" [int,int] int
mzopp         = typ_fun1 $ Fun [] "-" [int] int
mztimes       = typ_fun2 $ Fun [] "*" [int,int] int
mzpow         = typ_fun2 $ Fun [] "^" [int,int] int

mzint n       = Right $ zint n

gena = GENERIC "a"
gA = GENERIC "a"
gB = GENERIC "b"

var n t      = (Right $ Word $ v, v)
    where
        v = Var n t
prog_var n t = (Right $ Word v, Right $ Word $ prime v, v)
    where
        v = Var n t

prime (Var n t) = Var (n ++ "@prime") t

fromJust (Right x) = x
fromJust (Left msg) = error $ format "error: {0}" (msg :: String)
