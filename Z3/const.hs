module Z3.Const
where

    -- Modules
import UnitB.Genericity
    
import Z3.Def

    -- Libraries
import Control.Monad

import Data.List as L ( tails, map )
import Data.Map hiding (foldl)

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

--fun3 f x y z       = FunApp f [x,y,z]
--fun4 f x0 x1 x2 x3 = FunApp f [x0,x1,x2,x3]
--fun5 f x0 x1 x2 x3 x4 = FunApp f [x0,x1,x2,x3,x4]

znot         = fun1 $ Fun [] "not" [BOOL] BOOL
zimplies     = fun2 $ Fun [] "=>"  [BOOL,BOOL] BOOL
--zand         = fun2 $ Fun [] "and" [BOOL,BOOL] BOOL
zand x y     = zall [x,y]
--zor          = fun2 $ Fun [] "or"  [BOOL,BOOL] BOOL
zor x y      = zsome [x,y]
zeq          = fun2 $ Fun [] "="   [GENERIC "a", GENERIC "a"] BOOL
mzeq         = typ_fun2 $ Fun [] "="   [GENERIC "a", GENERIC "a"] BOOL
zfollows     = fun2 $ Fun [] "follows" [BOOL,BOOL] BOOL
ztrue        = Const [] "true"  BOOL
zfalse       = Const [] "false" BOOL
zall []      = ztrue
zall [x]     = x
zall xs      = FunApp (Fun [] "and" (take n $ repeat BOOL) BOOL) $ concatMap f xs
    where
        n = length xs
        f (FunApp (Fun [] "and" _ BOOL) xs) = concatMap f xs
        f x = [x]
zsome []     = zfalse
zsome [x]    = x
zsome xs     = FunApp (Fun [] "or" (take n $ repeat BOOL) BOOL) $ concatMap f xs
    where
        n = length xs
        f (FunApp (Fun [] "or" _ BOOL) xs) = concatMap f xs
        f x = [x]
--zall (x:xs)  = foldl zand x xs
zforall      = Binder Forall
zexists      = Binder Exists

mznot         = maybe1 znot
mzimplies     = maybe2 zimplies
--mzand         = maybe2 zand
mzand x y     = mzall [x,y]
--mzor          = maybe2 zor
mzor x y      = mzsome [x,y]
--mzeq          = maybe2 zeq
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
mzforall xs   = maybe1 $ zforall xs
mzexists xs   = maybe1 $ zexists xs

zless        = fun2 $ Fun [] "<" [int,int] BOOL
zgreater     = fun2 $ Fun [] ">" [int,int] BOOL
zle          = fun2 $ Fun [] "<=" [int,int] BOOL
zge          = fun2 $ Fun [] ">=" [int,int] BOOL
zplus        = fun2 $ Fun [] "+" [int,int] int
zminus       = fun2 $ Fun [] "-" [int,int] int
zopp         = fun1 $ Fun [] "-" [int] int
ztimes       = fun2 $ Fun [] "*" [int,int] int
zpow         = fun2 $ Fun [] "^" [int,int] int
zint n       = Const [] (show n) int

int = USER_DEFINED IntSort []

mzless        = typ_fun2 $ Fun [] "<" [int,int] BOOL
mzgreater     = typ_fun2 $ Fun [] ">" [int,int] BOOL
mzle          = typ_fun2 $ Fun [] "<=" [int,int] BOOL
mzge          = typ_fun2 $ Fun [] ">=" [int,int] BOOL
mzplus        = typ_fun2 $ Fun [] "+" [int,int] int
mzminus       = typ_fun2 $ Fun [] "-" [int,int] int
mzopp         = typ_fun1 $ Fun [] "-" [int] int
mztimes       = typ_fun2 $ Fun [] "*" [int,int] int
mzpow         = typ_fun2 $ Fun [] "^" [int,int] int

--mzless        = maybe2 zless
--mzgreater     = maybe2 zgreater
--mzle          = maybe2 zle
--mzge          = maybe2 zge
--mzplus        = maybe2 zplus
--mzminus       = maybe2 zminus
--mzopp         = fun1 $ Fun [] "-" [INT] INT
--mztimes       = maybe2 ztimes
--mzpow         = maybe2 zpow
mzint n       = Right $ zint n

gena = GENERIC "a"

var n t      = (Right $ Word $ v, v)
    where
        v = Var n t
prog_var n t = (Right $ Word v, Right $ Word $ prime v, v)
    where
        v = Var n t

prime (Var n t) = Var (n ++ "@prime") t

fromJust (Right x) = x
fromJust (Left msg) = error $ format "error: {0}" msg
