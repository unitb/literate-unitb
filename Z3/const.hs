module Z3.Const where

import Data.List as L ( tails, map )
import Data.Map hiding (foldl)

import Z3.Def
    

fun1 f x           = FunApp f [x]
fun2 f x y         = FunApp f [x,y]
fun3 f x y z       = FunApp f [x,y,z]
fun4 f x0 x1 x2 x3 = FunApp f [x0,x1,x2,x3]
fun5 f x0 x1 x2 x3 x4 = FunApp f [x0,x1,x2,x3,x4]

typed_fun1 f mx           = do
        x  <- mx
        fn <- f $ type_of x
        return $ FunApp fn [x]
typed_fun2 f mx my         = do
        x  <- mx
        y  <- my
        fn <- f (type_of x) (type_of y)
        return $ FunApp fn [x,y]
maybe1 f mx = do
        x <- mx :: Maybe Expr
        return $ f x
maybe2 f mx my = do
        x <- mx :: Maybe Expr
        y <- my :: Maybe Expr
        return $ f x y
maybe3 f mx my mz = do
        x <- mx :: Maybe Expr
        y <- my :: Maybe Expr
        z <- mz :: Maybe Expr
        return $ f x y z

--fun3 f x y z       = FunApp f [x,y,z]
--fun4 f x0 x1 x2 x3 = FunApp f [x0,x1,x2,x3]
--fun5 f x0 x1 x2 x3 x4 = FunApp f [x0,x1,x2,x3,x4]

znot         = fun1 $ Fun "not" [BOOL] BOOL
zimplies     = fun2 $ Fun "=>"  [BOOL,BOOL] BOOL
zand         = fun2 $ Fun "and" [BOOL,BOOL] BOOL
zor          = fun2 $ Fun "or"  [BOOL,BOOL] BOOL
zeq          = fun2 $ Fun "="   [GENERIC "a", GENERIC "a"] BOOL
zfollows     = fun2 $ Fun "follows" [BOOL,BOOL] BOOL
ztrue        = Const "true"  BOOL
zfalse       = Const "false" BOOL
zall (x:xs)  = foldl zand x xs
zall []      = ztrue
zforall      = Binder Forall
zexists      = Binder Exists

mznot         = maybe1 znot
mzimplies     = maybe2 zimplies
mzand         = maybe2 zand
mzor          = maybe2 zor
mzeq          = maybe2 zeq
mzfollows     = maybe2 zfollows
mztrue        = Just ztrue
mzfalse       = Just zfalse
mzall (x:xs)  = foldl mzand x xs
mzall []      = mztrue
mzforall xs   = maybe1 $ zforall xs
mzexists xs   = maybe1 $ zexists xs

zless        = fun2 $ Fun "<" [INT,INT] BOOL
zgreater     = fun2 $ Fun ">" [INT,INT] BOOL
zle          = fun2 $ Fun "<=" [INT,INT] BOOL
zge          = fun2 $ Fun ">=" [INT,INT] BOOL
zplus        = fun2 $ Fun "+" [INT,INT] INT
zminus       = fun2 $ Fun "-" [INT,INT] INT
zopp         = fun1 $ Fun "-" [INT] INT
ztimes       = fun2 $ Fun "*" [INT,INT] INT
zpow         = fun2 $ Fun "^" [INT,INT] INT
zint n       = Const (show n) INT

mzless        = maybe2 zless
mzgreater     = maybe2 zgreater
mzle          = maybe2 zle
mzge          = maybe2 zge
mzplus        = maybe2 zplus
mzminus       = maybe2 zminus
mzopp         = fun1 $ Fun "-" [INT] INT
mztimes       = maybe2 ztimes
mzpow         = maybe2 zpow
mzint n       = Just $ zint n

gena = GENERIC "a"

zapply       = fun2 $ Fun "select" [
        ARRAY (GENERIC "b") $ GENERIC "a", 
        GENERIC "b"] $ 
    GENERIC "a"
zovl        = fun3 $ Fun "store" [
        ARRAY (GENERIC "b") $ GENERIC "a", 
        GENERIC "b", GENERIC "a"] $ 
    ARRAY (GENERIC "b") $ GENERIC "a"

mzapply = maybe2 zapply
mzovl = maybe3 zovl

var n t = (Just $ Word $ Var n t, Var n t)
prog_var n t = (Just $ Word v, Just $ Word $ prime v, v)
    where
        v = Var n t

prime (Var n t) = Var (n ++ "@prime") t

