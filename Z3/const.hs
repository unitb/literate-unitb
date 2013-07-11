module Z3.Const where

import Z3.Def

fun1 f x           = FunApp f [x]
fun2 f x y         = FunApp f [x,y]
fun3 f x y z       = FunApp f [x,y,z]
fun4 f x0 x1 x2 x3 = FunApp f [x0,x1,x2,x3]
fun5 f x0 x1 x2 x3 x4 = FunApp f [x0,x1,x2,x3,x4]

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

zapply       = fun2 $ Fun "select" [
        ARRAY (GENERIC "b") $ GENERIC "a", 
        GENERIC "b"] $ 
    GENERIC "a"
zovl        = fun3 $ Fun "store" [
        ARRAY (GENERIC "b") $ GENERIC "a", 
        GENERIC "b", GENERIC "a"] $ 
    ARRAY (GENERIC "b") $ GENERIC "a"

var n t = (Word $ Var n t, Var n t)
prog_var n t = (Word v, Word $ prime v, v)
    where
        v = Var n t

prime (Var n t) = Var (n ++ "_prime") t