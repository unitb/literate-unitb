module Z3.Const where

import Data.List ( tails )
import Data.Map hiding (foldl)

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
zelem        = fun2 $ Fun "select" [SET (GENERIC "a"), GENERIC "a"] BOOL

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

mk_expr Plus x y    = x `zplus` y
mk_expr Mult x y    = x `ztimes` y
mk_expr And x y     = x `zand` y 
mk_expr Power x y   = x `zpow` y

mk_expr Equal x y      = x `zeq` y
mk_expr Implies x y    = x `zimplies` y 
mk_expr Follows x y    = x `zfollows` y 
mk_expr Leq x y        = x `zle` y
mk_expr Membership x y = x `zelem` y

chain Equal x         = x
chain x Equal         = x
chain Implies Implies = Implies
chain Follows Follows = Follows
chain Leq Leq         = Leq
chain _ _             = error "operators cannot be chained"


data Assoc = LeftAssoc | RightAssoc | Ambiguous
    deriving Show

associativity :: [([Operator],Assoc)]
associativity = [
        ([Power],Ambiguous),
        ([Mult],LeftAssoc),
        ([Plus],LeftAssoc),
        ([Equal,Leq],Ambiguous),
        ([And],LeftAssoc),
        ([Implies,Follows],Ambiguous) ]

prod (xs,z) = [ ((x,y),z) | x <- xs, y <- xs ]

pairs = fromList (concat (do
            ((x,_),xs) <- zip a $ tail $ tails a
            (y,_)      <- xs
            a          <- x
            b          <- y
            return [
                ((a,b),LeftAssoc),
                ((b,a),RightAssoc) ])
        ++ concatMap prod a    )
    where
        a = associativity

assoc x y = pairs ! (x,y)