module Logic.Const where

    -- Modules    
import Logic.Expr
import Logic.Genericity

    -- Libraries
import Control.Monad

import Utilities.Format
import Utilities.Syntactic

fun1 :: Fun -> Expr -> Expr
fun1 f x           = FunApp f [x]
fun2 :: Fun -> Expr -> Expr -> Expr
fun2 f x y         = FunApp f [x,y]

typed_fun1 :: (Type -> Either String Fun) 
           -> ExprP
           -> ExprP
typed_fun1 f mx           = do
        x  <- mx
        fn <- f $ type_of x
        return $ FunApp fn [x]

typed_fun2 :: (Type -> Type -> Either String Fun) 
           -> ExprP
           -> ExprP
           -> ExprP
typed_fun2 f mx my         = do
        x  <- mx
        y  <- my
        fn <- f (type_of x) (type_of y)
        return $ FunApp fn [x,y]

maybe1 :: (Expr -> Expr)
       -> ExprP -> ExprP
maybe1 f mx = do
        x <- mx :: Either String Expr
        return $ f x
maybe2 :: (Expr -> Expr -> Expr)
       -> ExprP -> ExprP
       -> ExprP
maybe2 f mx my = do
        x <- mx :: Either String Expr
        y <- my :: Either String Expr
        return $ f x y
maybe3 :: (Expr -> Expr -> Expr -> Expr)
       -> ExprP -> ExprP
       -> ExprP -> ExprP
maybe3 f mx my mz = do
        x <- mx :: Either String Expr
        y <- my :: Either String Expr
        z <- mz :: Either String Expr
        return $ f x y z

toErrors :: LineInfo -> ExprP -> Either [Error] Expr
toErrors li m = case m of
        Right x -> Right x
        Left xs -> Left [Error xs li]

znot :: Expr -> Expr
znot         = fun1 $ Fun [] "not" [bool] bool
zimplies :: Expr -> Expr -> Expr
zimplies x y
    | x == ztrue  = y
    | y == ztrue  = ztrue
    | x == zfalse = ztrue
    | y == zfalse = znot x 
    | otherwise   = fun2 (Fun [] "=>"  [bool,bool] bool) x y
zand :: Expr -> Expr -> Expr
zand x y     = zall [x,y]
zor :: Expr -> Expr -> Expr
zor x y      = zsome [x,y]

zeq_fun :: Fun
zeq_fun      = Fun [] "="   [GENERIC "a", GENERIC "a"] bool

zeq_symb :: Expr -> Expr -> Expr
zeq_symb     = fun2 $ Fun [GENERIC "a"] "eq" [GENERIC "a", GENERIC "a"] bool
mzeq_symb :: ExprP -> ExprP -> ExprP
mzeq_symb    = typ_fun2 $ Fun [GENERIC "a"] "eq" [GENERIC "a", GENERIC "a"] bool

zeq :: Expr -> Expr -> Expr
zeq          = fun2 zeq_fun
mzeq :: ExprP -> ExprP -> ExprP
mzeq         = typ_fun2 zeq_fun
zfollows :: Expr -> Expr -> Expr
zfollows     = fun2 $ Fun [] "follows" [bool,bool] bool
ztrue :: Expr
ztrue        = Const [] "true"  bool
zfalse :: Expr
zfalse       = Const [] "false" bool
zall :: [Expr] -> Expr
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
zsome :: [Expr] -> Expr
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
zforall :: [Var] -> Expr -> Expr -> Expr
zforall [] x y  = zimplies x y
zforall vs x w@(Binder Forall us y z) 
    | x == ztrue = zforall (vs ++ us) y z
    | otherwise  = Binder Forall vs x w
zforall vs x w   = Binder Forall vs x w
zexists :: [Var] -> Expr -> Expr -> Expr
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

mznot :: ExprP -> ExprP
mznot         = maybe1 znot
mzimplies :: ExprP -> ExprP -> ExprP
mzimplies     = maybe2 zimplies
mzand :: ExprP -> ExprP -> ExprP
mzand x y     = mzall [x,y]
mzor :: ExprP -> ExprP -> ExprP
mzor x y      = mzsome [x,y]
mzfollows :: ExprP -> ExprP -> ExprP
mzfollows     = maybe2 zfollows
mztrue :: ExprP
mztrue        = Right ztrue
mzfalse :: ExprP
mzfalse       = Right zfalse
mzall :: [ExprP] -> ExprP
mzall []      = mztrue
mzall [x]     = x
mzall xs      = do
        xs <- forM xs $ zcast bool 
        return $ zall xs

mzsome :: [ExprP] -> ExprP
mzsome []     = mzfalse
mzsome [x]    = x
mzsome xs     = do
        xs <- forM xs $ zcast bool
        return $ zsome xs

mzforall :: [Var] -> ExprP -> ExprP -> ExprP
mzforall xs mx my = do
        x <- zcast bool mx
        y <- zcast bool my
        return $ zforall xs x y

mzexists :: [Var] -> ExprP -> ExprP -> ExprP
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
zselect      = typ_fun2 (Fun [] "select" [ARRAY gA gB, gA] gB)
zint :: Int -> Expr
zint n       = Const [] (show n) int
 
int :: Type
int  = USER_DEFINED IntSort []
real :: Type
real = USER_DEFINED RealSort []
bool :: Type
bool = USER_DEFINED BoolSort []

mzless :: ExprP -> ExprP -> ExprP
mzless        = typ_fun2 $ Fun [] "<" [int,int] bool
mzle :: ExprP -> ExprP -> ExprP
mzle          = typ_fun2 $ Fun [] "<=" [int,int] bool
mzplus :: ExprP -> ExprP -> ExprP
mzplus        = typ_fun2 $ Fun [] "+" [int,int] int
mzminus :: ExprP -> ExprP -> ExprP
mzminus       = typ_fun2 $ Fun [] "-" [int,int] int
mzopp :: ExprP -> ExprP
mzopp         = typ_fun1 $ Fun [] "-" [int] int
mztimes :: ExprP -> ExprP -> ExprP
mztimes       = typ_fun2 $ Fun [] "*" [int,int] int
mzpow :: ExprP -> ExprP -> ExprP
mzpow         = typ_fun2 $ Fun [] "^" [int,int] int

mzint :: Int -> ExprP
mzint n       = Right $ zint n

mzpair :: ExprP -> ExprP -> ExprP
mzpair = typ_fun2 $ Fun [] "pair" [gA,gB] (pair_type gA gB)

gena :: Type
gena = GENERIC "a"
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

