module Logic.Expr.TypeChecking where

    -- Modules
import Logic.Expr.Classes
import Logic.Expr.Const
import Logic.Expr.Expr
import Logic.Expr.Genericity
import Logic.Expr.Type
import Logic.Expr.Label

    -- Libraries
import Control.Monad.Reader
import Control.Lens ((^.),view)

import Data.Either
import Data.List
import qualified Data.Map as M
import qualified Data.Set as S

import Text.Printf

stripTypes :: GenExpr t0 t1 q -> GenExpr () t1 q
stripTypes (Word (Var n _))  = Word (Var n ())
stripTypes (Const n _)       = Const n ()
stripTypes (FunApp fun args) = FunApp fun' (map stripTypes args)
    where
        f = map $ const ()
        fun' = Fun (f ts) n lf (f targs) ()
        Fun ts n lf targs _rt = fun
stripTypes (Binder q vs r t _) = Binder q (f vs) (stripTypes r) (stripTypes t) ()
    where
        f = map (\(Var n _) -> (Var n ()))
stripTypes (Cast e t) = Cast (stripTypes e) t
stripTypes (Lift e t) = Lift (stripTypes e) t

bind :: Maybe a -> String -> Either [String] a
bind (Just x) _  = Right x
bind Nothing msg = Left [msg]

bindAll :: [b] -> (b -> Maybe a) -> (b -> String) -> Either [String] [a]
bindAll xs f msg 
        | all isRight ys = Right $ rights ys
        | otherwise      = Left $ concat $ lefts ys
    where
        ys = map g xs
        g x = maybe (Left [msg x]) Right (f x)

parCheck :: Either [String] a -> Either [String] b -> Either [String] (a,b)
parCheck (Right x) (Right y) = Right (x,y)
parCheck mx my = Left $ errors mx ++ errors my
    where
        errors (Left xs) = xs
        errors (Right _) = []

getElementType :: Type -> Either [String] Type
getElementType t = runReaderT (getElementType_aux t t) 1

getElementType_aux :: Type -> Type -> ReaderT Int (Either [String]) Type
getElementType_aux orgt (VARIABLE _) = lift $ Left [[printf|Expecting array type but found %s|] $ show orgt]
getElementType_aux orgt (GENERIC _)  = lift $ Left [[printf|Expecting array type but found %s|] $ show orgt]
getElementType_aux _ (Gen (Sort "Array" "Array" 2) [_x,y]) = return y
getElementType_aux orgt (Gen (DefSort _ _ args t) xs) = do
    n <- ask
    if n == 0 
        then lift $ Left [[printf|Expecting array type but found %s|] $ show orgt]
        else local (-1 +) $ getElementType_aux orgt $ instantiate (M.fromList $ zip args xs) t
getElementType_aux orgt (Gen _ _) = lift $ Left [[printf|Expecting array type but found %s|] $ show orgt]

newContext :: [UntypedVar] -> Context -> Context
newContext us c@(Context ss vs fs ds dums) = Context ss (M.union vs' vs) fs ds dums
    where
        vs' = newDummies us c

newDummies :: [UntypedVar] -> Context -> M.Map String Var
newDummies us (Context _ _ _ _ dums) = vs'
        -- Context ss vs' fs ds dums
    where
        vs' = M.differenceWith favorSecond
                (symbol_table (map addType us)) dums
        addType (Var n ()) = Var n (GENERIC "a") 
        favorSecond _x y = Just y

checkTypes :: Context -> UntypedExpr -> Either [String] Expr
checkTypes c (Word (Var n ())) = do
    v <- bind (n `M.lookup` (c^.constants))
        ([printf|%s is undeclared|] )
    return $ Word v
checkTypes _ (Const n ()) = do
    let t = case n of 
             RealVal _ -> real
             IntVal _  -> int
    return (Const n t)
checkTypes c (FunApp f args) = do
    let Fun _ n _ _ _ = f ;
        targs = map (checkTypes c) args
    tfun <- bind (n `M.lookup` (c^.functions))
        ([printf|%s is undeclared|] ) ;
    check_type tfun targs
checkTypes c (Cast e t) = do
    e' <- zcast t $ checkTypes c e
    return (Cast e' t)
checkTypes c (Lift e t) = do
    elt <- getElementType t
    e'  <- zcast elt $ checkTypes c e
    return (Lift e' t)
checkTypes c' (Binder q vs' r t _) = do
    let c  = newContext vs' c'
        ns = map (view name) vs' :: [String]
        vs = M.ascElems $ newDummies vs' c'
    (r'',t'') <- parCheck 
        (zcast bool $ checkTypes c r) 
        (zcast (termType q) $ checkTypes c t)
    let vars = used_var r'' `S.union` used_var t''
        v_type = id -- L.filter ((1 <) . S.size . snd) 
                    $ zip vs
                    $ map f ns 
        f x = S.filter (\y -> x == view name y) vars
    ts <- forM v_type $ \((Var x t),xs) -> do
        let ys = map var_type $ S.toList xs
        t' <- maybe 
            (fail $ [printf|Inconsistent type for %s: %s|] 
                    x
                    $ intercalate "," $ map pretty ys)
            return
            $ foldM common gA ys
        t' <- if t' == gA 
            then return t
            else return t'
        return (x, Var x t')
    let ts' = M.map Word $ M.fromList ts
        r' = substitute ts' r''
        t' = substitute ts' t''
        vs' = map snd ts
        tuple = ztuple_type $ map var_type vs'
    return (Binder q vs' r' t' (exprType q tuple (type_of t')))

    -- return $ FunApp _ _
-- checkTypes c (Const xs n ()) = do
--  _