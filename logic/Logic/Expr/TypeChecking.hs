module Logic.Expr.TypeChecking where

    -- Modules
import Logic.Expr.Classes
import Logic.Expr.Context
import Logic.Expr.Expr
import Logic.Expr.Genericity
import Logic.Expr.Type
import Logic.Names
import Logic.Theories.SetTheory

    -- Libraries

import Control.Lens 
        ((^.),(^?),(&),(%~)
        ,_Left,_Right,view)
import Control.Lens.Misc
import Control.Monad
-- import Control.Precondition

import Data.Either
import Data.Either.Combinators (mapLeft)
import Data.List
import qualified Data.Map.Class as M
import qualified Data.Set as S

import Text.Pretty
import Text.Printf.TH

import Utilities.Syntactic

stripTypes :: GenExpr n t0 t1 q -> GenExpr n () t1 q
stripTypes (Word (Var n _))  = Word (Var n ())
stripTypes (Lit n _)         = Lit n ()
stripTypes (FunApp fun args) = FunApp fun (map stripTypes args)
stripTypes (Binder q vs r t _) = Binder q (f vs) (stripTypes r) (stripTypes t) ()
    where
        f = map (\(Var n _) -> (Var n ()))
stripTypes (Cast ct e t) = Cast ct (stripTypes e) t
stripTypes (Lift e t) = Lift (stripTypes e) t
stripTypes (Record r _) = Record (stripTypes <$> r) ()

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

newContext :: [UntypedVar] -> Context -> Context
newContext us c@(Context ss vs fs ds dums) = Context ss (M.union vs' vs) fs ds dums
    where
        vs' = newDummies us c

newDummies :: [UntypedVar] -> Context -> M.Map Name Var
newDummies us (Context _ _ _ _ dums) = vs'
        -- Context ss vs' fs ds dums
    where
        vs' = M.differenceWith favorSecond
                (symbol_table (map addType us)) dums
        addType (Var n ()) = Var n gA 
        favorSecond _x y = Just y

tryBoth :: Either a b -> Either a b -> Either a b
tryBoth x@(Right _) _ = x
tryBoth (Left _) x    = x

checkTypes :: Maybe GenericType
           -> Context
           -> UntypedExpr
           -> StringLi
           -> Either [Error] Expr
checkTypes expected_t c ue xs = do
    e <- (checkTypes' c ue) & _Left.traverse %~ strToErr
                            & _Right %~ normalize_generics
    case expected_t of
        Just t  -> mapLeft (\xs' -> map (`Error` li) xs') $ zcast t (Right e)
        Nothing -> return e
    where
        li = line_info xs
        strToErr = \msg -> Error msg li

checkTypes' :: Context -> UntypedExpr -> Either [String] Expr
checkTypes' c (Word (Var n ())) = do
    v <- bind (n `M.lookup` (c^.constants))
        ([printf|%s is undeclared|] $ pretty n)
    return $ Word v
checkTypes' _ (Lit n ()) = do
    let t = case n of 
             RealVal _ -> real
             IntVal _  -> int
    return (Lit n t)
checkTypes' c (FunApp f args) = do
    let targs = map (checkTypes' c) args
    check_type f targs
checkTypes' c (Record (FieldLookup e field) _) = do
    e' <- checkTypes' c e
    let t = type_of e'
    trecs <- bind (t^?fieldTypes)
        ([printf|While looking up field %s: %s is not a record|] (pretty field) (pretty e))
    t' <- bind (field `M.lookup` trecs)
        ([printf|Record %s of type %s has no field %s|] (pretty e) (pretty t) (pretty field))
    return (Record (FieldLookup e' field) t')
checkTypes' c (Record (RecUpdate e table) _) = do
    e' <- checkTypes' c e
    let t = type_of e'
    t' <- bind (t^?fieldTypes)
        ([printf|Expression %s is not a record|] (pretty e))
    m <- traverseValidation (checkTypes' c) table
    return $ Record (RecUpdate e' m) (record_type $ M.union (type_of <$> m) t')
checkTypes' c (Record (RecLit table) _) = do
    m <- traverseValidation (checkTypes' c) table
    return $ Record (RecLit m) $ record_type $ type_of <$> m
checkTypes' c (Record (RecSet table) _) = do
    -- let isSet e = maybe (Left undefined') (Right . (,e)) . preview _ElementType . type_of $ e
        -- msg = [printf|Expression %s has type %s but should have a set type|]
    -- m <- traverseValidation (isSet <=< zcast (set_type gA) . Right <=< checkTypes' c) table
    m <- traverseValidation (checkTypes' c) table
    -- let m' = snd <$> m
    --     t' = fst <$> m
    -- return $ Record (RecSet m') $ record_type t'
    zrecord_set $ Right <$> m
checkTypes' c (Cast ct e t) = do
    e' <- zcast t $ checkTypes' c e
    return (Cast ct e' t)
checkTypes' c (Lift e _) = do
    let phonyFun t = Fun [] [smt|lift|] Lifted [t] int FiniteWD
        setT = set_type gA
        arrayT = array gA gB
        mkLift _ e t = Lift (head e) (head t)
    check_type' mkLift (phonyFun setT) [checkTypes' c e] `tryBoth`
        check_type' mkLift (phonyFun arrayT) [checkTypes' c e] 
checkTypes' c' (Binder q vs' r t _) = do
    let c  = newContext vs' c'
        ns = map (view name) vs' :: [Name]
        vs = M.ascElems $ newDummies vs' c'
    (r'',t'') <- parCheck 
        (zcast bool $ checkTypes' c r) 
        (zcast (termType q) $ checkTypes' c t)
    let vars = used_var r'' `S.union` used_var t''
        v_type = id -- L.filter ((1 <) . S.size . snd) 
                    $ zip vs
                    $ map f ns 
        f x = S.filter (\y -> x == view name y) vars
    ts <- forM v_type $ \((Var x t),xs) -> do
        let ys = map var_type $ S.toList xs
        t' <- maybe 
            (fail $ [printf|Inconsistent type for %s: %s|] 
                    (pretty x)
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
-- checkTypes' c (Const xs n ()) = do
--  _