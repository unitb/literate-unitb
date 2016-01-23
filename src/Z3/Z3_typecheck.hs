module Z3_TypeCheck where

import Z3_Def
import Z3

type_correct (Word (Var n t0)) t1 = t0 `match` t1
type_correct (Const _ t0) t1      = t0 `match` t1
type_correct (FunApp (Fun fn ts t0) xs) t1 = (
    t0 `match` t1
    && length ts == length xs
    && and (map (uncurry type_correct) $ zip xs ts))
type_correct (Binder _ _ xp) t   =
    t `match` BOOL
    && type_correct xp BOOL

decls (Word (Var n t)) = Just [ConstDecl n t]
decls (Const _ _)      = Just []
decls (FunApp (Fun fn ts t0) xs) = 
        fmap (FunDecl fn ts t0 :) $
            foldl f (Just []) $ map decls xs
    where
        f Nothing _ = Nothing
        f _ Nothing = Nothing
        f (Just xs) (Just ys) = Just (xs ++ ys)
decls (Binder _ vs xp) = do
        ys <- xs
        foldl f (Just []) $ map valid ys
    where
        xs = decls xp
        valid d@(ConstDecl n t) 
            | any (\(Var vn vt) -> vn == n && not (t `match` vt)) vs
                = Nothing
            | any (\(Var vn vt) -> vn == n && t `match` vt) vs
                = Just []
            | otherwise
                = Just [d]
        f Nothing _ = Nothing
        f _ Nothing = Nothing
        f (Just xs) (Just ys) = Just (xs ++ ys)
