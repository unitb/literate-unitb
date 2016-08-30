module Logic.WellDefinedness where

    -- Modules
import Logic.Expr

import Logic.Theories.FunctionTheory
import Logic.Theories.SetTheory

    -- Libraries
import Control.Lens
import Control.Precondition

import Data.List

is_true_or_false :: Expr -> Expr
is_true_or_false e = is_true e `zor` is_false e

is_true :: Expr -> Expr
is_true e@(Word _) = e
is_true e@(Lit _ _) = e
is_true (Binder Forall vs r t tt) = Binder Forall vs ztrue (is_true $ r `zimplies` t) tt
is_true (Binder Exists vs r t tt) = Binder Exists vs ztrue (is_true $ r `zand` t) tt
is_true (Binder (UDQuant _ _ _ _) _ _ _ _) = undefined'
is_true (Cast e _) = is_true e
is_true (Lift e _) = is_true e
is_true e@(FunApp fun xs) 
        | view name fun == [smt|not|]   = is_false x0
        | view name fun == [smt|and|]   = zall $ map is_true xs
        | view name fun == [smt|or|]    = zsome $ map is_true xs
        | view name fun == [smt|=>|]    = is_true 
                                       $ znot x0 `zor` x1
        | otherwise                = e `zand` delta e
    where
        x0  = xs ! 0
        x1  = xs ! 1
is_true e@(Record _) = e `zand` delta e

is_false :: Expr -> Expr
is_false e@(Word _) = znot e
is_false e@(Lit _ _) = znot e
is_false (Binder Forall vs r t tt) = Binder Exists vs ztrue (is_false $ r `zimplies` t) tt
is_false (Binder Exists vs r t tt) = Binder Forall vs ztrue (is_false $ r `zand` t) tt
is_false (Binder (UDQuant _ _ _ _) _ _ _ _) = undefined'
is_false (Cast e _) = is_false e
is_false (Lift e _) = is_false e
is_false e@(FunApp fun xs) 
        | view name fun == [smt|not|]   = is_true x0
        | view name fun == [smt|and|]   = zsome $ map is_false xs
        | view name fun == [smt|or|]    = zall $ map is_false xs
        | view name fun == [smt|=>|]    = is_false 
                                       $ znot x0 `zor` x1
        | otherwise                = znot e `zand` delta e
    where
        x0  = xs ! 0
        x1  = xs ! 1
is_false e@(Record _) = znot e `zand` delta e

delta :: Expr -> Expr
delta = well_definedness

well_definedness :: Expr -> Expr
well_definedness (Word _) = ztrue
well_definedness (Lit _ _) = ztrue
well_definedness (Binder q vs r t _) = case q of
                Forall -> (zforall vs ztrue t') `zor` (zexists vs ztrue $ t' `zand` neg)
                    where
                        t' = well_definedness (r `zimplies` t) 
                        neg = r `zand` znot t
                Exists -> (zforall vs ztrue t') `zor` (zexists vs ztrue $ t' `zand` pos)
                    where
                        t' = well_definedness (r `zand` t)
                        pos = r `zand` t
                UDQuant _ _ _ _ -> (zforall vs ztrue t') `zand` fin
                    where
                        t' = well_definedness r
                                `zand` (r `zimplies` well_definedness t)
                        fin = case finiteness q of
                                FiniteWD -> ($typeCheck) $ mzfinite $ zcomprehension vs (Right r) (Right $ ztuple $ map Word vs)
                                InfiniteWD -> ztrue
well_definedness (Cast e _) = well_definedness e
well_definedness (Lift e _) = well_definedness e
well_definedness (FunApp fun xs) 
        | view name fun == [smt|and|]   = linearRecurse zall zsome id
        | view name fun == [smt|or|]    = linearRecurse zsome zall znot
        | view name fun == [smt|=>|]    = well_definedness 
                                       $ znot x0 `zor` x1
        | view name fun == [smt|apply|] = zall $ 
                                        (($typeCheck) $ x1' `zelem` zdom x0')
                                      : map well_definedness xs
        | view name fun == [smt|ite|]   = zall [ well_definedness x0
                                               , x0 `zimplies` well_definedness x1
                                               , znot x0 `zimplies` well_definedness x2 ]
        | otherwise                = zall $ wdFun : map well_definedness xs
    where
        wdFun = case fun^.finite of
            InfiniteWD -> ztrue
            FiniteWD -> zall $ map zfinite xs
        withAsms sign x = zall (map sign as) `zimplies` x
        linearRecurse foldTrue foldFalse sign = case bs of
                            [] -> ztrue
                            [x] -> withAsms sign $ well_definedness x
                            xs -> withAsms sign $ foldTrue (map is_true xs) `zor` foldFalse (map is_false xs)
        x0  = xs ! 0
        x0' = Right x0
        x1  = xs ! 1
        x1' = Right x1
        x2  = xs ! 2
        (as,bs) = partition ((ztrue ==) . well_definedness) xs
well_definedness (Record e) = zall $ e^.partsOf (traverseRecExpr.to well_definedness)
