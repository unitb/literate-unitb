module Logic.WellDefinedness where

    -- Modules
import Logic.Expr
import Logic.Classes
import Logic.Const

import Theories.FunctionTheory
import Theories.SetTheory

    -- Libraries
import Data.List

--well_definedness :: ExprP -> ExprP
--well_definedness x = do
--        x' <- x
--        well_definedness_aux x'

well_definedness :: Expr -> Expr
well_definedness (Word _) = ztrue
well_definedness (Const _ _ _) = ztrue
well_definedness (Binder q vs r t) = zforall vs ztrue t'
    where
        t' = case q of
                Forall -> well_definedness $ r `zimplies` t
                Exists -> well_definedness $ r `zand` t
                Lambda ->           well_definedness r
                            `zand` (r `zimplies` well_definedness t)
well_definedness (FunApp fun xs) 
        | name fun == "and"   = zsome $ map (f id) ys
        | name fun == "or"    = zsome $ map (f znot) ys
        | name fun == "=>"    = well_definedness 
                                  $ znot (xs !! 0) `zor` (xs !! 1)
        | name fun == "apply" = zall $ 
                                    (fromJust $ xs' !! 1 `zelem` zdom (xs' !! 0))
                                  : map well_definedness xs
        | otherwise           = zall $ map well_definedness xs
    where
        ys = permutations bs
        xs' = map Right xs
        f h xs = zall $ map (g h) $ tails xs
        g f (x:xs) = zall (map f $ xs++as) `zimplies` well_definedness x
        g _ [] = ztrue
        (as,bs) = partition ((ztrue ==) . well_definedness) xs
