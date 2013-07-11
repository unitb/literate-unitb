module Z3.Calculation where

import Control.Monad

import Z3.Z3 hiding ( context )
import Z3.Const
import Z3.Def

steps_po (Calc d _ e0 []) = []
steps_po (Calc d g e0 ((r0, e1, a0):es)) = 
    ProofObligation d a0 False (mk_expr r0 e0 e1) : steps_po (Calc d g e1 es)

entails_goal_po (Calc d g e0 es) = ProofObligation d assume False g
    where
        assume = map (\(x,y,z) -> (mk_expr x y z)) $ zip3 rs xs ys
        ys = map (\(_,x,_) -> x) es
        xs = take (length es) (e0:ys)
        rs = map (\(x,_,_) -> x) es

obligations c = entails_goal_po c : steps_po c

goal_po c = ProofObligation (context c) xs False (goal c)
    where
        xs = concatMap (\(_,_,x) -> x) $ following c

check :: Calculation -> IO [(Validity, Int)]
check c = do
    let po = obligations c
    rs <- forM po discharge
    let ln = filter (\(x,y) -> x /= Valid) $ zip rs [0..]
    return ln

data Calculation = Calc {
    context :: Context,
    goal :: Expr,
    first_step :: Expr,
--    following :: [(Expr -> Expr -> Expr, Expr, [Expr])] }
    following :: [(Operator, Expr, [Expr])] }

infer_goal (Calc _ _ s0 xs) = s0 `op` f (last xs)
    where
        op = mk_expr $ foldl chain Equal $ map g xs
        f (x,y,z) = y
        g (x,y,z) = x

show_proof (Calc _ g fs ss) = 
        unlines ( [
                show g,
                "----",
                "    " ++ show fs ]
            ++  concatMap f ss )
    where
        f (_, s, h) = (
                   (map ("      | " ++) $ map show h)
                ++ [ "    " ++ show s ] )