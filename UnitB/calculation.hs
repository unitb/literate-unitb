module UnitB.Calculation where

import Control.Monad

import Z3.Z3 -- hiding ( context )

import UnitB.Operator

steps_po :: Calculation -> Either String [ProofObligation]
steps_po (Calc d _ e0 [] _) = return []
steps_po (Calc d g e0 ((r0, e1, a0,_):es) li) = do
    expr <- mk_expr r0 e0 e1
    tail <- steps_po (Calc d g e1 es li)
    return $ ProofObligation d a0 False expr : tail

entails_goal_po (Calc d g e0 es _) = do
            a <- assume
            return $ ProofObligation d a False g
    where
        assume = 
                fmap reverse $ foldM f [] (map (\(x,y,z) -> (mk_expr x y z)) $ zip3 rs xs ys)
        f xs mx = do 
            x <- mx
            return (x:xs)
        ys = map (\(_,x,_,_) -> x) es
        xs = take (length es) (e0:ys)
        rs = map (\(x,_,_,_) -> x) es

obligations :: Calculation -> Either String [ProofObligation]
obligations c = do
        x <- entails_goal_po c
        ys <- steps_po c
        return (x:ys)

goal_po c = ProofObligation (context c) xs False (goal c)
    where
        xs = concatMap (\(_,_,x,_) -> x) $ following c

check :: Calculation -> IO (Either String [(Validity, Int)])
check c = f (\pos -> do
        rs <- forM pos discharge :: IO [Validity]
        let ln = filter (\(x,y) -> x /= Valid) $ zip rs [0..] :: [(Validity, Int)]
        return ln)
    where
        f :: ([ProofObligation] -> IO [(Validity, Int)]) -> IO (Either String [(Validity, Int)])
        f g = case mpo of
            Right po -> do
                xs <- g po
                return (Right xs)
            Left x -> return (Left x)
        mpo = obligations c

data Calculation = Calc {
    context :: Context,
    goal :: Expr,
    first_step :: Expr,
--    following :: [(Expr -> Expr -> Expr, Expr, [Expr])] }
    following :: [(Operator, Expr, [Expr], (Int,Int))],
    l_info :: (Int,Int) }

infer_goal (Calc _ _ s0 xs _) = s0 `op` last (ztrue:map f xs)
    where
        op = mk_expr $ foldl chain Equal $ map g xs
        f (x,y,z,_) = y
        g (x,y,z,_) = x

show_proof (Calc _ g fs ss _) = 
        unlines ( [
                show g,
                "----",
                "    " ++ show fs ]
            ++  concatMap f ss )
    where
        f (_, s, h, _) = (
                   (map ("      | " ++) $ map show h)
                ++ [ "    " ++ show s ] )
