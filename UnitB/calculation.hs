module UnitB.Calculation where

import Z3.Z3 -- hiding ( context )

import UnitB.Operator

    -- Libraries
import Control.Monad

import Data.List (intercalate)

embed :: Either a b -> (b -> IO c) -> IO (Either a c)
embed em f = do
        case em of
            Right x -> do
                y <- f x
                return (Right y)
            Left x  -> 
                return (Left x)

data Calculation = Calc 
    {  context    :: Context
    ,  goal       :: Expr
    ,  first_step :: Expr
    ,  following  :: [(Operator, Expr, [Expr], (Int,Int))]
    ,  l_info     :: (Int,Int) 
    }

infer_goal (Calc _ _ s0 xs (i,j)) = 
        case reverse $ map f xs of
            x:xs -> either 
                        (\x -> Left (x)) --,i,j)) 
                        Right 
                        (s0 `op` x)
            []   -> Left ("a calculation must include at least one reasoning step") --,i,j)
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
