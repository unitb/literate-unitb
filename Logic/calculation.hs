module Logic.Calculation where

    -- Modules
import Logic.Expr
import Logic.Operator
import Logic.Label

    -- Libraries
import Control.Monad

import Data.Map as M (Map, lookup, fromList)

import Utilities.Format
import Utilities.Syntactic

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
        ,  following  :: [(BinOperator, Expr, [Expr], LineInfo)]
        ,  l_info     :: LineInfo }
    deriving Eq

data Proof = 
        ByCalc Calculation
        | FreeGoal String String Proof     LineInfo
        | ByCases   [(Label, Expr, Proof)] LineInfo
        | Easy                             LineInfo
        | Assume (Map Label Expr) Expr Proof LineInfo
        | ByParts [(Expr,Proof)]           LineInfo
        | Assertion (Map Label (Expr,Proof)) Proof LineInfo
    deriving Eq

instance Syntactic Proof where
    line_info (ByCalc c)            = l_info c
    line_info (ByCases _ li)        = li
    line_info (Assume _ _ _ li)     = li
    line_info (ByParts _ li)        = li
    line_info (Assertion _ _ li)    = li
    line_info (Easy li)             = li
    line_info (FreeGoal _ _ _ li)   = li

chain :: Notation -> BinOperator -> BinOperator -> Either String BinOperator
chain n x y 
    | x == equal = Right y
    | y == equal = Right x
    | otherwise  = case M.lookup (x,y) $ fromList (chaining n) of
                    Just z -> Right z
                    Nothing -> Left $ format "chain: operators {0} and {1} don't chain" x y


infer_goal :: Calculation -> Notation -> Either String Expr
infer_goal (Calc _ _ s0 xs _) n = do
        op <- mk_expr `fmap` foldM (chain n) equal (map g xs)
        case reverse $ map f xs of
            x:_ -> either 
                        (\x -> Left (x)) --,i,j)) 
                        Right 
                        (s0 `op` x)
            []   -> Left ("a calculation must include at least one reasoning step") --,i,j)
    where
--        op = mk_expr $ foldl chain equal $ map g xs
        f (_,y,_,_) = y
        g (x,_,_,_) = x

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
