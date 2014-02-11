{-# LANGUAGE ExistentialQuantification, DeriveDataTypeable #-}
module Logic.Calculation where

    -- Modules
import Logic.Expr
import Logic.Operator
import Logic.Label

import Theories.Theory

    -- Libraries
import Control.Monad

import Data.Map as M (Map, lookup, fromList)
import Data.Typeable

import Utilities.Format
import Utilities.Syntactic
import Utilities.HeterogenousEquality

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
    deriving (Eq, Typeable)

data Proof = forall a. ProofRule a => Proof a
    deriving Typeable

instance Eq Proof where
    Proof x == Proof y = x `h_equal` y

data Ignore = Ignore LineInfo
    deriving (Eq,Typeable)

data Prune = Prune Int Proof
    deriving (Eq,Typeable)

data FreeGoal   = FreeGoal String String Type Proof LineInfo
    deriving (Eq,Typeable)

data ByCases    = ByCases   [(Label, Expr, Proof)] LineInfo
    deriving (Eq,Typeable)

data Easy       = Easy                             LineInfo
    deriving (Eq,Typeable)
data Assume     = Assume (Map Label Expr) Expr Proof LineInfo
    deriving (Eq,Typeable)
data ByParts    = ByParts [(Expr,Proof)]           LineInfo
    deriving (Eq,Typeable)
data Assertion  = Assertion (Map Label (Expr,Proof)) Proof LineInfo
    deriving (Eq,Typeable)

class (Syntactic a, Typeable a, Eq a) => ProofRule a where
    proof_po :: Theory -> a -> Label -> Sequent -> Either [Error] [(Label,Sequent)]

instance ProofRule Proof where
    proof_po y (Proof x) z a = proof_po y x z a

instance Syntactic Calculation where
    line_info c = l_info c

instance Syntactic Proof where
    line_info (Proof x) = line_info x

instance Syntactic ByCases where
    line_info (ByCases _ li)        = li

instance Syntactic Assume where
    line_info (Assume _ _ _ li)     = li

instance Syntactic ByParts where
    line_info (ByParts _ li)        = li

instance Syntactic Assertion where
    line_info (Assertion _ _ li)    = li

instance Syntactic Easy where
    line_info (Easy li)             = li

instance Syntactic FreeGoal where
    line_info (FreeGoal _ _ _ _ li)   = li

instance Syntactic Prune where
    line_info (Prune _ p) = line_info p

instance Syntactic Ignore where
    line_info (Ignore li) = li

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
