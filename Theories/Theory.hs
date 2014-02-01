module Theories.Theory where

import Logic.Expr
import Logic.Label

    -- Libraries
import Data.Map hiding ( map )

data Theory = Theory {
        extends :: [Theory],
        gen_param :: Maybe Type, 
        types   :: Map String Sort,
        funs    :: Map String Fun,
        consts  :: Map String Var,
        fact    :: Map Label Expr,
        dummies :: Map String Var }
    deriving (Eq, Show)

--data GenericTheory = GenTh String (Set Type -> Theory)
--
--instance Show GenericTheory where
--    show (GenTh name _) = "{ generic theory: " ++ name ++ "}"