{-# LANGUAGE DeriveDataTypeable #-} 

module UnitB.AST 
    ( Label, Theory (..), Event(..), empty_event
    , Machine (..), label
    , empty_machine
    , Transient  (..)
    , Constraint (..)
    , ProgressProp(..)
    , SafetyProp  (..) 
    , PropertySet (..) 
    , empty_property_set
    , composite_label, empty_theory
    , Rule (..)
    , Variant (..)
    , Direction (..)
--    , ps_union
    ) 
where

import Data.List hiding ( union )
import Data.Map as M hiding (map)
import Data.Typeable

import UnitB.FunctionTheory
import UnitB.SetTheory
import UnitB.Theory
import UnitB.Calculation

import Z3.Z3

empty_theory :: Theory
empty_theory = Theory [] --[set_theory train_type] 
    (symbol_table [set_sort,fun_sort,BoolSort,IntSort,RealSort]) empty empty empty empty

data Event = Event {
        indices   :: Map String Var,
        c_sched   :: Maybe (Map Label Expr),
        f_sched   :: Maybe Expr,
        params    :: Map String Var,
        guard     :: Map Label Expr,
        action    :: Map Label Expr }
    deriving Show

empty_event = Event empty Nothing  Nothing empty empty empty

data Machine = 
    Mch {
        _name      :: Label,
        theory     :: Theory,
        variables  :: Map String Var,
        inits      :: Map Label Expr,
        events     :: Map Label Event,
        props      :: PropertySet }
    deriving (Show, Typeable)

class RefRule a where
    apply         :: a -> Machine -> Machine
    ref_condition :: a -> Machine -> Map Label ProofObligation

empty_machine :: String -> Machine
empty_machine n = Mch (Lbl n) empty_theory empty empty empty empty_property_set

instance Named Machine where
    name m = case _name m of Lbl s -> s

data Constraint = 
        Co [Var] Expr
    deriving Show

data Transient = 
        Transient (Map String Var) Expr Label
--      | Grd thm
--      | Sch thm
    deriving Show

--data Derivation = Deriv 
--        Label Rule 
--        [LivenessDerivation] 
--        [Label] 

data Direction = Up | Down
    deriving Show

data Variant = 
        SetVariant Expr Expr Direction
        | IntegerVariant Expr Expr Direction
    deriving Show

data Rule = 
        Monotonicity ProgressProp ProgressProp
        | Transitivity ProgressProp ProgressProp ProgressProp
        | Induction ProgressProp ProgressProp Variant
        | PSP ProgressProp ProgressProp SafetyProp
        | Disjunction Label
        | NegateDisjunct ProgressProp ProgressProp
        | Discharge ProgressProp Transient (Maybe SafetyProp)
        | Add
    deriving Show

--data Liveness = Live (Map Label ProgressProp) 

data ProgressProp = LeadsTo [Var] Expr Expr
    deriving (Typeable)

data SafetyProp = Unless [Var] Expr Expr
    deriving Typeable

instance Show ProgressProp where
    show (LeadsTo _ p q) = show p ++ "  |->  " ++ show q

instance Show SafetyProp where
    show (Unless _ p q) = show p ++ "  UNLESS  " ++ show q

data PropertySet = PS
        { transient    :: Map Label Transient
        , constraint   :: Map Label Constraint
        , inv          :: Map Label Expr       -- inv
        , inv_thm      :: Map Label Expr       -- inv thm
        , proofs       :: Map Label Proof
        , progress     :: Map Label ProgressProp
        , safety       :: Map Label SafetyProp
        , derivation   :: Map Label Rule
        }

instance Show PropertySet where
    show x = intercalate ", " $ map (\(x,y) -> x ++ " = " ++ y) [
        ("transient",  show $ transient x),
        ("constraint", show $ constraint x),
        ("inv", show $ inv x),
        ("inv_thm", show $ inv_thm x),
        ("proofs", show $ keys $ proofs x),
        ("progress", show $ progress x),
        ("safety", show $ safety x)]

empty_property_set :: PropertySet
empty_property_set = PS empty empty empty empty empty empty empty empty

--ps_union (PS a0 b0 c0 d0 e0 f0) (PS a1 b1 c1 d1 e1 f1) =
--    PS (a0 `union` a1) (b0 `union` b1) 
--        (c0 `union` c1) (d0 `union` d1)
--        (e0 `union` e1) (f0 `union` f1)
        

composite_label xs = Lbl $ intercalate "/" $ map str xs
    where
        str (Lbl s) = s