module UnitB.AST (
    Label, Theory (..), Event(..), empty_event, 
    Machine (..), label,
    empty_machine, ProgProp(..), ProgressProp,
    SafetyProp, PropertySet, empty_property_set,
    composite_label,
    machine, proofs, prog_prop, inv, inv_thm
    ) 
where

import Data.List 
import Data.Map as M hiding (map)

import Z3.Z3
import Z3.Calculation
import Z3.Def
import Z3.Const

data Label = Lbl String
    deriving (Ord, Eq)

instance Show Label where
    show (Lbl s) = s

label s = Lbl s

data Theory = Theory {
    extends :: [Theory],
    funs    :: Map String Fun,
    consts  :: Map String Var,
    fact    :: Map Label Expr }

data Event = Event {
    indices   :: [Var],
    c_sched   :: Map Label Expr,
    f_sched   :: Maybe Expr,
    params    :: [Var],
    guard     :: Map Label Expr,
    action    :: Map Label Expr }

empty_event = Event [] (singleton (Lbl "SCH") zfalse)  Nothing [] empty empty

data Machine = 
    Mch {
        _name      :: Label,
        theories   :: [Theory],
        variables  :: Map String Var,
        inits      :: [Expr],
        events     :: Map Label Event,
        progress   :: Map Label ProgressProp,
        safety     :: Map Label SafetyProp }

class RefRule a where
    apply         :: a -> Machine -> Machine
    ref_condition :: a -> Machine -> Map Label ProofObligation

empty_machine :: String -> Machine
empty_machine n = Mch (Lbl n) [] empty [] empty empty empty

instance Named Machine where
    name m = case _name m of Lbl s -> s

data ProgProp = 
    Co [Var] Expr
    | Transient [Var] Expr Label
--    | Grd thm
--    | Sch thm

data ProgressProp = LeadsTo [Var] Expr Expr

data SafetyProp = Unless [Var] Expr Expr

data PropertySet = PS {
    machine   :: Machine,                 
    prog_prop :: Map Label ProgProp,
    inv       :: Map Label Expr,       -- inv
    inv_thm   :: Map Label Expr,       -- inv thm
    proofs    :: Map Label Calculation }

empty_property_set :: String -> PropertySet
empty_property_set xs = PS (empty_machine xs) empty empty empty empty

composite_label xs = Lbl $ intercalate "/" $ map str xs
    where
        str (Lbl s) = s