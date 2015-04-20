{-# LANGUAGE DeriveDataTypeable, ExistentialQuantification #-} 
{-# LANGUAGE TemplateHaskell #-} 
module UnitB.AST 
    ( Theory  (..)
    , Machine (..)
    , variableSet
    , EventId (..)
    , Event   (..)
    , empty_event
    , Action (..)
    , ba_predicate
    , ba_predicate'
    , ba_pred
    , rel_action
    , empty_machine
    , empty_theory
    , TrHint (..)
    , empty_hint
    , Transient   (..)
    , Constraint  (..)
    , ProgressProp(..)
    , Schedule    (..)
    , SafetyProp  (..) 
    , PropertySet (..) 
    , inv_thm, inv, proofs
    , progress, safety
    , transient, constraint
    , empty_property_set
    , Rule (..)
    , Variant (..)
    , variant_decreased
    , variant_equals_dummy
    , variant_bounded
    , Direction (..)
    , RefRule (..)
    , ProgId (..)
    , primed, make_unique
    , all_types
    , basic_theory
    , disjoint_union
    , keep', frame, frame'
    , cycles
    , ScheduleChange 
        ( add, remove
        , keep, event
        , rule)
    , replace, weaken
    , ScheduleRule (..)
    , new_sched
    , new_guard
    , default_schedule
    , System (..)
    , empty_system
    , replace_fine
    , all_notation
    , remove_guard
    , add_guard
    , th_notation
    , DocItem (..)
    ) 
where
 
    -- Modules
import Logic.Expr hiding (merge)
import Logic.ExpressionStore
import Logic.Operator
import Logic.Theory as Th

import Theories.SetTheory
import Theories.FunctionTheory
import Theories.Arithmetic

import UnitB.Event
import UnitB.POGenerator ( POGen )
import UnitB.Property

    -- Libraries
import Control.DeepSeq
import Control.Lens.TH

import Control.Monad hiding ( guard )
import Control.Monad.Writer hiding ( guard )

import           Data.DeriveTH
import           Data.List as L hiding ( union, inits )
import           Data.Map as M hiding (map)
import qualified Data.Set as S
import           Data.Typeable

import Utilities.Format
import Utilities.HeterogenousEquality
import Utilities.Graph  (cycles)

all_types :: Theory -> Map String Sort
all_types th = unions (types th : map all_types (elems $ extends th)) 

newtype ProgId = PId { getProgId :: Label }
    deriving (Eq,Ord)

instance Show ProgId where
    show (PId x) = show x

data Machine = 
    Mch 
        { _name      :: Label
        , theory     :: Theory
        , variables  :: Map String Var
        , abs_vars   :: Map String Var
        , del_vars   :: Map String Var
        , init_witness :: Map Var Expr
        , del_inits  :: Map Label Expr
        , inits      :: Map Label Expr
        , events     :: Map Label Event
        , inh_props  :: PropertySet
        , props      :: PropertySet
        , derivation :: Map Label Rule         
        , comments   :: Map DocItem String }
    deriving (Eq, Show, Typeable)

variableSet :: Machine -> S.Set Var
variableSet m = S.fromList $ M.elems $ variables m

data DocItem = 
        DocVar String 
        | DocEvent Label 
        | DocInv Label
        | DocProg Label
    deriving (Eq,Ord)

instance Show DocItem where
    show (DocVar xs) = format "{0} (variable)" xs
    show (DocEvent xs) = format "{0} (event)" xs
    show (DocInv xs) = format "{0} (invariant)" xs
    show (DocProg xs) = format "{0} (progress)" xs


empty_machine :: String -> Machine
empty_machine n = Mch 
        { _name = (Lbl n) 
        , theory = empty_theory { extends = fromList [
                ("arithmetic",arithmetic), 
                ("basic", basic_theory)] }
        , variables = empty
        , abs_vars  = empty
        , del_vars  = empty
        , init_witness = empty
        , del_inits = empty
        , inits     = empty
        , events    = empty 
        , inh_props = empty_property_set 
        , props     = empty_property_set
        , derivation = empty
        , comments  = empty
        }  

-- data Decomposition = Decomposition 
    
class (Typeable a, Eq a, Show a, NFData a) => RefRule a where
    refinement_po :: a -> Machine -> POGen ()
    rule_name     :: a -> Label
    hyps_labels   :: a -> [ProgId]
    supporting_evts :: a -> [EventId]

data System = Sys 
        {  proof_struct :: [(Label,Label)]
        ,  ref_struct   :: Map Label Label
        ,  expr_store   :: ExprStore
        ,  machines     :: Map String Machine
        ,  theories     :: Map String Theory
        }
    deriving Eq

empty_system :: System
empty_system = Sys [] M.empty empty_store 
        M.empty $ M.fromList 
            [ ("sets",set_theory)
            , ("functions",function_theory)
            , ("arithmetic",arithmetic)
            , ("basic",basic_theory)]

all_notation :: Machine -> Notation
all_notation m = flip precede logic 
        $ L.foldl combine empty_notation 
        $ map Th.notation th
    where
        th = theory m : elems (extends $ theory m)

toEither :: (Eq a, Monoid a) => Writer a b -> Either a b
toEither m
        | w == mempty   = Right x
        | otherwise     = Left w
    where
        (x,w) = runWriter m


disjoint_union :: (Monoid c, Eq c, Ord a) => (a -> c) -> Map a b -> Map a b -> Either c (Map a b)
disjoint_union f x y = do
        toEither $ forM_ zs $ \z ->
            tell $ f z
        return (x `union` y)
    where
        zs = S.toList (keysSet x `S.intersection` keysSet y)

instance Named Machine where
    name m = case _name m of Lbl s -> s
    decorated_name' = return . name

data Rule = forall r. RefRule r => Rule r
    deriving Typeable

instance Show Rule where
    show (Rule x) = show x

instance Eq Rule where
    Rule x == Rule y = x `h_equal` y


instance RefRule Rule where
    refinement_po (Rule r) = refinement_po r
    rule_name (Rule r) = rule_name r
    hyps_labels (Rule r) = hyps_labels r
    supporting_evts (Rule r) = supporting_evts r

--data Liveness = Live (Map Label ProgressProp) 

--data Schedule = Schedule [Var] Expr Expr Label
--    deriving (Eq,Typeable)

ba_predicate :: Machine -> Event -> Map Label Expr
ba_predicate m evt =          ba_predicate' (variables m) (actions evt)
                    `M.union` M.mapKeys (label . name) (witness evt)

makeLenses ''PropertySet

derive makeNFData ''DocItem
derive makeNFData ''Machine
derive makeNFData ''Rule
derive makeNFData ''System
