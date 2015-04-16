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
import Logic.Proof
import Logic.Theory as Th

import Theories.SetTheory
import Theories.FunctionTheory
import Theories.Arithmetic

import UnitB.POGenerator ( POGen )

    -- Libraries
import Control.DeepSeq

import Control.Monad hiding ( guard )
import Control.Monad.Writer hiding ( guard )

import Control.Lens.TH
import           Data.Default
import           Data.DeriveTH
import           Data.List as L hiding ( union, inits )
import           Data.Map as M hiding (map)
import qualified Data.Map as M
import qualified Data.Set as S
import           Data.Typeable

import Utilities.Format
import Utilities.HeterogenousEquality
import Utilities.Graph  (cycles)

all_types :: Theory -> Map String Sort
all_types th = unions (types th : map all_types (elems $ extends th)) 

data Schedule = Schedule
        { coarse :: Map Label Expr
        , fine   :: Maybe (Label, Expr)
        }
    deriving (Eq, Show)


empty_schedule :: Schedule
empty_schedule = Schedule default_schedule Nothing

data Action = 
        Assign Var Expr 
        | BcmSuchThat [Var] Expr
        | BcmIn Var Expr
    deriving (Eq,Ord)

instance Show Action where
    show (Assign v e) = format "{0} := {1}" (name v) (show e)
    show (BcmIn v e) = format "{0} :∈ {1}" (name v) (show e)
    show (BcmSuchThat vs e) = format "{0} :| {1}" 
            (intercalate "," $ map name vs)
            (show e)


data Event = Event 
        { indices   :: Map String Var
        , sched_ref :: [ScheduleChange]
        , old_sched :: Schedule
        , scheds    :: Map Label Expr
        , params    :: Map String Var
        , witness   :: Map Var Expr
        , old_guard :: Map Label Expr
        , guards    :: Map Label Expr
        , old_acts :: Map Label ()
        , del_acts :: Map Label Action
        , actions  :: Map Label Action
        , eql_vars :: Map String Var
        } deriving (Eq, Show)


empty_event :: Event
empty_event = Event 
        { indices = empty 
        , sched_ref = []
        , old_sched = empty_schedule
        , scheds = default_schedule
        , params = empty
        , witness = empty
        , old_guard = empty
        , guards = empty 
        , actions = empty
        , old_acts = empty
        , del_acts = empty
        , eql_vars = empty
        }

frame' :: Action -> Map String Var
frame' (Assign v _) = M.singleton (name v) v
frame' (BcmIn v _)  = M.singleton (name v) v
frame' (BcmSuchThat vs _) = M.fromList $ zip (map name vs) vs

frame :: Map Label Action -> Map String Var
frame acts = M.unions $ L.map frame' $ M.elems acts

ba_pred :: Action -> Expr
ba_pred (Assign v e) = $fromJust $ Right (Word (prime v)) `mzeq` Right e
ba_pred (BcmIn v e) = $fromJust $ Right (Word (prime v)) `zelem` Right e
ba_pred (BcmSuchThat _ e) = e

rel_action :: [Var] -> Map Label Expr -> Map Label Action
rel_action vs act = M.map (\x -> BcmSuchThat vars x) act
    where
        vars = vs

keep' :: Map String Var -> Map Label Action -> Map String Var
keep' vars acts = vars `M.difference` frame acts

skip' :: Map String Var -> Map Label Expr
skip' keep = M.fromList $ map f $ M.toList keep
    where
        f (n,v) = (label ("SKIP:" ++ n), Word (prime v) `zeq` Word v)

ba_predicate' :: Map String Var -> Map Label Action -> Map Label Expr
ba_predicate' vars acts =           M.map ba_pred acts
                          `M.union` skip
    where
        skip = skip' $ keep' vars acts

ba_predicate :: Machine -> Event -> Map Label Expr
ba_predicate m evt =          ba_predicate' (variables m) (actions evt)
                    `M.union` M.mapKeys (label . name) (witness evt)

newtype EventId = EventId Label
    deriving (Eq,Ord)

instance Show EventId where
    show (EventId x) = show x

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

default_schedule :: Map Label Expr
default_schedule = fromList [(label "default", zfalse)]

primed :: Map String Var -> Expr -> Expr
primed vs e = make_unique "@prime" vs e


make_unique :: String           -- suffix to be added to the name of variables
            -> Map String Var   -- set of variables that must renamed
            -> Expr             -- expression to rewrite
            -> Expr
make_unique suf vs w@(Word (Var vn vt)) 
        | vn `M.member` vs    = Word (Var (vn ++ suf) vt)
        | otherwise           = w
make_unique _ _ c@(Const _ _)    = c
make_unique suf vs (FunApp f xs)     = FunApp f $ map (make_unique suf vs) xs
make_unique suf vs (Cast e t)        = Cast (make_unique suf vs e) t
make_unique suf vs (Lift e t)        = Lift (make_unique suf vs e) t
make_unique suf vs (Binder q d r xp t) = Binder q d (f r) (f xp) t
    where
        local = (L.foldr M.delete vs (map name d))
        f = make_unique suf local

instance Named Machine where
    name m = case _name m of Lbl s -> s
    decorated_name' = return . name




data Constraint = 
        Co [Var] Expr
    deriving (Eq,Ord,Show)


data TrHint = TrHint (Map String (Type,Expr)) (Maybe Label)
    deriving (Eq,Ord,Show)


empty_hint :: TrHint
empty_hint = TrHint empty Nothing

data Transient = 
        Transient 
            (Map String Var)     -- Free variables
            Expr                 -- Predicate
            [Label]              -- Event, Schedule 
            TrHint               -- Hints for instantiation
            -- (Map String Expr)    -- Index substitution
            -- (Maybe Label)        -- Progress Property for fine schedule
    deriving (Eq,Ord,Show)


data Direction = Up | Down
    deriving (Eq,Show)


data Variant = 
        SetVariant     Var Expr Expr Direction
      | IntegerVariant Var Expr Expr Direction
    deriving (Eq,Show)


variant_equals_dummy :: Variant -> Expr
--variant_equals_dummy (SetVariant d var _ _)     = Word d `zeq` var
variant_equals_dummy (IntegerVariant d var _ _) = Word d `zeq` var
variant_equals_dummy (SetVariant d var _ _) = Word d `zeq` var

variant_decreased :: Variant -> Expr
variant_decreased (SetVariant d var _ Up)       = ($fromJust) $ Right (Word d) `zsubset` Right var
variant_decreased (IntegerVariant d var _ Up)   = Word d `zless` var
variant_decreased (SetVariant d var _ Down)     = ($fromJust) $ Right var `zsubset` Right (Word d)
variant_decreased (IntegerVariant d var _ Down) = var `zless` Word d

variant_bounded :: Variant -> Expr
--variant_bounded (SetVariant d var _ _)     = error "set variants unavailable"
variant_bounded (IntegerVariant _ var b Down) = b `zle` var
variant_bounded (IntegerVariant _ var b Up)   = var `zle` b
variant_bounded (SetVariant _ var b Down) = ($fromJust) $ 
    mzand (Right b `zsubset` Right var)
          (mzfinite $ Right var `zsetdiff` Right b)
variant_bounded (SetVariant _ var b Up)   = ($fromJust) $ 
    mzand (Right var `zsubset` Right b)
          (mzfinite $ Right b `zsetdiff` Right var)

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

data ProgressProp = LeadsTo [Var] Expr Expr
    deriving (Eq,Ord,Typeable)

data SafetyProp = Unless [Var] Expr Expr (Maybe Label)
    deriving (Eq,Ord,Typeable)

instance Show ProgressProp where
    show (LeadsTo _ p q) = show p ++ "  |->  " ++ show q

instance Show SafetyProp where
    show (Unless _ p q ev) = show p ++ "  UNLESS  " ++ show q ++ except
        where
            except = maybe "" (("  EXCEPT  " ++) . show) ev



data PropertySet = PS
        { _transient    :: Map Label Transient
        , _constraint   :: Map Label Constraint
        , _inv          :: Map Label Expr       -- inv
        , _inv_thm      :: Map Label Expr       -- inv thm
        , _proofs       :: Map Label Proof
        , _progress     :: Map Label ProgressProp
--        , schedule     :: Map Label Schedule
        , _safety       :: Map Label SafetyProp
        }
    deriving Eq

instance Show PropertySet where
    show x = intercalate ", " $ map (\(x,y) -> x ++ " = " ++ y)
        [ ("transient",  show $ _transient x)
        , ("constraint", show $ _constraint x)
        , ("inv", show $ _inv x)
        , ("inv_thm", show $ _inv_thm x)
        , ("proofs", show $ keys $ _proofs x)
        , ("progress", show $ _progress x)
        , ("safety", show $ _safety x)
        ]

instance Default PropertySet where
    def = empty_property_set

data ScheduleChange = ScheduleChange 
        { event  :: Label
        , remove :: S.Set Label
        , add    :: S.Set Label
        , keep   :: S.Set Label
        , rule   :: ScheduleRule
        }
    deriving (Show,Eq,Typeable)


data ScheduleRule = 
        Replace (Label,ProgressProp) (Label,SafetyProp)
        | Weaken
        | ReplaceFineSch Expr (Maybe Label) Expr (Maybe (Label,ProgressProp))
        | RemoveGuard Label
        | AddGuard    Label
            -- old expr, new label, new expr, proof
    deriving (Show,Eq)


weaken :: Label -> ScheduleChange
weaken lbl = ScheduleChange lbl S.empty S.empty S.empty Weaken

replace :: Label -> (Label, ProgressProp) -> (Label, SafetyProp) -> ScheduleChange
replace lbl prog saf = ScheduleChange lbl 
        S.empty S.empty S.empty 
        (Replace prog saf)

replace_fine :: Label
             -> Expr
             -> Maybe Label
             -> Expr
             -> Maybe (Label, ProgressProp)
             -> ScheduleChange
replace_fine lbl old tag new prog = 
    ScheduleChange lbl S.empty S.empty S.empty 
        (ReplaceFineSch old tag new prog)

add_guard :: Label -> Label -> ScheduleChange
add_guard evt lbl = ScheduleChange evt S.empty S.empty S.empty (AddGuard lbl)

remove_guard :: Label -> Label -> ScheduleChange
remove_guard evt lbl = ScheduleChange evt S.empty S.empty S.empty (RemoveGuard lbl)

new_fine_sched :: Maybe (Label, Expr) -> ScheduleChange -> Maybe (Label, Expr)
new_fine_sched _ (ScheduleChange { rule = ReplaceFineSch _ (Just n_lbl) n_expr _ }) = Just (n_lbl,n_expr)
new_fine_sched _ (ScheduleChange { rule = ReplaceFineSch _ Nothing _ _ }) = Nothing
new_fine_sched x _ = x

new_sched :: Event -> Schedule
new_sched e = Schedule new_c_sched new_f_sched
    where
        new_c_sched = M.filterWithKey f_out c_sch `M.union` M.filterWithKey f_in sched
        f_out k _ = not $ k `S.member` r_set
        f_in  k _ = k `S.member` a_set
        new_f_sched = L.foldl new_fine_sched f_sch ref
        Schedule c_sch f_sch = old_sched e 
        ref   = sched_ref e
        sched = scheds e 
        r_set = L.foldl S.union S.empty $ map remove ref
        a_set = L.foldl S.union S.empty $ map add ref

new_guard :: Event -> Map Label Expr
new_guard e = L.foldl f old ref
    where
        ref = map rule $ sched_ref e
        grd = guards e
        old = old_guard e
        f m (AddGuard lbl)    = M.insert lbl (grd ! lbl) m
        f m (RemoveGuard lbl) = M.delete lbl m
        f m _ = m

empty_property_set :: PropertySet
empty_property_set = PS 
        empty empty empty 
        empty empty empty 
        empty

makeLenses ''PropertySet

derive makeNFData ''Event
derive makeNFData ''DocItem
derive makeNFData ''Machine
derive makeNFData ''System
derive makeNFData ''EventId
derive makeNFData ''TrHint
derive makeNFData ''Constraint
derive makeNFData ''ScheduleChange
derive makeNFData ''ScheduleRule
derive makeNFData ''PropertySet
derive makeNFData ''ProgressProp
derive makeNFData ''SafetyProp
derive makeNFData ''Schedule
derive makeNFData ''Action
derive makeNFData ''Rule
derive makeNFData ''Transient
derive makeNFData ''Variant
derive makeNFData ''Direction
