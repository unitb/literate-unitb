{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE DeriveDataTypeable #-}
module UnitB.Event where

    -- Modules
import Logic.Expr

import Theories.SetTheory

import UnitB.Property

    -- Libraries
import Control.DeepSeq

import Data.Default
import Data.DeriveTH
import Data.List as L
import Data.Map  as M
import Data.Typeable
import Data.Set as S

import Utilities.Format
import Utilities.TH

data Schedule = Schedule
        { coarse :: Map Label Expr
        , fine   :: Maybe (Label, Expr)
        }
    deriving (Eq, Show)

empty_schedule :: Schedule
empty_schedule = Schedule default_schedule Nothing

instance Default Schedule where
    def = empty_schedule

data Action = 
        Assign Var Expr 
        | BcmSuchThat [Var] Expr
        | BcmIn Var Expr
    deriving (Eq,Ord)

instance Show Action where
    show (Assign v e) = format "{0} := {1}" (name v) (show e)
    show (BcmIn v e) = format "{0} :∈ {1}" (name v) (show e)
    show (BcmSuchThat vs e) = format "{0} :| {1}" 
            (intercalate "," $ L.map name vs)
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

default_schedule :: Map Label Expr
default_schedule = M.fromList [(label "default", zfalse)]

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

mkCons ''Event

empty_event :: Event
empty_event = makeEvent { scheds = default_schedule }

frame' :: Action -> Map String Var
frame' (Assign v _) = M.singleton (name v) v
frame' (BcmIn v _)  = M.singleton (name v) v
frame' (BcmSuchThat vs _) = M.fromList $ zip (L.map name vs) vs

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
skip' keep = M.mapKeys f $ M.map g keep
    where
        f n = label ("SKIP:" ++ n)
        g v = Word (prime v) `zeq` Word v

ba_predicate' :: Map String Var -> Map Label Action -> Map Label Expr
ba_predicate' vars acts =           M.map ba_pred acts
                          `M.union` skip
    where
        skip = skip' $ keep' vars acts

newtype EventId = EventId Label
    deriving (Eq,Ord,Typeable)

instance Show EventId where
    show (EventId x) = show x

primed :: Map String Var -> Expr -> Expr
primed vs e = make_unique "@prime" vs e

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
        r_set = L.foldl S.union S.empty $ L.map remove ref
        a_set = L.foldl S.union S.empty $ L.map add ref

new_guard :: Event -> Map Label Expr
new_guard e = L.foldl f old ref
    where
        ref = L.map rule $ sched_ref e
        grd = guards e
        old = old_guard e
        f m (AddGuard lbl)    = M.insert lbl (grd ! lbl) m
        f m (RemoveGuard lbl) = M.delete lbl m
        f m _ = m

derive makeNFData ''Event
derive makeNFData ''Action
derive makeNFData ''EventId
derive makeNFData ''Schedule
derive makeNFData ''ScheduleChange
derive makeNFData ''ScheduleRule
