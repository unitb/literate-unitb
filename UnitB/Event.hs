{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric      #-}
module UnitB.Event
    ( EventId (..)
    , Event   (..)
    , empty_event
    , all_guards
    , Action (..)
    , ba_predicate'
    , ba_pred
    , rel_action, primed
    , keep', frame, frame'
    , deleted_sched
    , added_sched
    , kept_sched
    , deleted_guard
    , Schedule    (..)
    , ScheduleChange (..)
    , replace
    , hyps_label
    , default_schedule
    , empty_schedule
    )
where

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

import Utilities.Format
import Utilities.TH

data Schedule = Schedule
        { coarse :: Map Label Expr
        , fine   :: Map Label Expr
        }
    deriving (Eq, Show)

empty_schedule :: Schedule
empty_schedule = Schedule default_schedule M.empty

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
        , c_sched_ref :: [ScheduleChange]
        , f_sched_ref :: Maybe (Label,ProgressProp)
        , old_sched :: Schedule
        , new_sched :: Schedule
        , params    :: Map String Var
        , witness   :: Map Var Expr
        , old_guard :: Map Label Expr
        , new_guard :: Map Label Expr
        , old_acts :: Map Label ()
        , del_acts :: Map Label Action
        , actions  :: Map Label Action
        , eql_vars :: Map String Var
        } deriving (Eq, Show)

default_schedule :: Map Label Expr
default_schedule = M.fromList [(label "default", zfalse)]

all_guards :: Event -> Map Label Expr
all_guards evt = old_guard evt `M.union` new_guard evt

data ScheduleChange = ScheduleChange 
        { remove :: Map Label ()
        , add    :: Map Label ()
        , keep   :: Map Label ()
        , sch_prog :: (Label,ProgressProp) 
        , sch_saf  :: (Label,SafetyProp)
        }
    deriving (Show,Eq,Typeable)

hyps_label :: ScheduleChange -> ProgId
hyps_label = PId . fst . sch_prog

mkCons ''Event

empty_event :: Event
empty_event = makeEvent

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

deleted_sched :: Event -> Schedule
deleted_sched e = Schedule 
        { fine = fine (old_sched e) `M.difference` fine (new_sched e)
        , coarse = coarse (old_sched e) `M.difference` coarse (new_sched e) }

added_sched :: Event -> Schedule
added_sched e = Schedule 
        { fine = fine (new_sched e) `M.difference` fine (old_sched e)
        , coarse = coarse (new_sched e) `M.difference` coarse (old_sched e) }

kept_sched :: Event -> Schedule
kept_sched e = Schedule 
        { fine = fine (new_sched e) `M.intersection` fine (old_sched e)
        , coarse = coarse (new_sched e) `M.intersection` coarse (old_sched e) }

deleted_guard :: Event -> Map Label Expr
deleted_guard e = old_guard e `M.difference` new_guard e

replace :: (Label, ProgressProp) -> (Label, SafetyProp) -> ScheduleChange
replace prog saf = ScheduleChange def def def prog saf

derive makeNFData ''Event
derive makeNFData ''Action
derive makeNFData ''EventId
derive makeNFData ''Schedule
derive makeNFData ''ScheduleChange
