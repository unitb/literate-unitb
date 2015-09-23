{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
module UnitB.Event
    ( EventId (..)
    , Event   (..)
    , EventRef (..)
    , EventRefinement (..)
    , EventMerging    (..)
    , EventSplitting  (..)
    , evt_pairs
    , AbstrEvent (..)
    , HasAbstrEvent (..)
    , skip_abstr
    , skip_event
    , ConcrEvent (..)
    , HasConcrEvent (..)
    , HasEvent (..)
    , empty_event
    , Action (..)
    , ba_predicate'
    , ba_pred
    , rel_action, primed
    , concrete
    , abstract
    , keep', frame, frame'
    , deleted, kept
    , total, added
    , deleted', kept'
    , total', added'
    , old', new'
    , old_actions, new_actions
    , added_actions, deleted_actions
    , total_actions, kept_actions
    , multiAbstract
    , multiConcrete
    , schedules
    -- , Schedule    (..)
    , ScheduleChange (..)
    , replace
    , hyps_label
    , default_schedule
    -- , empty_schedule
    )
where

    -- Modules
import Logic.Expr

import Theories.SetTheory

import UnitB.Property

    -- Libraries
-- import Control.Applicative
import Control.DeepSeq
import Control.Lens hiding (indices)

import Data.Default
import Data.DeriveTH
import Data.List as L
import Data.List.NonEmpty as NE
import Data.Map  as M
import Data.String
import Data.Typeable

import Utilities.Format
import Utilities.TH

-- data Schedule = Schedule
--         { coarse :: Map Label Expr
--         , fine   :: Map Label Expr
--         }
--     deriving (Eq, Show)

-- empty_schedule :: Schedule
-- empty_schedule = Schedule default_schedule M.empty

-- instance Default Schedule where
--     def = empty_schedule

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
        { _indices    :: Map String Var
        , _coarse_sched :: Map Label Expr
        , _fine_sched :: Map Label Expr
        , _params     :: Map String Var
        , _guards   :: Map Label Expr
        , _actions  :: Map Label Action
        } deriving (Eq, Show)

data AbstrEvent = AbsEvent
        { _old   :: Event
        , _f_sched_ref :: Maybe (Label,ProgressProp)
        , _c_sched_ref :: [ScheduleChange]
        } deriving (Eq, Show)

data ConcrEvent = CEvent 
        { _new   :: Event
        , _witness   :: Map Var Expr
        , _eql_vars  :: Map String Var
        } deriving (Eq, Show)

data EventMerging   = EvtM  
        { _eventMergingMultiAbstract :: NonEmpty (Label,AbstrEvent)
        , _eventMergingConcrete ::   (Label,ConcrEvent) }

data EventSplitting = EvtS   
        { _eventSplittingAbstract :: (Label,AbstrEvent) 
        , _eventSplittingMultiConcrete :: NonEmpty (Label,ConcrEvent) }

data EventRef = EvtRef 
        { _eventRefAbstract :: (Label,AbstrEvent)  
        , _eventRefConcrete :: (Label,ConcrEvent) }

default_schedule :: Map Label Expr
default_schedule = M.fromList [(label "default", zfalse)]

data ScheduleChange = ScheduleChange 
        { remove :: Map Label ()
        , add    :: Map Label ()
        , keep   :: Map Label ()
        , sch_prog :: (Label,ProgressProp) 
        , sch_saf  :: (Label,SafetyProp)
        }
    deriving (Show,Eq,Typeable)

makeFields ''EventRef
makeFields ''EventSplitting
makeFields ''EventMerging
-- makeLenses ''EventSplitting
-- makeLenses ''EventMerging

hyps_label :: ScheduleChange -> ProgId
hyps_label = PId . fst . sch_prog

mkCons ''Event

empty_event :: Event
empty_event = makeEvent

frame' :: Action -> Map String Var
frame' (Assign v _) = M.singleton (name v) v
frame' (BcmIn v _)  = M.singleton (name v) v
frame' (BcmSuchThat vs _) = M.fromList $ L.zip (L.map name vs) vs

frame :: Map Label Action -> Map String Var
frame acts = M.unions $ L.map frame' $ M.elems acts

ba_pred :: Action -> Expr
ba_pred (Assign v e) = $fromJust $ Right (Word (prime v)) `mzeq` Right e
ba_pred (BcmIn v e) = $fromJust $ Right (Word (prime v)) `zelem` Right e
ba_pred (BcmSuchThat _ e) = e

rel_action :: [Var] -> Map Label Expr -> Map Label Action
rel_action vs act = M.map (BcmSuchThat vs) act

keep' :: Map String Var -> Map Label Action -> Map String Var
keep' vars acts = vars `M.difference` frame acts

skip' :: Map String Var -> Map Label Expr
skip' keep = M.mapKeys f $ M.map g keep
    where
        f n = label ("SKIP:" ++ n)
        g v = Word (prime v) `zeq` Word v

skip_abstr :: AbstrEvent
skip_abstr = AbsEvent empty_event Nothing []

skip_event :: ConcrEvent
skip_event = CEvent empty_event M.empty M.empty

ba_predicate' :: Map String Var -> Map Label Action -> Map Label Expr
ba_predicate' vars acts = M.map ba_pred acts `M.union` skip
    where
        skip = skip' $ keep' vars acts

newtype EventId = EventId Label
    deriving (Eq,Ord,Typeable)

instance Show EventId where
    show (EventId x) = show x

instance IsString EventId where
    fromString = EventId . fromString

primed :: Map String Var -> Expr -> Expr
primed vs e = make_unique "@prime" vs e

makeClassy ''Event
makeClassy ''AbstrEvent
makeClassy ''ConcrEvent

instance HasEvent AbstrEvent where
    event = old

instance HasEvent ConcrEvent where
    event = new

instance HasConcrEvent EventMerging where
    concrEvent = concrete._2

instance HasEvent EventMerging where
    event = concrEvent.event

instance HasAbstrEvent EventSplitting where
    abstrEvent = abstract._2

instance HasConcrEvent EventRef where
    concrEvent = concrete._2

instance HasAbstrEvent EventRef where
    abstrEvent = abstract._2

-- class OneAbstract a where
--     abstract :: Lens' a AbstrEvent

-- class OneConcrete a where
--     concrete :: Lens' a ConcrEvent

-- instance OneAbstract EventRef where
--     abstract = lens 
--         (\(EvtRef x _) -> x) 
--         (\(EvtRef _ y) x -> EvtRef x y)

-- instance OneAbstract EventSplitting where
--     abstract = lens _ _

-- instance OneConcrete EventRef where
--     concrete = lens 
--         (\(EvtRef _ x) -> x) 
--         (\(EvtRef x _) y -> EvtRef x y)

-- instance OneConcrete EventMerging where
--     concrete = lens _ _

class ActionRefinement a where
    abstract_acts :: Getter a (Map Label Action)
    concrete_acts :: Getter a (Map Label Action)

instance ActionRefinement EventRef where
    abstract_acts = old.actions
    concrete_acts = new.actions

class EventRefinement a where
    abstract_evts :: Getter a (NonEmpty (Label,AbstrEvent))
    concrete_evts :: Getter a (NonEmpty (Label,ConcrEvent))

evt_pairs :: EventRefinement a => Getter a (NonEmpty EventRef)
evt_pairs = to $ \e -> do
                a <- e^.abstract_evts
                c <- e^.concrete_evts
                return $ EvtRef a c

instance EventRefinement EventMerging where
    abstract_evts = multiAbstract
    concrete_evts = to $ \(EvtM _ y)  -> y :| []

instance EventRefinement EventSplitting where
    abstract_evts = to $ \(EvtS x _)  -> x :| []
    concrete_evts = multiConcrete
    -- evt_pairs = to $ \(EvtS x ys) -> L.map (EvtRef x) ys

-- deleted_sched :: Event -> Schedule
-- deleted_sched e = Schedule 
--         { fine = fine (old_sched e) `M.difference` fine (new_sched e)
--         , coarse = coarse (old_sched e) `M.difference` coarse (new_sched e) }

-- added_sched :: Event -> Schedule
-- added_sched e = Schedule 
--         { fine = fine (new_sched e) `M.difference` fine (old_sched e)
--         , coarse = coarse (new_sched e) `M.difference` coarse (old_sched e) }

-- kept_sched :: Event -> Schedule
-- kept_sched e = Schedule 
--         { fine = fine (new_sched e) `M.intersection` fine (old_sched e)
--         , coarse = coarse (new_sched e) `M.intersection` coarse (old_sched e) }

changes :: (forall k a. Ord k => Map k a -> Map k a -> Map k a)
        -> Getter EventRef Event
changes diff = to $ \(EvtRef (_,aevt) (_,cevt)) -> Event 
    { _indices = ( aevt^.indices ) `diff` ( cevt^.indices )
    , _coarse_sched = ( aevt^.coarse_sched ) `diff` ( cevt^.coarse_sched )
    , _fine_sched   = ( aevt^.fine_sched )   `diff` ( cevt^.fine_sched ) 
    , _params  = ( aevt^.params )  `diff` ( cevt^.params ) 
    , _guards  = ( aevt^.guards )  `diff` ( cevt^.guards ) 
    , _actions = ( aevt^.actions ) `diff` ( cevt^.actions )
    }

schedules :: Getter Event (Map Label Expr)
schedules = to $ \e -> _coarse_sched e `M.union` _fine_sched e

getItems :: EventRefinement evt
         => Getter EventRef Event 
         -> Getter Event (Map a b) 
         -> Getter evt [(a,b)]
getItems ln ln' = evt_pairs.to NE.toList.to (concatMap $ view $ ln.ln'.to M.toList)

deleted' :: EventRefinement evt
         => Getter Event (Map a b) 
         -> Getter evt [(a,b)]
deleted' = getItems deleted

deleted :: Getter EventRef Event
deleted = changes M.difference

added' :: EventRefinement evt
       => Getter Event (Map a b) 
       -> Getter evt [(a,b)]
added' = getItems added

added :: Getter EventRef Event
added = changes (flip M.difference)

kept' :: EventRefinement evt
      => Getter Event (Map a b) 
      -> Getter evt [(a,b)]
kept' = getItems kept

kept :: Getter EventRef Event
kept = changes M.intersection

total' :: EventRefinement evt
       => Getter Event (Map a b) 
       -> Getter evt [(a,b)]
total' = getItems total

total :: Getter EventRef Event
total = changes M.union

new' :: EventRefinement evt
     => Getter Event (Map a b) 
     -> Getter evt [(a,b)]
new' = getItems new

old' :: EventRefinement evt
     => Getter Event (Map a b) 
     -> Getter evt [(a,b)]
old' = getItems old

actions_changes :: (Map Label Action -> Map Label Action -> Map Label Action)
                -> Getter EventMerging (Map Label Action)
actions_changes diff = to $ \(EvtM aevts cevt) -> (snd (NE.head aevts)^.actions) `diff` (cevt^._2.actions)

new_actions :: Getter EventMerging (Map Label Action)
new_actions = actions_changes $ flip const

old_actions :: Getter EventMerging (Map Label Action)
old_actions = actions_changes const

total_actions :: Getter EventMerging (Map Label Action)
total_actions   = actions_changes M.union

kept_actions :: Getter EventMerging (Map Label Action)
kept_actions    = actions_changes M.intersection

added_actions :: Getter EventMerging (Map Label Action)
added_actions   = actions_changes (flip M.difference)

deleted_actions :: Getter EventMerging (Map Label Action)
deleted_actions = actions_changes M.difference

replace :: (Label, ProgressProp) -> (Label, SafetyProp) -> ScheduleChange
replace prog saf = ScheduleChange def def def prog saf

derive makeNFData ''Event
derive makeNFData ''AbstrEvent
derive makeNFData ''ConcrEvent
derive makeNFData ''Action
derive makeNFData ''EventId
-- derive makeNFData ''Schedule
derive makeNFData ''ScheduleChange
