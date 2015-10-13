{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveFoldable     #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
module UnitB.Event
    ( EventId (..)
    , SkipEventId (..)
    , SkipOrEvent
    , Event'  (..)
    , Event
    , EventRef'
    , EventRef (..)
    , EventRefinement (..)
    , EventMerging'
    , EventMerging   (..)
    , EventSplitting'
    , EventSplitting (..)
    , evt_pairs
    , AbstrEvent
    , AbstrEvent' (..)
    , HasAbstrEvent' (..)
    , skip_abstr
    , skip_event
    , ConcrEvent
    , ConcrEvent' (..)
    , HasConcrEvent' (..)
    , HasEvent' (..)
    , empty_event
    , Action
    , Action' (..)
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
    , ScheduleChange 
    , ScheduleChange' (..)
    , replace
    , hyps_label
    , default_schedule
    -- , empty_schedule
    , ($=)
    )
where

    -- Modules
import Theories.SetTheory

import UnitB.Expr
import UnitB.Property

    -- Libraries
import Control.Applicative
import Control.DeepSeq
import Control.Lens hiding (indices)

import Data.Default
import Data.DeriveTH
import Data.Either.Combinators
import Data.Foldable (Foldable)
import Data.List as L
import Data.List.NonEmpty as NE
import Data.Map  as M
import Data.String
import Data.Typeable

import GHC.Generics hiding (to)

import Utilities.Format
import Utilities.TH
import Utilities.Instances

-- data Schedule = Schedule
--         { coarse :: Map Label Expr
--         , fine   :: Map Label Expr
--         }
--     deriving (Eq, Show)

-- empty_schedule :: Schedule
-- empty_schedule = Schedule default_schedule M.empty

-- instance Default Schedule where
--     def = empty_schedule

type Action = Action' Expr

data Action' expr = 
        Assign Var expr 
        | BcmSuchThat [Var] expr
        | BcmIn Var expr
    deriving (Eq,Ord,Functor,Foldable,Traversable)

instance Show expr => Show (Action' expr) where
    show (Assign v e) = format "{0} := {1}" (view name v) (show e)
    show (BcmIn v e) = format "{0} :∈ {1}" (view name v) (show e)
    show (BcmSuchThat vs e) = format "{0} :| {1}" 
            (intercalate "," $ L.map (view name) vs)
            (show e)

data SkipEventId = SkipEvent
    deriving (Show,Eq,Ord,Typeable)

instance NFData SkipEventId where

type SkipOrEvent = Either SkipEventId EventId

instance IsString SkipOrEvent where
    fromString = Right . fromString

type Event = Event' Expr

data Event' expr = Event 
        { _indices    :: Map String Var
        , _coarse_sched :: Map Label expr
        , _fine_sched :: Map Label expr
        , _params     :: Map String Var
        , _guards   :: Map Label expr
        , _actions  :: Map Label (Action' expr)
        } deriving (Eq, Show,Functor,Foldable,Traversable,Generic)

type AbstrEvent = AbstrEvent' Expr

data AbstrEvent' expr = AbsEvent
        { _old   :: Event' expr
        , _f_sched_ref :: Maybe (Label,ProgressProp' expr)
        , _c_sched_ref :: [ScheduleChange' expr]
        } deriving (Eq, Show,Functor,Foldable,Traversable,Generic)

type ConcrEvent = ConcrEvent' Expr

data ConcrEvent' expr = CEvent 
        { _new   :: Event' expr
        , _witness   :: Map Var RawExpr
        , _eql_vars  :: Map String Var
        } deriving (Eq,Show,Functor,Foldable,Traversable,Generic)

type EventMerging' = EventMerging RawExpr

data EventMerging expr = EvtM  
        { _eventMergingMultiAbstract :: NonEmpty (SkipOrEvent,AbstrEvent' expr)
        , _eventMergingConcrete ::   (SkipOrEvent,ConcrEvent' expr) }

type EventSplitting' = EventSplitting RawExpr

data EventSplitting expr = EvtS   
        { _eventSplittingAbstract :: (SkipOrEvent,AbstrEvent' expr) 
        , _eventSplittingMultiConcrete :: NonEmpty (SkipOrEvent,ConcrEvent' expr) }

type EventRef' = EventRef RawExpr

data EventRef expr = EvtRef 
        { _eventRefAbstract :: (SkipOrEvent,AbstrEvent' expr)  
        , _eventRefConcrete :: (SkipOrEvent,ConcrEvent' expr) 
        } deriving (Generic)

default_schedule :: Map Label Expr
default_schedule = M.fromList [(label "default", zfalse)]

type ScheduleChange = ScheduleChange' Expr

data ScheduleChange' expr = ScheduleChange 
        { remove :: Map Label ()
        , add    :: Map Label ()
        , keep   :: Map Label ()
        , sch_prog :: (Label,ProgressProp' expr) 
        , sch_saf  :: (Label,SafetyProp' expr)
        }
    deriving (Show,Eq,Typeable,Functor,Foldable,Traversable)

makeFields ''EventRef
makeFields ''EventSplitting
makeFields ''EventMerging
-- makeLenses ''EventSplitting
-- makeLenses ''EventMerging

hyps_label :: ScheduleChange -> ProgId
hyps_label = PId . fst . sch_prog

mkCons ''Event'

instance Default (AbstrEvent' expr) where
    def = genericDefault

instance Default (Event' expr) where
    def = genericDefault

instance Default (ConcrEvent' expr) where
    def = genericDefault

empty_event :: Event' expr
empty_event = makeEvent' def def def def

infix 1  $=

($=) :: HasExpr expr RawExpr 
     => Either [String] expr 
     -> Either [String] expr 
     -> Either [String] (Action' expr)
($=) v e = do
    v' <- getExpr <$> v  
    v' <- mapLeft (const ["expecting a variable"]) $ matching _Word v' 
    e' <- e
    return $ Assign v' e'

frame' :: Action' expr -> Map String Var
frame' (Assign v _) = M.singleton (view name v) v
frame' (BcmIn v _)  = M.singleton (view name v) v
frame' (BcmSuchThat vs _) = M.fromList $ L.zip (L.map (view name) vs) vs

frame :: Map Label (Action' expr) -> Map String Var
frame acts = M.unions $ L.map frame' $ M.elems acts

ba_pred :: HasExpr expr RawExpr => Action' expr -> RawExpr
ba_pred (Assign v e) = $typeCheck $ Right (Word (prime v)) `mzeq` Right (getExpr e)
ba_pred (BcmIn v e) = $typeCheck $ Right (Word (prime v)) `zelem` Right (getExpr e)
ba_pred (BcmSuchThat _ e) = getExpr e

rel_action :: [Var] -> Map Label Expr -> Map Label Action
rel_action vs act = M.map (BcmSuchThat vs) act

keep' :: Map String Var -> Map Label (Action' expr) -> Map String Var
keep' vars acts = vars `M.difference` frame acts

skip' :: Map String Var -> Map Label RawExpr
skip' keep = M.mapKeys f $ M.map g keep
    where
        f n = label ("SKIP:" ++ n)
        g v = Word (prime v) `zeq` Word v

skip_abstr :: AbstrEvent' expr
skip_abstr = AbsEvent empty_event Nothing []

skip_event :: ConcrEvent' expr
skip_event = CEvent empty_event M.empty M.empty

ba_predicate' :: HasExpr expr RawExpr => Map String Var -> Map Label (Action' expr) -> Map Label RawExpr
ba_predicate' vars acts = M.map ba_pred acts `M.union` skip
    where
        skip = skip' $ keep' vars acts

primed :: Map String Var -> RawExpr -> RawExpr
primed vs e = make_unique "@prime" vs e

makeClassy ''Event'
makeClassy ''AbstrEvent'
makeClassy ''ConcrEvent'

instance HasEvent' (AbstrEvent' expr) expr where
    event' = old

instance HasEvent' (ConcrEvent' expr) expr where
    event' = new

instance HasConcrEvent' (EventMerging expr) expr where
    concrEvent' = concrete._2

instance HasEvent' (EventMerging expr) expr where
    event' = concrEvent'.event'

instance HasEvent' (EventSplitting expr) expr where
    event' = abstrEvent'.event'

instance HasAbstrEvent' (EventSplitting expr) expr where
    abstrEvent' = abstract._2

instance HasConcrEvent' (EventRef expr) expr where
    concrEvent' = concrete._2

instance HasAbstrEvent' (EventRef expr) expr where
    abstrEvent' = abstract._2

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

class ActionRefinement a expr | a -> expr where
    abstract_acts :: Getter a (Map Label (Action' expr))
    concrete_acts :: Getter a (Map Label (Action' expr))

instance ActionRefinement (EventRef expr) expr where
    abstract_acts = old.actions
    concrete_acts = new.actions

class EventRefinement a expr | a -> expr where
    abstract_evts :: Getter a (NonEmpty (SkipOrEvent,AbstrEvent' expr))
    concrete_evts :: Getter a (NonEmpty (SkipOrEvent,ConcrEvent' expr))

evt_pairs :: EventRefinement a expr => Getter a (NonEmpty (EventRef expr))
evt_pairs = to $ \e -> do
                a <- e^.abstract_evts
                c <- e^.concrete_evts
                return $ EvtRef a c

instance EventRefinement (EventMerging expr) expr where
    abstract_evts = multiAbstract
    concrete_evts = to $ \(EvtM _ y)  -> y :| []

instance EventRefinement (EventSplitting expr) expr where
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
        -> Getter (EventRef expr) (Event' expr)
changes diff = to $ \(EvtRef (_,aevt) (_,cevt)) -> Event 
    { _indices = ( aevt^.indices ) `diff` ( cevt^.indices )
    , _coarse_sched = ( aevt^.coarse_sched ) `diff` ( cevt^.coarse_sched )
    , _fine_sched   = ( aevt^.fine_sched )   `diff` ( cevt^.fine_sched ) 
    , _params  = ( aevt^.params )  `diff` ( cevt^.params ) 
    , _guards  = ( aevt^.guards )  `diff` ( cevt^.guards ) 
    , _actions = ( aevt^.actions ) `diff` ( cevt^.actions )
    }

schedules :: Getter (Event' expr) (Map Label expr)
schedules = to $ \e -> _coarse_sched e `M.union` _fine_sched e

getItems :: EventRefinement evt expr
         => Getter (EventRef expr) (Event' expr) 
         -> Getter (Event' expr) (Map a b) 
         -> Getter evt [(a,b)]
getItems ln ln' = evt_pairs.to NE.toList.to (concatMap $ view $ ln.ln'.to M.toList)

deleted' :: EventRefinement evt expr
         => Getter (Event' expr) (Map a b) 
         -> Getter evt [(a,b)]
deleted' = getItems deleted

deleted :: Getter (EventRef expr) (Event' expr)
deleted = changes M.difference

added' :: EventRefinement evt expr
       => Getter (Event' expr) (Map a b) 
       -> Getter evt [(a,b)]
added' = getItems added

added :: Getter (EventRef expr) (Event' expr)
added = changes (flip M.difference)

kept' :: EventRefinement evt expr
      => Getter (Event' expr) (Map a b) 
      -> Getter evt [(a,b)]
kept' = getItems kept

kept :: Getter (EventRef expr) (Event' expr)
kept = changes M.intersection

total' :: EventRefinement evt expr
       => Getter (Event' expr) (Map a b) 
       -> Getter evt [(a,b)]
total' = getItems total

total :: Getter (EventRef expr) (Event' expr)
total = changes M.union

new' :: EventRefinement evt expr
     => Getter (Event' expr) (Map a b) 
     -> Getter evt [(a,b)]
new' = getItems new

old' :: EventRefinement evt expr
     => Getter (Event' expr) (Map a b) 
     -> Getter evt [(a,b)]
old' = getItems old

actions_changes :: (Map Label (Action' expr) -> Map Label (Action' expr) -> Map Label (Action' expr))
                -> Getter (EventMerging expr) (Map Label (Action' expr))
actions_changes diff = to $ \(EvtM aevts cevt) -> (snd (NE.head aevts)^.actions) `diff` (cevt^._2.actions)

new_actions :: Getter (EventMerging expr) (Map Label (Action' expr))
new_actions = actions_changes $ flip const

old_actions :: Getter (EventMerging expr) (Map Label (Action' expr))
old_actions = actions_changes const

total_actions :: Getter (EventMerging expr) (Map Label (Action' expr))
total_actions   = actions_changes M.union

kept_actions :: Getter (EventMerging expr) (Map Label (Action' expr))
kept_actions    = actions_changes M.intersection

added_actions :: Getter (EventMerging expr) (Map Label (Action' expr))
added_actions   = actions_changes (flip M.difference)

deleted_actions :: Getter (EventMerging expr) (Map Label (Action' expr))
deleted_actions = actions_changes M.difference

replace :: (Label, ProgressProp) -> (Label, SafetyProp) -> ScheduleChange
replace prog saf = ScheduleChange def def def prog saf

derive makeNFData ''Event'
derive makeNFData ''AbstrEvent'
derive makeNFData ''ConcrEvent'
derive makeNFData ''Action'
-- derive makeNFData ''Schedule
derive makeNFData ''ScheduleChange'
