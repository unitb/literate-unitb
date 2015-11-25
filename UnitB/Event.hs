{-# LANGUAGE OverloadedStrings #-}
module UnitB.Event 
    ( module UnitB.Event
    , EventId (..) )
where

    -- Modules
import Theories.SetTheory

import Logic.Expr.Scope

import UnitB.Expr
import UnitB.Property

    -- Libraries
import Control.DeepSeq
import Control.Lens hiding (indices)

import Data.Default
import Data.Either.Combinators
import Data.Foldable as F
import Data.List as L
import Data.List.NonEmpty as NE
import Data.Map  as M
import Data.Maybe
import Data.String
import Data.Typeable

import GHC.Generics hiding (to)

import Test.QuickCheck hiding (label)

import Utilities.Format
import Utilities.Instances
import Utilities.Lens
import Utilities.TH

type Action = Action' Expr
type RawAction = Action' RawExpr

data Action' expr = 
        Assign Var expr 
        | BcmSuchThat [Var] expr
        | BcmIn Var expr
    deriving (Eq,Ord,Functor,Foldable,Traversable,Generic)

instance Show expr => Show (Action' expr) where
    show (Assign v e) = format "{0} := {1}" (view name v) (show e)
    show (BcmIn v e) = format "{0} :∈ {1}" (view name v) (show e)
    show (BcmSuchThat vs e) = format "{0} :| {1}" 
            (intercalate "," $ L.map (view name) vs)
            (show e)

data SkipEventId = SkipEvent
    deriving (Show,Eq,Ord,Typeable,Generic)

instance NFData SkipEventId where

type SkipOrEvent = Either SkipEventId EventId

instance IsString SkipOrEvent where
    fromString = Right . fromString

type Event = Event' Expr
type RawEvent = Event' RawExpr

data Event' expr = Event 
        { _indices    :: Map String Var
        , _raw_coarse_sched :: Maybe (Map Label expr)
        , _fine_sched :: Map Label expr
        , _params     :: Map String Var
        , _raw_guards :: Map Label expr
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
        , _witness   :: Map String (Var,RawExpr)
        , _ind_witness :: Map String (Var,RawExpr)
        , _eql_vars  :: Map String Var
        , _abs_actions :: Map Label (Action' expr)
        } deriving (Eq,Show,Functor,Foldable,Traversable,Generic)

type RawEventMerging = EventMerging RawExpr
type EventMerging' = EventMerging Expr

data EventMerging expr = EvtM  
        { _eventMergingMultiAbstract :: NonEmpty (SkipOrEvent,AbstrEvent' expr)
        , _eventMergingConcrete ::   (SkipOrEvent,ConcrEvent' expr) }
    deriving (Show,Generic)

type RawEventSplitting = EventSplitting RawExpr
type EventSplitting' = EventSplitting Expr

data EventSplitting expr = EvtS   
        { _eventSplittingAbstract :: (SkipOrEvent,AbstrEvent' expr) 
        , _eventSplittingMultiConcrete :: NonEmpty (SkipOrEvent,ConcrEvent' expr) }
    deriving (Show,Generic)

type EventRef' = EventRef Expr
type RawEventRef = EventRef RawExpr

data EventRef expr = EvtRef 
        { _eventRefAbstract :: (SkipOrEvent,AbstrEvent' expr)  
        , _eventRefConcrete :: (SkipOrEvent,ConcrEvent' expr) 
        } deriving (Generic,Show)

default_schedule :: IsGenExpr expr => Map Label expr
default_schedule = M.fromList [(label "default", zfalse)]

type ScheduleChange = ScheduleChange' Expr
type RawScheduleChange = ScheduleChange' RawExpr

data ScheduleChange' expr = ScheduleChange 
        { _remove :: Map Label ()
        , _add    :: Map Label ()
        , _keep   :: Map Label ()
        , _sch_prog :: (Label,ProgressProp' expr) 
        }
    deriving (Show,Eq,Typeable,Functor,Foldable,Traversable,Generic)

makeFields ''EventRef
makeLenses ''EventRef
makeLenses ''ScheduleChange'
makeFields ''EventSplitting
makeFields ''EventMerging
makeClassy ''Event'
makeClassy ''AbstrEvent'
makeClassy ''ConcrEvent'

hyps_label :: ScheduleChange -> ProgId
hyps_label = PId . fst . view sch_prog

mkCons ''Event'

instance IsExpr expr => Default (AbstrEvent' expr) where
    def = genericDefault

instance IsExpr expr => Default (Event' expr) where
    def = empty_event

instance IsExpr expr => Default (ConcrEvent' expr) where
    def = genericDefault

instance (IsExpr expr) => HasScope (Action' expr) where
    scopeCorrect' act@(Assign v e) = withPrefix "assign" $ F.fold 
        [ scopeCorrect' e
        , areVisible [vars,abs_vars] [v] act ]
    scopeCorrect' act@(BcmSuchThat vs p) = withPrefix "become such that" $ F.fold
        [ withPrimes $ scopeCorrect' p 
        , areVisible [vars,abs_vars] vs act ]
    scopeCorrect' act@(BcmIn v s) = withPrefix "become such that" $ F.fold
        [ scopeCorrect' s
        , areVisible [vars,abs_vars] [v] act ]

instance (IsExpr expr) => HasScope (AbstrEvent' expr) where
    scopeCorrect' = withPrefix "abstract" . scopeCorrect' . view old

instance (IsExpr expr) => HasScope (ConcrEvent' expr) where
    scopeCorrect' evt = withPrefix "concrete" $ F.fold
        [ scopeCorrect' $ evt^.new
        , withPrefix "variable witnesses (vars)" $
            withVars ((evt^.params) `M.union` (evt^.indices)) $ 
            areVisible [to $ M.difference <$> view abs_vars <*> view vars] 
                (elems $ fst <$> evt^.witness) 
                (elems $ fst <$> evt^.witness) 
        , withPrefix "variable witnesses (expression)" $
            withVars ((evt^.params) `M.union` (evt^.indices)) 
                $ withAbstract $ withPrimes 
                $ foldMapWithKey scopeCorrect'' (snd <$> evt^.witness)
        , areVisible [abs_vars] (evt^.eql_vars) (evt^.eql_vars) ]

instance IsExpr expr => HasScope (EventMerging expr) where
    scopeCorrect' evt = withPrefix "merging" $ F.fold
        [ withPrefix "index witnesses (vars)" $
            withOnly (evt^.compact.added.indices) $ 
            areVisible [constants] 
                (elems $ fst <$> evt^.ind_witness) 
                (elems $ fst <$> evt^.ind_witness) 
        , withPrefix "index witnesses (expression)" $
            withVars ((evt^.compact.old.params) `M.union` (evt^.compact.old.indices)) 
                $ withAbstract
                $ foldMapWithKey correct (evt^.ind_witness)
        ]
        where
            correct lbl (v,e) = withVars [v] $ scopeCorrect'' lbl e
instance (IsExpr expr) => HasScope (Event' expr) where
    scopeCorrect' e = withPrefix "event" $ withVars (e^.indices) $ F.fold 
        [ foldMapWithKey scopeCorrect'' (e^.coarse_sched) 
        , foldMapWithKey scopeCorrect'' (e^.fine_sched) 
        , withVars (e^.params) $ F.fold 
            [ foldMapWithKey scopeCorrect'' (e^.guards) 
            , foldMapWithKey scopeCorrect'' (e^.actions) 
            ]
        ]

instance Arbitrary expr => Arbitrary (Action' expr) where
    arbitrary = genericArbitrary

infix 1  $=

($=) :: IsExpr expr 
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

ba_pred :: IsExpr expr => Action' expr -> RawExpr
ba_pred (Assign v e) = $typeCheck $ Right (Word (prime v)) `mzeq` Right (getExpr e)
ba_pred (BcmIn v e) = $typeCheck $ Right (Word (prime v)) `zelem` Right (getExpr e)
ba_pred (BcmSuchThat _ e) = getExpr e

rel_action :: [Var] -> Map Label expr -> Map Label (Action' expr)
rel_action vs act = M.map (BcmSuchThat vs) act

keep' :: Map String Var -> Map Label (Action' expr) -> Map String Var
keep' vars acts = vars `M.difference` frame acts

skip' :: Map String Var -> Map Label RawExpr
skip' keep = M.mapKeys f $ M.map g keep
    where
        f n = label ("SKIP:" ++ n)
        g v = Word (prime v) `zeq` Word v

ba_predicate' :: IsExpr expr => Map String Var -> Map Label (Action' expr) -> Map Label RawExpr
ba_predicate' vars acts = M.map ba_pred acts `M.union` skip
    where
        skip = skip' $ keep' vars acts

primed :: Map String Var -> RawExpr -> RawExpr
primed vs e = make_unique "@prime" vs e

empty_event :: IsExpr expr => Event' expr
empty_event = (makeEvent' def def def def) { _raw_coarse_sched = Nothing }

skip_abstr :: IsExpr expr => AbstrEvent' expr
skip_abstr = AbsEvent empty_event Nothing []

skip_event :: IsExpr expr => ConcrEvent' expr
skip_event = CEvent empty_event M.empty M.empty M.empty M.empty

eventRef :: IsExpr expr => EventId -> EventId -> EventRef expr
eventRef aid cid = EvtRef (Right aid,def) (Right cid,def)

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

class ActionRefinement a expr | a -> expr where
    abstract_acts :: Getter a (Map Label (Action' expr))
    concrete_acts :: Getter a (Map Label (Action' expr))

instance ActionRefinement (EventRef expr) expr where
    abstract_acts = old.actions
    concrete_acts = new.actions

class IsExpr expr => EventRefinement a expr | a -> expr where
    abstract_evts :: Getter a (NonEmpty (SkipOrEvent,AbstrEvent' expr))
    concrete_evts :: Getter a (NonEmpty (SkipOrEvent,ConcrEvent' expr))
    evt_pairs :: (EventRefinement a expr) => Getter a (NonEmpty (EventRef expr))

instance IsExpr expr => EventRefinement (EventMerging expr) expr where
    abstract_evts = multiAbstract
    concrete_evts = to $ \(EvtM _ y)  -> y :| []
    evt_pairs = to $ \e -> do
            let c = e^.concrete
            a <- e^.multiAbstract
            return $ EvtRef a c

instance IsExpr expr => EventRefinement (EventSplitting expr) expr where
    abstract_evts = to $ \(EvtS x _)  -> x :| []
    concrete_evts = multiConcrete
    evt_pairs = to $ \e -> do
            let a = e^.abstract
            c <- e^.multiConcrete
            return $ EvtRef a c

coarse_sched :: (IsExpr expr, HasEvent' event expr) => Lens' event (Map Label expr)
coarse_sched = raw_coarse_sched.lens (fromMaybe default_schedule) (const f)
    where
        f m
            | "default" `M.lookup` m == Just zfalse = Nothing
            | otherwise                             = Just m

guards :: HasEvent' event expr => Getter event (Map Label expr)
guards = to $ \e -> M.unions 
        [ e^.raw_guards
        , fromMaybe M.empty $ e^.raw_coarse_sched
        , e^.fine_sched
        ]

all_witnesses :: HasConcrEvent' event expr 
              => Getter event (Map String (Var,RawExpr))
all_witnesses = to $ \e -> (e^.witness) `M.union` (e^.ind_witness)

changes :: IsExpr expr
        => (forall k a. Ord k => Map k a -> Map k a -> Map k a)
        -> Getter (EventRef expr) (Event' expr)
changes diff = to $ \(EvtRef (_,aevt) (_,cevt)) -> create $ do 
    indices .= ( aevt^.indices ) `diff` ( cevt^.indices )
    coarse_sched .= ( aevt^.coarse_sched ) `diff` ( cevt^.coarse_sched )
    fine_sched   .= ( aevt^.fine_sched )   `diff` ( cevt^.fine_sched ) 
    params  .= ( aevt^.params )  `diff` ( cevt^.params ) 
    raw_guards  .= ( aevt^.raw_guards )  `diff` ( cevt^.raw_guards ) 
    actions .= ( aevt^.actions ) `diff` ( cevt^.actions )

schedules :: IsExpr expr => Getter (Event' expr) (Map Label expr)
schedules = to $ \e -> view coarse_sched e `M.union` _fine_sched e

getItems :: EventRefinement evt expr
         => Getter (EventRef expr) (Event' expr) 
         -> Getter (Event' expr) (Map a b) 
         -> Getter evt [(a,b)]
getItems ln ln' = evt_pairs.to NE.toList.to (concatMap $ view $ ln.ln'.to M.toList)

deleted' :: EventRefinement evt expr
         => Getter (Event' expr) (Map a b) 
         -> Getter evt [(a,b)]
deleted' = getItems deleted

deleted :: IsExpr expr => Getter (EventRef expr) (Event' expr)
deleted = changes M.difference

added' :: EventRefinement evt expr
       => Getter (Event' expr) (Map a b) 
       -> Getter evt [(a,b)]
added' = getItems added

added :: IsExpr expr => Getter (EventRef expr) (Event' expr)
added = changes (flip M.difference)

kept' :: EventRefinement evt expr
      => Getter (Event' expr) (Map a b) 
      -> Getter evt [(a,b)]
kept' = getItems kept

kept :: IsExpr expr => Getter (EventRef expr) (Event' expr)
kept = changes M.intersection

total' :: EventRefinement evt expr
       => Getter (Event' expr) (Map a b) 
       -> Getter evt [(a,b)]
total' = getItems total

total :: IsExpr expr => Getter (EventRef expr) (Event' expr)
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
actions_changes diff = to $ \em -> (em^.abs_actions) `diff` (em^.new.actions) 
    -- \(EvtM aevts cevt) -> (snd (NE.head aevts)^.actions) `diff` (cevt^._2.actions)

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

compact :: IsExpr expr 
        => Getter (EventMerging expr) (EventRef expr)
compact = to $ \m -> EvtRef (Left SkipEvent, evt m) (m^.concrete)
    where
        aevts m = snd <$> m^.abstract_evts
        evt :: IsExpr expr => EventMerging expr -> AbstrEvent' expr
        evt m = create $ do
                combineAll' (indices) M.union $ aevts m
                combineAll' (params) M.union $ aevts m
                combineAll' (coarse_sched) M.union $ aevts m
                combineAll' (fine_sched) M.union $ aevts m
                combineAll' (raw_guards) M.union $ aevts m
                combineAll' (actions) M.union $ aevts m

replace :: (Label, ProgressProp) -> ScheduleChange
replace prog = ScheduleChange def def def prog

instance NFData expr => NFData (Event' expr)
instance NFData expr => NFData (AbstrEvent' expr)
instance NFData expr => NFData (EventMerging expr)
instance NFData expr => NFData (EventSplitting expr)
instance NFData expr => NFData (ConcrEvent' expr)
instance NFData expr => NFData (Action' expr)
instance NFData expr => NFData (ScheduleChange' expr)
