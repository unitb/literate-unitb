{-# LANGUAGE OverloadedStrings #-}
module UnitB.Event 
    ( module UnitB.Event
    , EventId (..) )
where

    -- Modules
import Logic.Expr.Scope

import UnitB.Expr
import UnitB.Property

    -- Libraries
import Control.DeepSeq
import Control.Lens hiding (indices)

import Data.Default
import Data.Foldable as F
import Data.List as L
import Data.List.NonEmpty as NE
import Data.Map.Class  as M
import Data.Maybe
import Data.Semigroup
import Data.String
import Data.Typeable

import GHC.Generics hiding (to)
import GHC.Generics.Instances

import Test.QuickCheck hiding (label)

import Text.Printf

import Utilities.Lens
import Utilities.Table
import Utilities.TH

type Action = Action' Expr
type RawAction = Action' RawExpr

data Action' expr = 
        Assign Var expr 
        | BcmSuchThat [Var] expr
        | BcmIn Var expr
    deriving (Eq,Ord,Functor,Foldable,Traversable,Generic,Show)

instance PrettyPrintable expr => PrettyPrintable (Action' expr) where
    pretty (Assign v e) = printf "%s := %s" (render $ v^.name) (pretty e)
    pretty (BcmIn v e) = printf "%s :∈ %s" (render $ v^.name) (pretty e)
    pretty (BcmSuchThat vs e) = printf "%s :| %s" 
            (intercalate "," $ L.map (render . view name) vs)
            (pretty e)

data SkipEventId = SkipEvent
    deriving (Show,Eq,Ord,Typeable,Generic)

instance IsLabel SkipEventId where
    as_label SkipEvent = label "SKIP"
instance NFData SkipEventId where
instance Hashable SkipEventId where
instance PrettyPrintable SkipEventId where
    pretty = show

type SkipOrEvent = Either SkipEventId EventId

instance IsString SkipOrEvent where
    fromString = Right . fromString

type Event = Event' Expr
type RawEvent = Event' RawExpr

data Event' expr = Event 
        { _indices    :: Table Name Var
        , _raw_coarse_sched :: Maybe (Table Label expr)
        , _fine_sched :: Table Label expr
        , _params     :: Table Name Var
        , _raw_guards :: Table Label expr
        , _actions  :: Table Label (Action' expr)
        } deriving (Eq, Show,Functor,Foldable,Traversable,Generic)

type AbstrEvent = AbstrEvent' Expr

data AbstrEvent' expr = AbsEvent
        { _old   :: Event' expr
        , _f_sched_ref :: Maybe (Label,ProgressProp' expr)
        , _c_sched_ref :: [ScheduleChange' expr]
        , _ind_witness :: Table Name (Var,RawExpr)
        } deriving (Eq, Show,Functor,Foldable,Traversable,Generic)

type ConcrEvent = ConcrEvent' Expr

data ConcrEvent' expr = CEvent 
        { _new   :: Event' expr
        , _witness   :: Table Name (Var,RawExpr)
        , _eql_vars  :: Table Name Var
        , _abs_actions :: Table Label (Action' expr)
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
        } deriving (Generic,Show,Eq)

default_schedule :: HasGenExpr expr => Table Label expr
default_schedule = M.fromList [(label "default", zfalse)]

type ScheduleChange = ScheduleChange' Expr
type RawScheduleChange = ScheduleChange' RawExpr

data ScheduleChange' expr = ScheduleChange 
        { _remove :: Table Label ()
        , _add    :: Table Label ()
        , _keep   :: Table Label ()
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

instance HasExpr expr => Default (AbstrEvent' expr) where
    def = genericDefault

instance HasExpr expr => Default (Event' expr) where
    def = empty_event

instance HasExpr expr => Default (ConcrEvent' expr) where
    def = genericDefault

instance Semigroup (Event' expr) where
instance Monoid (Event' expr) where
    mempty = genericMEmpty
    mappend = genericMAppend

instance HasExpr expr => Semigroup (ConcrEvent' expr) where
    (<>) e0 e1 = combine new (<>) e0 e1 def
instance HasExpr expr => Semigroup (AbstrEvent' expr) where
    (<>) e0 e1 = combine old (<>) e0 e1 def

instance (HasExpr expr) => HasScope (Action' expr) where
    scopeCorrect' act@(Assign v e) = withPrefix "assign" $ F.fold 
        [ scopeCorrect' e
        , areVisible [vars,abs_vars] [v] act ]
    scopeCorrect' act@(BcmSuchThat vs p) = withPrefix "become such that" $ F.fold
        [ withPrimes $ scopeCorrect' p 
        , areVisible [vars,abs_vars] vs act ]
    scopeCorrect' act@(BcmIn v s) = withPrefix "become such that" $ F.fold
        [ scopeCorrect' s
        , areVisible [vars,abs_vars] [v] act ]

instance (HasExpr expr) => HasScope (AbstrEvent' expr) where
    scopeCorrect' = withPrefix "abstract" . scopeCorrect' . view old

instance (HasExpr expr) => HasScope (ConcrEvent' expr) where
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

instance HasExpr expr => HasScope (EventSplitting expr) where
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
instance (HasExpr expr) => HasScope (Event' expr) where
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

--infix 1  $=

--($=) :: IsExpr expr 
--     => Either [String] expr 
--     -> Either [String] expr 
--     -> Either [String] (Action' expr)
--($=) v e = do
--    v' <- getExpr <$> v  
--    v' <- mapLeft (const ["expecting a variable"]) $ matching _Word v' 
--    e' <- e
--    return $ Assign v' e'

frame' :: Action' expr -> Table Name Var
frame' (Assign v _) = M.singleton (view name v) v
frame' (BcmIn v _)  = M.singleton (view name v) v
frame' (BcmSuchThat vs _) = M.fromList $ L.zip (L.map (view name) vs) vs

frame :: Table Label (Action' expr) -> Table Name Var
frame acts = M.unions $ L.map frame' $ M.elems acts

ba_pred :: HasExpr expr => Action' expr -> RawExpr
ba_pred (Assign v e) = Word (prime v) `zeq` getExpr e
ba_pred (BcmIn v e)  = Word (prime v) `zelemUnchecked` getExpr e
ba_pred (BcmSuchThat _ e) = getExpr e

rel_action :: [Var] -> Table Label expr -> Table Label (Action' expr)
rel_action vs act = M.map (BcmSuchThat vs) act

keep' :: Table Name Var -> Table Label (Action' expr) -> Table Name Var
keep' vars acts = vars `M.difference` frame acts

skip' :: Table Name Var -> Table Label RawExpr
skip' keep = M.mapKeys f $ M.map g keep
    where
        f n = label ("SKIP:" ++ render n)
        g v = Word (prime v) `zeq` Word v

ba_predicate' :: HasExpr expr => Table Name Var -> Table Label (Action' expr) -> Table Label RawExpr
ba_predicate' vars acts = M.map ba_pred acts `M.union` skip
    where
        skip = skip' $ keep' vars acts

primed :: Table Name var -> RawExpr -> RawExpr
primed vs = primeOnly vs

empty_event :: HasExpr expr => Event' expr
empty_event = genericDefault { _raw_coarse_sched = Nothing }

skip_abstr :: HasExpr expr => AbstrEvent' expr
skip_abstr = def

skip_event :: HasExpr expr => ConcrEvent' expr
skip_event = def

eventRef :: HasExpr expr => EventId -> EventId -> EventRef expr
eventRef aid cid = EvtRef (Right aid,def) (Right cid,def)

instance HasEvent' (AbstrEvent' expr) expr where
    event' = old

instance HasEvent' (ConcrEvent' expr) expr where
    event' = new

instance PrettyPrintable (ScheduleChange' expr) where
    pretty _ = "<schedule-change>"

instance (PrettyPrintable expr,Typeable expr) => PrettyRecord (AbstrEvent' expr) where
    recordFields = genericRecordFields [[field|_old|]]
instance (PrettyPrintable expr,Typeable expr) => PrettyRecord (ConcrEvent' expr) where
    recordFields = genericRecordFields [[field|_new|]]
instance PrettyPrintable expr => PrettyRecord (Event' expr) where
    recordFields = genericRecordFields []
instance (PrettyPrintable expr,Typeable expr) => PrettyPrintable (AbstrEvent' expr) where
    pretty = prettyRecord
instance (PrettyPrintable expr,Typeable expr) => PrettyPrintable (ConcrEvent' expr) where
    pretty = prettyRecord
instance PrettyPrintable expr => PrettyPrintable (Event' expr) where
    pretty = prettyRecord

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
    abstract_acts :: Getter a (Table Label (Action' expr))
    concrete_acts :: Getter a (Table Label (Action' expr))

instance ActionRefinement (EventRef expr) expr where
    abstract_acts = old.actions
    concrete_acts = new.actions

class HasExpr expr => EventRefinement a expr | a -> expr where
    abstract_evts :: Getter a (NonEmpty (SkipOrEvent,AbstrEvent' expr))
    concrete_evts :: Getter a (NonEmpty (SkipOrEvent,ConcrEvent' expr))
    evt_pairs :: Getter a (NonEmpty (EventRef expr))

instance HasExpr expr => EventRefinement (EventMerging expr) expr where
    abstract_evts = multiAbstract
    concrete_evts = to $ \(EvtM _ y)  -> y :| []
    evt_pairs = to $ \e -> do
            let c = e^.concrete
            a <- e^.multiAbstract
            return $ EvtRef a c

instance HasExpr expr => EventRefinement (EventSplitting expr) expr where
    abstract_evts = to $ \(EvtS x _)  -> x :| []
    concrete_evts = multiConcrete
    evt_pairs = to $ \e -> do
            let a = e^.abstract
            c <- e^.multiConcrete
            return $ EvtRef a c

coarse_sched :: (HasExpr expr, HasEvent' event expr) => Lens' event (Table Label expr)
coarse_sched = raw_coarse_sched.lens (fromMaybe default_schedule) (const f)
    where
        f m
            | "default" `M.lookup` m == Just zfalse = Nothing
            | otherwise                             = Just m

guards :: HasEvent' event expr => Getter event (Table Label expr)
guards = to $ \e -> M.unions 
        [ e^.raw_guards
        , fromMaybe M.empty $ e^.raw_coarse_sched
        , e^.fine_sched
        ]


{-# INLINE changes #-}
changes :: (HasExpr expr)
        => (forall k a map. (IsMap map,IsKey map k) => map k a -> map k a -> map k a)
        -> Getter (EventRef expr) (Event' expr)
changes diff = to $ \(EvtRef (_,aevt) (_,cevt)) -> create $ do 
    indices .= ( aevt^.indices ) `diff` ( cevt^.indices )
    coarse_sched .= ( aevt^.coarse_sched ) `diff` ( cevt^.coarse_sched )
    fine_sched   .= ( aevt^.fine_sched )   `diff` ( cevt^.fine_sched ) 
    params  .= ( aevt^.params )  `diff` ( cevt^.params ) 
    raw_guards  .= ( aevt^.raw_guards )  `diff` ( cevt^.raw_guards ) 
    actions .= ( aevt^.actions ) `diff` ( cevt^.actions )

schedules :: HasExpr expr => Getter (Event' expr) (Table Label expr)
schedules = to $ \e -> view coarse_sched e `M.union` _fine_sched e

getItems :: (EventRefinement evt expr,Ord a)
         => Getter (EventRef expr) (Event' expr) 
         -> Getter (Event' expr) (Table a b) 
         -> Getter evt [(a,b)]
getItems ln ln' = evt_pairs.to NE.toList.to (concatMap $ view $ ln.ln'.to M.toList)

deleted' :: (EventRefinement evt expr,Ord a)
         => Getter (Event' expr) (Table a b) 
         -> Getter evt [(a,b)]
deleted' = getItems deleted

deleted :: HasExpr expr => Getter (EventRef expr) (Event' expr)
deleted = changes M.difference

added' :: (EventRefinement evt expr,Ord a)
       => Getter (Event' expr) (Table a b) 
       -> Getter evt [(a,b)]
added' = getItems added

added :: HasExpr expr => Getter (EventRef expr) (Event' expr)
added = changes (flip M.difference)

kept' :: (EventRefinement evt expr,Ord a)
      => Getter (Event' expr) (Table a b) 
      -> Getter evt [(a,b)]
kept' = getItems kept

kept :: HasExpr expr => Getter (EventRef expr) (Event' expr)
kept = changes M.intersection

total' :: (EventRefinement evt expr,Ord a)
       => Getter (Event' expr) (Table a b) 
       -> Getter evt [(a,b)]
total' = getItems total

total :: HasExpr expr => Getter (EventRef expr) (Event' expr)
total = changes M.union

new' :: (EventRefinement evt expr,Ord a)
     => Getter (Event' expr) (Table a b) 
     -> Getter evt [(a,b)]
new' = getItems new

old' :: (EventRefinement evt expr,Ord a)
     => Getter (Event' expr) (Table a b) 
     -> Getter evt [(a,b)]
old' = getItems old

actions_changes :: (Table Label (Action' expr) -> Table Label (Action' expr) -> Table Label (Action' expr))
                -> Getter (EventMerging expr) (Table Label (Action' expr))
actions_changes diff = to $ \em -> (em^.abs_actions) `diff` (em^.new.actions) 
    -- \(EvtM aevts cevt) -> (snd (NE.head aevts)^.actions) `diff` (cevt^._2.actions)

new_actions :: Getter (EventMerging expr) (Table Label (Action' expr))
new_actions = actions_changes $ flip const

old_actions :: Getter (EventMerging expr) (Table Label (Action' expr))
old_actions = actions_changes const

total_actions :: Getter (EventMerging expr) (Table Label (Action' expr))
total_actions   = actions_changes M.union

kept_actions :: Getter (EventMerging expr) (Table Label (Action' expr))
kept_actions    = actions_changes M.intersection

added_actions :: Getter (EventMerging expr) (Table Label (Action' expr))
added_actions   = actions_changes (flip M.difference)

deleted_actions :: Getter (EventMerging expr) (Table Label (Action' expr))
deleted_actions = actions_changes M.difference

compact :: EventRefinement event expr
        => Getter event (EventRef expr)
compact = to $ \m -> EvtRef 
        (Left SkipEvent, sconcat $ snd <$> m^.abstract_evts) 
        (Left SkipEvent, sconcat $ snd <$> m^.concrete_evts)

replace :: (Label, ProgressProp) -> ScheduleChange
replace prog = ScheduleChange def def def prog

instance NFData expr => NFData (Event' expr)
instance NFData expr => NFData (AbstrEvent' expr)
instance NFData expr => NFData (EventMerging expr)
instance NFData expr => NFData (EventSplitting expr)
instance NFData expr => NFData (ConcrEvent' expr)
instance NFData expr => NFData (Action' expr)
instance NFData expr => NFData (ScheduleChange' expr)
