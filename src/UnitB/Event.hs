{-# LANGUAGE OverloadedStrings,CPP #-}
module UnitB.Event 
    ( module UnitB.Event
    , EventId (..) )
where

    -- Modules
import Logic.Expr.Scope

import UnitB.Expr
import UnitB.Property

    -- Libraries
import Control.Applicative
import Control.DeepSeq
import Control.Lens hiding (indices)
import Control.Lens.HierarchyTH
import Control.Lens.Misc

import Data.Default
#if MIN_VERSION_transformers(0,5,0)
import qualified Data.Functor.Classes as F
#endif
import Data.Foldable as F
import Data.Hashable
import Data.List as L
import Data.List.NonEmpty as NE
import Data.Map  as M
import Data.Maybe
import Data.Semigroup hiding (All)
import Data.Serialize hiding (label)
import Data.String
import Data.Typeable

import GHC.Generics hiding (to)
import GHC.Generics.Instances

import Test.QuickCheck hiding (label)
import Test.QuickCheck.ZoomEq

import Text.Printf

type Action = Action' Expr
type RawAction = Action' RawExpr

data Action' expr = 
        Assign Var expr 
        | BcmSuchThat [Var] expr
        | BcmIn Var expr
    deriving (Eq,Ord,Functor,Foldable,Traversable,Generic,Generic1,Show)

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
instance ZoomEq SkipEventId where
instance PrettyPrintable SkipEventId where
    pretty = show

prettyEvent :: SkipOrEvent -> String
prettyEvent = either (const "[skip]") pretty

type SkipOrEvent = Either SkipEventId EventId

instance IsString SkipOrEvent where
    fromString = Right . fromString

type Event = Event' Expr
type RawEvent = Event' RawExpr

data Witness' expr = 
        WitEq { witVar :: Var, witExpr :: expr }
        | WitSuch { witVar :: Var, witExpr :: expr }
        | WitIn { witVar :: Var, witExpr :: expr }
    deriving (Eq, Show,Functor,Foldable,Traversable,Generic,Generic1)

type Witness = Witness' Expr
type RawWitness = Witness' RawExpr

witnessDef :: HasExpr expr => Witness' expr -> RawExpr
witnessDef (WitEq v e)   = Word (prime v) `zeq` getExpr e
witnessDef (WitIn v e)   = Word (prime v) `zelemUnchecked` getExpr e
witnessDef (WitSuch _ e) = getExpr e

witnessOf :: Var -> Action' expr -> Witness' expr
witnessOf v (Assign _ e)  = WitEq v e
witnessOf v (BcmIn _ e)   = WitIn v e
witnessOf v (BcmSuchThat _ e) = WitSuch v e

data Event' expr = Event 
        { _indices    :: Map Name Var
        , _raw_coarse_sched :: Maybe (Map Label expr)
        , _fine_sched :: Map Label expr
        , _params     :: Map Name Var
        , _raw_guards :: Map Label expr
        , _actions  :: Map Label (Action' expr)
        } deriving (Eq, Show,Functor,Foldable,Traversable,Generic,Generic1)

type AbstrEvent = AbstrEvent' Expr

data AbstrEvent' expr = AbsEvent
        { _old   :: Event' expr
        , _f_sched_ref :: Maybe (Label,ProgressProp' expr)
        , _c_sched_ref :: [ScheduleChange' expr]
        , _ind_witness :: Map Name (Witness' expr)
        } deriving (Eq, Show,Functor,Foldable,Traversable,Generic,Generic1)

type ConcrEvent = ConcrEvent' Expr

data ConcrEvent' expr = CEvent 
        { _new   :: Event' expr
        , _witness   :: Map Name (Witness' expr)
        , _param_witness :: Map Name (Witness' expr)
        , _eql_vars  :: Map Name Var
        , _abs_actions :: Map Label (Action' expr)
        } deriving (Eq,Show,Functor,Foldable,Traversable,Generic,Generic1)

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

default_schedule :: HasGenExpr expr => Map Label expr
default_schedule = M.fromList [(label "default", zfalse)]

type ScheduleChange = ScheduleChange' Expr
type RawScheduleChange = ScheduleChange' RawExpr

data ScheduleChange' expr = ScheduleChange 
        { _add    :: Map Label ()
        , _sch_prog :: (Label,ProgressProp' expr) 
        }
    deriving (Show,Eq,Typeable,Functor,Foldable,Traversable,Generic,Generic1)

makePrisms ''Action'
makeFields ''EventRef
makeLenses ''EventRef
makeLenses ''ScheduleChange'
makeFields ''EventSplitting
makeFields ''EventMerging
makeClassy ''Event'
makeClassy ''AbstrEvent'
makeClassy ''ConcrEvent'
mkCons ''Event'

type OldNewPair expr = (Map Label expr,Map Label expr)

oldNewPair :: HasExpr expr
           => AbstrEvent' expr
           -> ScheduleChange' expr 
           -> OldNewPair ()
oldNewPair e sch = (() <$ e^.coarse_sched,sch^.add)

unrefinedSched :: HasExpr expr
               => EventSplitting expr
               -> Maybe (OldNewPair expr)
unrefinedSched e 
        | M.null new = Nothing
        | otherwise  = Just (e^.old.coarse_sched,new)
    where
        new = M.unions [ unref e' | e' <- NE.toList $ e^.evt_pairs ]
        unref e' = (e'^.added.coarse_sched) `M.difference` M.unions (L.map (view add) $ e^.c_sched_ref)

hyps_label :: ScheduleChange -> ProgId
hyps_label = PId . fst . view sch_prog

instance ZoomEq expr => ZoomEq (ScheduleChange' expr) where

instance ZoomEq expr => ZoomEq (AbstrEvent' expr) where

instance HasExpr expr => Default (AbstrEvent' expr) where
    def = genericDefault

instance ZoomEq expr => ZoomEq (Event' expr) where

instance HasExpr expr => Default (Event' expr) where
    def = empty_event

instance ZoomEq expr => ZoomEq (ConcrEvent' expr) where

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

instance (HasExpr expr) => HasScope (Witness' expr) where
    scopeCorrect' = scopeCorrect' . witExpr

instance (HasExpr expr) => HasScope (AbstrEvent' expr) where
    scopeCorrect' = withPrefix "abstract" . scopeCorrect' . view old

instance (HasExpr expr) => HasScope (ConcrEvent' expr) where
    scopeCorrect' evt = withPrefix "concrete" $ F.fold
        [ scopeCorrect' $ evt^.new
        , withPrefix "variable witnesses (vars)" $
            withVars ((evt^.params) `M.union` (evt^.indices)) $ 
            areVisible [to $ M.difference <$> view abs_vars <*> view vars] 
                (elems $ witVar <$> evt^.witness) 
                (elems $ witVar <$> evt^.witness) 
        , withPrefix "variable witnesses (expression)" $
            withVars ((evt^.params) `M.union` (evt^.indices)) 
                $ withAbstract $ withPrimes 
                $ foldMapWithKey scopeCorrect'' (witExpr <$> evt^.witness)
        , areVisible [abs_vars] (evt^.eql_vars) (evt^.eql_vars) ]

instance HasExpr expr => HasScope (EventSplitting expr) where
    scopeCorrect' evt = withPrefix "merging" $ F.fold
        [ withPrefix "index witnesses (vars)" $
            withOnly (evt^.compact.added.indices) $ 
            areVisible [constants] 
                (elems $ witVar <$> evt^.ind_witness) 
                (elems $ witVar <$> evt^.ind_witness) 
        , withPrefix "index witnesses (expression)" $
            withVars ((evt^.compact.old.params) `M.union` (evt^.compact.old.indices)) 
                $ withAbstract
                $ foldMapWithKey correct (evt^.ind_witness)
        ]
        where
            correct lbl w = withVars [witVar w] $ scopeCorrect'' lbl (witExpr w)
instance (HasExpr expr) => HasScope (Event' expr) where
    scopeCorrect' e = withPrefix "event" $ withVars (e^.indices) $ F.fold 
        [ withPrefix (pretty e) $ foldMapWithKey scopeCorrect'' (e^.coarse_sched) 
        , foldMapWithKey scopeCorrect'' (e^.fine_sched) 
        , withVars (e^.params) $ F.fold 
            [ foldMapWithKey scopeCorrect'' (e^.guards) 
            , foldMapWithKey scopeCorrect'' (e^.actions) 
            ]
        ]

instance ZoomEq expr => ZoomEq (Action' expr) where
instance Arbitrary expr => Arbitrary (Action' expr) where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance ZoomEq expr => ZoomEq (Witness' expr) where
instance Arbitrary expr => Arbitrary (Witness' expr) where
    arbitrary = genericArbitrary
    shrink = genericShrink

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

frame' :: Action' expr -> Map Name Var
frame' (Assign v _) = M.singleton (view name v) v
frame' (BcmIn v _)  = M.singleton (view name v) v
frame' (BcmSuchThat vs _) = M.fromList $ L.zip (L.map (view name) vs) vs

frame :: Map Label (Action' expr) -> Map Name Var
frame acts = M.unions $ L.map frame' $ M.elems acts

ba_pred :: HasExpr expr => Action' expr -> RawExpr
ba_pred (Assign v e) = Word (prime v) `zeq` getExpr e
ba_pred (BcmIn v e)  = Word (prime v) `zelemUnchecked` getExpr e
ba_pred (BcmSuchThat _ e) = getExpr e

rel_action :: [Var] -> Map Label expr -> Map Label (Action' expr)
rel_action vs act = M.map (BcmSuchThat vs) act

keep' :: Map Name Var -> Map Label (Action' expr) -> Map Name Var
keep' vars acts = vars `M.difference` frame acts

skip' :: Map Name Var -> Map Label RawExpr
skip' keep = M.mapKeys f $ M.map g keep
    where
        f n = label ("SKIP:" ++ render n)
        g v = Word (prime v) `zeq` Word v

ba_predicate' :: HasExpr expr => Map Name Var -> Map Label (Action' expr) -> Map Label RawExpr
ba_predicate' vars acts = M.map ba_pred acts `M.union` skip
    where
        skip = skip' $ keep' vars acts

primed :: Map Name var -> RawExpr -> RawExpr
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
instance PrettyPrintable expr => PrettyPrintable (Event' expr) where
    pretty = prettyRecord
instance PrettyPrintable expr => PrettyPrintable (Witness' expr) where
    pretty (WitEq v e)   = pretty v ++ " := " ++ pretty e
    pretty (WitSuch v e) = pretty v ++ " :| " ++ pretty e
    pretty (WitIn v e)   = pretty v ++ " :∈ " ++ pretty e

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

isOneToOne :: EventRefinement evt expr
           => evt -> Bool
isOneToOne x = neOne (x^.abstract_evts) && neOne (x^.concrete_evts)
    where
        neOne = L.null . NE.tail

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

coarse_sched :: (HasExpr expr, HasEvent' event expr) => Lens' event (Map Label expr)
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

data Changes = Old | New | All | Kept

{-# INLINE changes #-}
changes :: (HasExpr expr)
        => Changes
        -> Getter (EventRef expr) (Event' expr)
changes ch = to $ \(EvtRef (_,aevt) (_,cevt)) -> create $ do 
        indices .= ( aevt^.indices ) `diff` ( cevt^.indices )
        raw_coarse_sched .= combine ( aevt^.raw_coarse_sched ) ( cevt^.raw_coarse_sched )
        fine_sched   .= ( aevt^.fine_sched )   `diff` ( cevt^.fine_sched ) 
        params  .= ( aevt^.params )  `diff` ( cevt^.params ) 
        raw_guards  .= ( aevt^.raw_guards )  `diff` ( cevt^.raw_guards ) 
        actions .= ( aevt^.actions ) `diff` ( cevt^.actions )
    where
        diff :: Ord k
             => Map k a -> Map k a -> Map k a
        diff = case ch of
                    Old -> M.difference
                    New -> flip M.difference
                    Kept -> M.intersection
                    All  -> M.union
        combine asch csch = case ch of
                    Old  -> liftA2 M.difference asch csch <|> asch <|> emp csch
                    New  -> liftA2 (flip M.difference) asch csch <|> csch <|> emp asch
                    Kept -> liftA2 M.intersection asch csch <|> (M.empty <$ asch) <|> (M.empty <$ csch)
                    All  -> liftA2 M.union asch csch <|> asch <|> csch
        emp Nothing = Just M.empty
        emp (Just _)= Nothing

schedules :: HasExpr expr => Getter (Event' expr) (Map Label expr)
schedules = to $ \e -> view coarse_sched e `M.union` _fine_sched e

getItems :: (EventRefinement evt expr,Ord a)
         => Getter (EventRef expr) (Event' expr) 
         -> Getter (Event' expr) (Map a b) 
         -> Getter evt [(a,b)]
getItems ln ln' = evt_pairs.to NE.toList.to (concatMap $ view $ ln.ln'.to M.toList)

deleted' :: (EventRefinement evt expr,Ord a)
         => Getter (Event' expr) (Map a b) 
         -> Getter evt [(a,b)]
deleted' = getItems deleted

deleted :: HasExpr expr => Getter (EventRef expr) (Event' expr)
deleted = changes Old

added' :: (EventRefinement evt expr,Ord a)
       => Getter (Event' expr) (Map a b) 
       -> Getter evt [(a,b)]
added' = getItems added

added :: HasExpr expr => Getter (EventRef expr) (Event' expr)
added = changes New

kept' :: (EventRefinement evt expr,Ord a)
      => Getter (Event' expr) (Map a b) 
      -> Getter evt [(a,b)]
kept' = getItems kept

kept :: HasExpr expr => Getter (EventRef expr) (Event' expr)
kept = changes Kept

total' :: (EventRefinement evt expr,Ord a)
       => Getter (Event' expr) (Map a b) 
       -> Getter evt [(a,b)]
total' = getItems total

total :: HasExpr expr => Getter (EventRef expr) (Event' expr)
total = changes All

new' :: (EventRefinement evt expr,Ord a)
     => Getter (Event' expr) (Map a b) 
     -> Getter evt [(a,b)]
new' = getItems new

old' :: (EventRefinement evt expr,Ord a)
     => Getter (Event' expr) (Map a b) 
     -> Getter evt [(a,b)]
old' = getItems old

actions_changes :: (Map Label (Action' expr) -> Map Label (Action' expr) -> Map Label (Action' expr))
                -> Getter (EventMerging expr) (Map Label (Action' expr))
actions_changes diff = to $ \em -> (em^.abs_actions) `diff` (em^.new.actions) 
    -- \(EvtM aevts cevt) -> (snd (NE.head aevts)^.actions) `diff` (cevt^._2.actions)

new_actions :: Getter (EventMerging expr) (Map Label (Action' expr))
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

compact :: EventRefinement event expr
        => Getter event (EventRef expr)
compact = to $ \m -> EvtRef 
        (Left SkipEvent, sconcat $ snd <$> m^.abstract_evts) 
        (Left SkipEvent, sconcat $ snd <$> m^.concrete_evts)

replace :: (Label, ProgressProp) -> ScheduleChange
replace prog = ScheduleChange def prog

#if MIN_VERSION_transformers(0,5,0)
instance F.Show1 Event' where
    liftShowsPrec = genericLiftShowsPrec
instance F.Show1 Action' where
    liftShowsPrec = genericLiftShowsPrec
instance F.Show1 AbstrEvent' where
    liftShowsPrec = genericLiftShowsPrec
instance F.Show1 ConcrEvent' where
    liftShowsPrec = genericLiftShowsPrec
instance F.Show1 Witness' where
    liftShowsPrec = genericLiftShowsPrec
instance F.Show1 ScheduleChange' where
    liftShowsPrec = genericLiftShowsPrec
instance F.Eq1 Event' where
    liftEq = genericLiftEq
instance F.Eq1 Action' where
    liftEq = genericLiftEq
instance F.Eq1 AbstrEvent' where
    liftEq = genericLiftEq
instance F.Eq1 ConcrEvent' where
    liftEq = genericLiftEq
instance F.Eq1 Witness' where
    liftEq = genericLiftEq
instance F.Eq1 ScheduleChange' where
    liftEq = genericLiftEq
#endif

instance NFData expr => NFData (Event' expr)
instance NFData expr => NFData (AbstrEvent' expr)
instance NFData expr => NFData (EventMerging expr)
instance NFData expr => NFData (EventSplitting expr)
instance NFData expr => NFData (ConcrEvent' expr)
instance NFData expr => NFData (Action' expr)
instance NFData expr => NFData (ScheduleChange' expr)
instance NFData expr => NFData (Witness' expr)
instance NFData expr => NFData (EventRef expr)

instance Serialize expr => Serialize (Event' expr) where
instance Serialize expr => Serialize (AbstrEvent' expr) where
instance Serialize expr => Serialize (ConcrEvent' expr) where
instance Serialize expr => Serialize (ScheduleChange' expr) where
instance Serialize expr => Serialize (Action' expr) where
instance Serialize expr => Serialize (Witness' expr) where
instance Serialize SkipEventId where
