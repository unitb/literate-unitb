{-# LANGUAGE OverloadedStrings
    , TypeFamilies
    , ScopedTypeVariables
    , StandaloneDeriving
    #-} 
module UnitB.Machine where

    -- Modules
import Logic.Expr.Scope
import Logic.Operator as OP
import Logic.Proof
import Logic.Theory as Th

import Theories.Arithmetic

import UnitB.Event
import UnitB.Expr hiding (merge,target)
import UnitB.Proof
import UnitB.Property

    -- Libraries
import Control.Arrow
import Control.DeepSeq
import Control.Lens hiding (indices)

import Control.Monad hiding ( guard )
import Control.Monad.State

import           Data.Default
import           Data.Monoid
import           Data.Foldable as F (all,toList)
import           Data.Functor.Compose
import           Data.Functor.Classes
import           Data.List as L hiding ( union, inits )
import           Data.List.NonEmpty as NE hiding (inits)
import           Data.Maybe as M
import qualified Data.Set as S
import           Data.String
import qualified Data.Traversable as T
import           Data.Typeable

import Utilities.BipartiteGraph as G
import Utilities.CallStack
import Utilities.Format
import Utilities.Instances
import Utilities.Invariant
import Utilities.Lens
import Utilities.Map as M
import Utilities.Partial
import Utilities.Table
import Utilities.TH

all_types :: Theory -> Table Name Sort
all_types th = unions (_types th : L.map all_types (elems $ _extends th)) 

newtype EventTable expr = EventTable { _table :: 
        BiGraph' SkipOrEvent (AbstrEvent' expr) 
                 SkipOrEvent (ConcrEvent' expr) 
                 () }
    deriving (Eq,Default,NFData)

type Machine = Machine' Expr

type RawMachine = Machine' RawExpr

type Machine' = Compose Checked MachineBase

data MachineBase expr = 
    Mch 
        { _machineBaseName :: Name
        , _theory     :: Theory
        , _variables  :: Table Name Var
        , _machineBaseAbs_vars :: Table Name Var
        , _del_vars   :: Table Name Var
        , _init_witness :: Table Name (Var,expr)
        , _del_inits  :: Table Label expr
        , _inits      :: Table Label expr
        , _event_table :: EventTable expr
        , _inh_props  :: PropertySet' expr
        , _props      :: PropertySet' expr
        , _derivation :: Table ProgId ProofTree         
        , _comments   :: Table DocItem String }
    deriving (Eq,Show,Typeable,Functor,Foldable,Traversable,Generic)

instance Eq1 MachineBase where
    eq1 x y = x == y

instance Show1 MachineBase where
    showsPrec1 n m = showsPrec n m

newtype MachineId = MId { getMId :: Name }
    deriving (Eq,Ord,Typeable,Generic,Hashable)

instance PrettyPrintable MachineId where
    pretty = render . getMId

instance Show MachineId where
    show = render . getMId

instance IsString MachineId where
    fromString = MId . makeName assert

instance NFData MachineId where

instance IsLabel MachineId where
    as_label (MId x) = label $ render x

data DocItem = 
        DocVar Name 
        | DocEvent EventId 
        | DocInv Label
        | DocProg Label
    deriving (Eq,Ord,Generic)

instance Hashable DocItem where

instance Show expr => Show (EventTable expr) where
    show (EventTable m) = show m
instance Functor EventTable where
    fmap f (EventTable g) = EventTable $ mapBoth (fmap f) (fmap f) g
instance Foldable EventTable where
    foldMap f (EventTable m) = 
                foldMap (foldMap f) (leftMap m) 
            `mappend` foldMap (foldMap f) (rightMap m)
instance Traversable EventTable where
    traverse f (EventTable g) = EventTable <$> acrossBoth 
            (traverse f) (traverse f) 
            pure g 

instance Show DocItem where
    show (DocVar xs) = format "{0} (variable)" xs
    show (DocEvent xs) = format "{0} (event)" xs
    show (DocInv xs) = format "{0} (invariant)" xs
    show (DocProg xs) = format "{0} (progress)" xs

makeLenses ''EventTable
makeClassy ''MachineBase
makeFields ''MachineBase
mkCons ''MachineBase

class (Controls mch (Internal mch expr)
        , HasExpr expr
        , HasMachineBase (Internal mch expr) expr
        , HasName (Internal mch expr) Name 
        , HasAbs_vars (Internal mch expr) (Table Name Var) ) 
        => HasMachine mch expr | mch -> expr where
    type Internal mch expr :: *
    empty_machine :: Name -> mch

instance HasExpr expr => HasMachine (Machine' expr) expr where
    type Internal (Machine' expr) expr = MachineBase expr
    empty_machine = empty_machine'

instance HasExpr expr => HasMachine (MachineBase expr) expr where
    type Internal (MachineBase expr) expr = MachineBase expr
    empty_machine = view content' . empty_machine'

instance (HasExpr expr) => HasName (Machine' expr) Name where
    name = content assert.name

instance (HasExpr expr) => HasInvariant (MachineBase expr) where
    invariant m = withPrefix (render $ m^.name) $ do
            "inv0" ## F.all ((`isSubmapOf` (m^.variables)).frame.view (new.actions)) (conc_events m) 
            "inv1" ## F.all validEvent (m^.props.transient)
            "inv2" ## F.all tr_wit_enough (m^.props.transient)
                -- valid witnesses
            "inv3" ## G.member (Left SkipEvent) (Left SkipEvent) (m^.events)  
                -- has skip and (a)skip refined by (b)skip
                -- valid scopes
            forM_ (scopeCorrect m) $ \(x,y) -> 
                format "inv4: {0}\n{1}" x y ## False
            "inv5" ## ((m^.abs_vars) `M.difference` (m^.variables)) `isSubmapOf'` (m^.del_vars)
                -- Inv5 is not an equality because del_vars is cummulative
            "inv6" ## ((m^.abs_vars) `M.difference` (m^.del_vars)) `isSubmapOf'` (m^.variables)
            "inv7" ## noClashes (m^.inh_props) (m^.props)
            withPrefix "inv8" $ forM_ (all_refs m) $ \ev -> 
                format "%s - %s" (show $ ev^.abstract._1) (show $ ev^.concrete._1) 
                    ## (ev^.old.actions) === (ev^.abs_actions)
                -- Proofs match properties
            "inv9" ## Pretty ((m^.derivation) `M.difference` (m^.props.progress)) === Pretty M.empty
                -- events in proofs
            "inv10" ## mapM_ ((`elem` (m^.events)).Right) 
                (m^.partsOf (derivation.traverse.traverseEvents))
                -- progress/safety properties referenced in proofs
            "inv11" ## mapM_ (`member'` (m^.all_props.progress)) 
                (m^.partsOf (derivation.traverse.traverseProgId))
            --"inv8" ## no name clashes between declarations of events, state variables and theories
            --"inv9" ## no name clashes between expression tags of events, state variables and theories
        where
            elem = relation "elem" rightMember 
            validEvent (Tr _ _ es _) = L.all (`M.member` nonSkipUpwards m) es
            tr_wit_enough (Tr _ _ es (TrHint ws _)) = fmap M.keys (unions . L.map (view indices) <$> tr_evt es) == Just (M.keys ws)
            tr_evt es = mapM (flip M.lookup $ nonSkipUpwards m) (NE.toList es)

instance HasExpr expr => HasScope (MachineBase expr) where
    scopeCorrect' m = mconcat 
        [ withVars (symbols $ m^.theory) $ mconcat 
            [ withPrefix "inherited"
                $ withVars' vars ((m^.del_vars) `M.union` (m^.abs_vars))
                $ scopeCorrect' $ m^.inh_props 
            , withVars' vars ((m^.variables) `M.union` (m^.abs_vars))
                $ scopeCorrect' $ m^.props 
            , withPrefix "del init"
                $ withVars' vars (m^.abs_vars)
                $ foldMapWithKey scopeCorrect'' $ m^.del_inits
            , withPrefix "init" 
                $ withVars' vars (m^.variables)
                $ foldMapWithKey scopeCorrect'' $ m^.inits
            , withPrefix "witnesses (var)" 
                $ withVars ((m^.abs_vars) `M.difference` (m^.variables))
                $ areVisible [constants] 
                        (M.elems $ fst <$> m^.init_witness) 
                        (M.elems $ fst <$> m^.init_witness)
            , withPrefix "witnesses (expr)" 
                $ withVars ((m^.variables) `M.union` (m^.abs_vars))
                $ foldMapWithKey scopeCorrect'' $ snd <$> m^.init_witness
            , withPrefix "abstract events"
                $ withVars' vars (m^.abs_vars)
                $ foldMapWithKey scopeCorrect'' $ m^.events.to leftMap
            , withPrefix "concrete events"
                $ withVars' abs_vars (m^.abs_vars)
                $ withVars' vars (m^.variables)
                $ foldMapWithKey scopeCorrect'' $ m^.events.to rightMap
            , withPrefix "splitting events"
                $ withVars' abs_vars (m^.abs_vars)
                $ withVars' vars (m^.variables)
                $ foldMapWithKey scopeCorrect'' $ all_downwards m
            ]
        , withPrefix "theory"
            $ scopeCorrect' $ m^.theory
        ]

instance Controls (MachineBase expr) (MachineBase expr) where 

all_refs :: HasMachine machine expr
         => machine -> [EventRef expr]
all_refs = F.toList . all_refs'

all_refs' :: HasMachine machine expr
          => machine -> Map (SkipOrEvent, SkipOrEvent) (EventRef expr)
all_refs' m = readGraph (m!.events) $ do
        es <- getEdges
        m  <- forM (M.toList es) $ \(e,()) -> do
            k  <- (,) <$> leftKey (source e) <*> rightKey (target e)
            ae <- (,) <$> leftKey (source e) <*> leftInfo (source e)
            ce <- (,) <$> rightKey (target e) <*> rightInfo (target e)
            return (k,EvtRef ae ce)
        return $ M.fromList m

conc_events :: HasMachine machine expr
            => machine -> Map SkipOrEvent (ConcrEvent' expr)
conc_events = M.map fst . backwardEdges . view' events

upward_event :: Assert -> Machine' expr -> SkipOrEvent -> EventMerging expr
upward_event arse m lbl = readGraph (m!.events) $ do
        v  <- rightVertex arse lbl
        es <- predecessors v
        EvtM <$> T.forM es (\e -> (,) <$> leftKey (source e) <*> leftInfo (source e))
             <*> ((,) <$> rightKey v <*> rightInfo v)

downward_event :: Assert -> Machine' expr -> SkipOrEvent -> EventSplitting expr
downward_event arse m lbl = readGraph (m!.events) $ do
        v  <- leftVertex arse lbl
        es <- successors v
        EvtS <$> ((,) <$> leftKey v <*> leftInfo v)
             <*> T.forM es (\e -> (,) <$> rightKey (target e) <*> rightInfo (target e))

new_event_set :: HasExpr expr
              => Table Name Var
              -> Map EventId (Event' expr)
              -> EventTable expr
new_event_set vs es = EventTable $ fromJust'' assert $ makeGraph $ do
        skip <- newLeftVertex (Left SkipEvent) skip_abstr
        forM_ (M.toList es) $ \(lbl,e) -> do
            v <- newRightVertex (Right lbl) $ 
                def & new .~ e 
                    & witness .~ makeWitness vs e
            newEdge skip v
        newEdge skip =<< newRightVertex (Left SkipEvent) def

makeWitness :: Table Name Var 
            -> Event' expr -> Table Name (Var,RawExpr)
makeWitness vs = view $ actions.to frame.to f -- .to (traverse._2.namesOf %~ asInternal)
    where 
        f m = M.fromList $ L.map (view name &&& (id &&& Word)) $ M.elems $ m `M.difference` vs

nonSkipUpwards :: HasMachine machine expr
               => machine -> Map EventId (EventMerging expr)
nonSkipUpwards m = readGraph (m!.events) $ do
        es <- getRightVertices
        ms <- forM es $ \e -> do
            es' <- predecessors e
            k   <- rightKey e
            x   <- (EvtM <$> T.forM es' (\e -> (,) <$> leftKey (source e) <*> leftInfo (source e))
                         <*> ((,) <$> rightKey e <*> rightInfo e))
            return $ either (const []) ((:[]).(,x)) k
        return $ M.fromList $ concat ms

nonSkipDownwards :: HasMachine machine expr
                 => machine -> Map EventId (EventSplitting expr)
nonSkipDownwards m = readGraph (m!.events) $ do
        es <- getLeftVertices
        ms <- forM es $ \e -> do
            es' <- successors e
            k   <- leftKey e
            x   <- (EvtS <$> ((,) <$> leftKey e <*> leftInfo e)
                         <*> T.forM es' (\e -> (,) <$> rightKey (target e) <*> rightInfo (target e)))
            return $ either (const []) ((:[]).(,x)) k
        return $ M.fromList $ concat ms

all_upwards :: HasMachine machine expr
            => machine -> Map SkipOrEvent (EventMerging expr)
all_upwards m = readGraph (m!.events) $ do
        es <- getRightVertices
        ms <- forM es $ \e -> do
            es' <- predecessors e
            (,) <$> rightKey e
                <*> (EvtM <$> T.forM es' (\e -> (,) <$> leftKey (source e) <*> leftInfo (source e))
                          <*> ((,) <$> rightKey e <*> rightInfo e))
        return $ M.fromList ms
    -- M.mapWithKey (upward m) (conc_events m)

all_downwards :: HasMachine machine expr
              => machine -> Map SkipOrEvent (EventSplitting expr)
all_downwards m = readGraph (m!.events) $ do
        es <- getLeftVertices
        ms <- forM es $ \e -> do
            es'   <- successors e
            cevts <- T.forM es' (\e -> (,) <$> rightKey (target e) <*> rightInfo (target e))
            aevt  <- ((,) <$> leftKey e <*> leftInfo e)
            e     <- leftKey e
            case e of
                Right e -> 
                    return [(Right e,EvtS aevt cevts)]
                Left SkipEvent ->
                    return [(Left SkipEvent,EvtS aevt (c :|[])) | c <- NE.toList cevts]
        return $ M.fromList $ concat ms

eventTable :: forall expr. HasExpr expr
           => (forall s0 s1. GraphBuilder SkipOrEvent (AbstrEvent' expr) SkipOrEvent (ConcrEvent' expr) () s0 s1 ())
           -> EventTable expr
eventTable gr = EventTable $ fromJust $ makeGraph $ do
    let skip = def 
    a <- newLeftVertex (Left SkipEvent)  $ create $ old .= skip
    c <- newRightVertex (Left SkipEvent) $ create $ new .= skip
    newEdge a c
    gr

event :: HasExpr expr
      => EventId -> State (Event' expr) ()
      -> GraphBuilder SkipOrEvent (AbstrEvent' expr) SkipOrEvent (ConcrEvent' expr) () s0 s1 ()
event eid cmd = do
    askip <- newLeftVertex (Left SkipEvent) def
    evt   <- newRightVertex (Right eid) $ create $ new .= execState cmd def
    newEdge askip evt

split_event :: (HasExpr expr, ?loc :: CallStack)
            => EventId 
            -> State (AbstrEvent' expr) ()
            -> [(EventId,State (ConcrEvent' expr) ())]
            -> GraphBuilder SkipOrEvent (AbstrEvent' expr) SkipOrEvent (ConcrEvent' expr) () s0 s1 ()
split_event eid ae ces = do
        a  <- newLeftVertex (Right eid) (create ae)
        cs <- mapM (uncurry newRightVertex.(Right *** create)) ces
        mapM_ (newEdge a) cs

merge_event :: (HasExpr expr, ?loc :: CallStack)
            => EventId 
            -> [(EventId,State (AbstrEvent' expr) ())]
            -> State (ConcrEvent' expr) ()
            -> GraphBuilder SkipOrEvent (AbstrEvent' expr) SkipOrEvent (ConcrEvent' expr) () s0 s1 ()
merge_event eid aes ce = do
        c  <- newRightVertex (Right eid) (create ce)
        as <- mapM (uncurry newLeftVertex.(Right *** create)) aes
        mapM_ (flip newEdge c) as

refined_event :: HasExpr expr
              => EventId -> State (EventRef expr) ()
              -> GraphBuilder SkipOrEvent (AbstrEvent' expr) SkipOrEvent (ConcrEvent' expr) () s0 s1 ()
refined_event eid cmd = do
    let event = execState cmd $ EvtRef (eid',def) (eid',def)
        eid' = Right eid
    aevt <- newLeftVertex eid' $ event^.abstrEvent'
    cevt <- newRightVertex eid' $ event^.concrEvent'
    newEdge aevt cevt

newEvents :: HasExpr expr 
          => [(EventId,Event' expr)]
          -> EventTable expr
newEvents xs = eventTable $ mapM_ (uncurry event . over _2 put) xs

variableSet :: Machine -> S.Set Var
variableSet m = S.fromList $ M.elems $ m!.variables

events :: HasMachineBase mch expr
       => Lens' mch
                (BiGraph' SkipOrEvent (AbstrEvent' expr) 
                   SkipOrEvent (ConcrEvent' expr)
                   ())
events = event_table . table

all_props :: Getter (MachineBase expr) (PropertySet' expr)
all_props = to $ \m -> (m^.props) <> (m^.inh_props)

-- data Decomposition = Decomposition 

all_notation :: HasMachine machine expr => machine -> Notation
all_notation m = flip precede logical_notation 
        $ L.foldl OP.combine empty_notation 
        $ L.map (view Th.notation) th
    where
        th = (m!.theory) : ascElems (_extends $ m!.theory)

instance (HasExpr expr) => Named (Machine' expr) where
    type NameOf (Machine' expr) = Name
    decorated_name' = adaptName . view name

_name :: (HasMachine machine expr)
      => machine -> MachineId
_name = MId . view' machineBaseName

ba_predicate :: (HasConcrEvent' event RawExpr,Show expr)
             => Machine' expr 
             -> event -> Table Label RawExpr
ba_predicate m evt =          ba_predicate' (m!.variables) (evt^.new.actions :: Table Label RawAction)
                    --`M.union` ba_predicate' (m^.del_vars) (evt^.abs_actions)
                    `M.union` M.mapKeys (label.render) (convertMap $ snd <$> evt^.witness)
                    `M.union` M.mapKeys (skipLbl.render) (convertMap $ M.map eqPrime noWitness)
    where
        _ = ba_predicate' (m!.variables) (evt^.new.actions :: Table Label RawAction) :: Table Label RawExpr
        skipLbl :: String -> Label
        skipLbl = label . ("SKIP:"++)
        eqPrime v = Word (prime v) `zeq` Word v
        noWitness = (m!.del_vars) `M.difference` (evt^.witness)

empty_machine' :: (HasScope expr, HasExpr expr) => Name -> Machine' expr
empty_machine' n = check assert $ flip execState (makeMachineBase n (empty_theory n)) $ do
            -- & events .~ _ $ G.fromList _ _
            events .= G.fromList' assert [(skip,def)] [(skip,def)] [(skip,skip)]
            theory .= (empty_theory n) { _extends = symbol_table 
                [arithmetic, basic_theory] } 
            -- & name
    where
        skip = Left SkipEvent

newMachine :: ( HasMachine machine expr
              , IsChecked machine (Internal machine expr)) 
           => Assert
           -> Name
           -> State (MachineBase expr) a
           -> machine
newMachine arse name f = empty_machine name & content arse.machineBase %~ execState f

instance NFData DocItem where
instance PrettyPrintable DocItem where
    pretty = show
instance NFData expr => NFData (MachineBase expr) where
