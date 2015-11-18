{-# LANGUAGE OverloadedStrings
    , ExistentialQuantification
    , ScopedTypeVariables
    , StandaloneDeriving
    #-} 
module UnitB.Machine where

    -- Modules
import Logic.Expr.Scope
import Logic.Operator
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
import Control.Exception
import Control.Lens hiding (indices)

import Control.Monad hiding ( guard )
import Control.Monad.State
import Control.Monad.Trans.Maybe

import           Data.Default
import           Data.Monoid
import           Data.Foldable as F (all,toList)
import           Data.Functor.Compose
import           Data.Functor.Classes
import           Data.List as L hiding ( union, inits )
import           Data.List.NonEmpty as NE hiding (inits)
import           Data.Map as M
import           Data.Maybe as M
import qualified Data.Set as S
import           Data.String
import qualified Data.Traversable as T
import           Data.Typeable

import Utilities.BipartiteGraph as G
import Utilities.Format
import Utilities.Instances
import Utilities.Invariant
import Utilities.Partial
import Utilities.Lens
import Utilities.TH

all_types :: Theory -> Map String Sort
all_types th = unions (_types th : L.map all_types (elems $ _extends th)) 

newtype EventTable expr = EventTable { _table :: 
        BiGraph' SkipOrEvent (AbstrEvent' expr) 
                 SkipOrEvent (ConcrEvent' expr) 
                 () }
    deriving (Eq,Default,NFData)

type Machine = Machine' Expr

type RawMachine = Machine' RawExpr

type Machine' = Compose Checked Machine''

data Machine'' expr = 
    Mch 
        { _machine''Name :: String
        , _theory     :: Theory
        , _variables  :: Map String Var
        , _machine''Abs_vars :: Map String Var
        , _del_vars   :: Map String Var
        , _init_witness :: Map Var expr
        , _del_inits  :: Map Label expr
        , _inits      :: Map Label expr
        , _event_table :: EventTable expr
        , _inh_props  :: PropertySet' expr
        , _props      :: PropertySet' expr
        , _derivation :: Map ProgId ProofTree         
        , _proofs     :: Map Label Proof
        , _comments   :: Map DocItem String }
    deriving (Eq,Show,Typeable,Functor,Foldable,Traversable,Generic)

instance Eq1 Machine'' where
    eq1 x y = x == y

instance Show1 Machine'' where
    showsPrec1 n m = showsPrec n m

newtype MachineId = MId { getMId :: String }
    deriving (Eq,Ord,Typeable,Generic)

instance Show MachineId where
    show = getMId

instance IsString MachineId where
    fromString = MId

instance NFData MachineId where

instance IsLabel MachineId where
    as_label (MId x) = label x

data DocItem = 
        DocVar String 
        | DocEvent EventId 
        | DocInv Label
        | DocProg Label
    deriving (Eq,Ord,Generic)



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
makeLenses ''Machine''
makeFields ''Machine''

instance (IsExpr expr) => HasName (Machine' expr) String where
    name = content assert.name

--instance Show expr => HasMachine'' (Machine' expr) expr where
--    machine'' = content assert

instance (IsExpr expr) => HasInvariant (Machine'' expr) where
    invariant m = withPrefix (m^.name) $ do
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
            "inv9" ## ((m^.derivation) `M.difference` (m^.props.progress)) === M.empty
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

instance IsExpr expr => HasScope (Machine'' expr) where
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
                $ areVisible [constants] (M.keys $ m^.init_witness) (M.keys $ m^.init_witness)
            , withPrefix "witnesses (expr)" 
                $ withVars ((m^.variables) `M.union` (m^.abs_vars))
                $ foldMapWithKey scopeCorrect'' $ m^.init_witness
            , withPrefix "abstract events"
                $ withVars' vars (m^.abs_vars)
                $ foldMapWithKey scopeCorrect'' $ m^.events.to leftMap
            , withPrefix "concrete events"
                $ withVars' abs_vars (m^.abs_vars)
                $ withVars' vars (m^.variables)
                $ foldMapWithKey scopeCorrect'' $ m^.events.to rightMap
            ]
        , withPrefix "theory"
            $ scopeCorrect' $ m^.theory
        ]

instance Controls (Machine'' expr) (Machine'' expr) where 
    content' = id

all_refs :: Controls machine (Machine'' expr) 
         => machine -> [EventRef expr]
all_refs = F.toList . all_refs'

all_refs' :: Controls machine (Machine'' expr) 
          => machine -> Map (SkipOrEvent, SkipOrEvent) (EventRef expr)
all_refs' m = readGraph (m!.events) $ do
        es <- getEdges
        m  <- forM (M.toList es) $ \(e,()) -> do
            k  <- (,) <$> leftKey (source e) <*> rightKey (target e)
            ae <- (,) <$> leftKey (source e) <*> leftInfo (source e)
            ce <- (,) <$> rightKey (target e) <*> rightInfo (target e)
            return (k,EvtRef ae ce)
        return $ M.fromList m

conc_events :: Controls machine (Machine'' expr)
            => machine -> Map SkipOrEvent (ConcrEvent' expr)
conc_events = M.map fst . backwardEdges . view' events

upward_event :: Show expr => Machine' expr -> SkipOrEvent -> EventMerging expr
upward_event m lbl = fromJust'' assert $ readGraph (m!.events) $ runMaybeT $ do
        v  <- MaybeT $ hasRightVertex lbl
        lift $ do
            es <- predecessors v
            EvtM <$> T.forM es (\e -> (,) <$> leftKey (source e) <*> leftInfo (source e))
                 <*> ((,) <$> rightKey v <*> rightInfo v)

new_event_set :: IsExpr expr
              => Map String Var
              -> Map EventId (Event' expr)
              -> EventTable expr
new_event_set vs es = EventTable $ fromJust'' assert $ makeGraph $ do
        skip <- newLeftVertex (Left SkipEvent) skip_abstr
        forM_ (M.toList es) $ \(lbl,e) -> do
            let f m = M.fromList $ L.map (id &&& Word) $ M.elems $ m `M.difference` vs
            v <- newRightVertex (Right lbl) $ CEvent e (e^.actions.to frame.to f) M.empty M.empty
            newEdge skip v
        newEdge skip =<< newRightVertex (Left SkipEvent) def

nonSkipUpwards :: Controls machine (Machine'' expr)    
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

nonSkipDownwards :: Controls machine (Machine'' expr)    
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

all_upwards :: Controls machine (Machine'' expr)    
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

all_downwards :: Controls machine (Machine'' expr)    
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

eventTable :: forall expr. IsExpr expr
           => (forall s0 s1. GraphBuilder SkipOrEvent (AbstrEvent' expr) SkipOrEvent (ConcrEvent' expr) () s0 s1 ())
           -> EventTable expr
eventTable gr = EventTable $ fromJust $ makeGraph $ do
    let skip = def 
    a <- newLeftVertex (Left SkipEvent)  $ create $ old .= skip
    c <- newRightVertex (Left SkipEvent) $ create $ new .= skip
    newEdge a c
    gr

event :: IsExpr expr
      => EventId -> State (Event' expr) ()
      -> GraphBuilder SkipOrEvent (AbstrEvent' expr) SkipOrEvent (ConcrEvent' expr) () s0 s1 ()
event eid cmd = do
    askip <- newLeftVertex (Left SkipEvent) def
    evt   <- newRightVertex (Right eid) $ create $ new .= execState cmd def
    newEdge askip evt

refined_event :: IsExpr expr
              => EventId -> State (EventRef expr) ()
              -> GraphBuilder SkipOrEvent (AbstrEvent' expr) SkipOrEvent (ConcrEvent' expr) () s0 s1 ()
refined_event eid cmd = do
    let event = execState cmd $ EvtRef (eid',def) (eid',def)
        eid' = Right eid
    aevt <- newLeftVertex eid' $ event^.abstrEvent'
    cevt <- newRightVertex eid' $ event^.concrEvent'
    newEdge aevt cevt

newEvents :: IsExpr expr 
          => [(EventId,Event' expr)]
          -> EventTable expr
newEvents xs = eventTable $ mapM_ (uncurry event . over _2 put) xs

variableSet :: Machine -> S.Set Var
variableSet m = S.fromList $ M.elems $ m!.variables

events :: Lens' (Machine'' expr)
                (BiGraph' SkipOrEvent (AbstrEvent' expr) 
                   SkipOrEvent (ConcrEvent' expr)
                   ())
events = event_table . table

all_props :: Getter (Machine'' expr) (PropertySet' expr)
all_props = to $ \m -> (m^.props) <> (m^.inh_props)

-- data Decomposition = Decomposition 

all_notation :: Show expr => Machine' expr -> Notation
all_notation m = flip precede logical_notation 
        $ L.foldl combine empty_notation 
        $ L.map (view Th.notation) th
    where
        th = (m!.theory) : elems (_extends $ m!.theory)

instance (IsExpr expr) => Named (Machine' expr) where
    decorated_name' = return . view name

_name :: Controls (machine expr) (Machine'' expr)
      => machine expr -> MachineId
_name = MId . view' machine''Name

ba_predicate :: (HasConcrEvent' event RawExpr,Show expr)
             => Machine' expr 
             -> event -> Map Label RawExpr
ba_predicate m evt =          ba_predicate' (m!.variables) (evt^.new.actions)
                    --`M.union` ba_predicate' (m^.del_vars) (evt^.abs_actions)
                    `M.union` M.mapKeys (label . view name) (evt^.witness)
                    `M.union` M.mapKeys skipLbl (M.map eqPrime noWitness)
    where
        skipLbl = label . ("SKIP:"++)
        eqPrime v = Word (prime v) `zeq` Word v
        noWitness = (m!.del_vars) `M.difference` M.mapKeys (view name) (evt^.witness)

mkCons ''Machine''

empty_machine :: (HasScope expr, IsExpr expr) => String -> Machine' expr
empty_machine n = check assert $ flip execState genericDefault $ do
            machine''Name .= n
            -- & events .~ _ $ G.fromList _ _
            events .= G.fromList' assert [(skip,def)] [(skip,def)] [(skip,skip)]
            theory .= empty_theory { _extends = M.fromList [
                ("arithmetic",arithmetic), 
                ("basic", basic_theory)] } 
            -- & name
    where
        skip = Left SkipEvent

newMachine :: IsExpr expr 
           => Assert
           -> String
           -> State (Machine'' expr) a
           -> Machine' expr
newMachine arse name f = empty_machine name & content arse %~ execState f

instance NFData DocItem where
instance NFData expr => NFData (Machine'' expr) where
