{-# LANGUAGE OverloadedStrings
    , TypeFamilies, CPP
    , ScopedTypeVariables
    , StandaloneDeriving
    #-} 
module UnitB.Machine 
    ( module UnitB.Machine 
    , HasTimeout(..) )
where

    -- Modules
import Logic.Expr.Scope
import Logic.Operator as OP
import Logic.Proof
import Logic.Theory as Th

import Logic.Theories

import UnitB.Event
import UnitB.Expr hiding (merge,target)
import UnitB.Proof
import UnitB.Property

    -- Libraries
import Control.Arrow
import Control.DeepSeq
import Control.Invariant
import Control.Lens hiding (indices)
import Control.Lens.HierarchyTH
import Control.Lens.Misc
import Control.Monad hiding ( guard )
import Control.Monad.State
import Control.Precondition

import           Data.Default
import           Data.Hashable
import           Data.Monoid
import           Data.Foldable as F (all,toList)
import           Data.Functor.Compose
#if MIN_VERSION_transformers(0,5,0)
import           Prelude.Extras hiding (Lift1)
import qualified Data.Functor.Classes as F
#else
import Data.Functor.Classes
#endif
import           Data.Graph.Bipartite as G
import           Data.List as L hiding ( union, inits )
import           Data.List.NonEmpty as NE hiding (inits)
import           Data.Map as M
import           Data.Maybe as M
import qualified Data.Set as S
import           Data.Serialize hiding (label,put)
import           Data.String
import qualified Data.Traversable as T
import           Data.Typeable

import GHC.Generics (Generic1)
import GHC.Generics.Instances

import Test.QuickCheck.ZoomEq

import Text.Printf.TH

all_types :: Theory -> Map Name Sort
all_types th = unions (_types th : L.map all_types (elems $ _extends th)) 

newtype EventMap expr = EventMap { _table :: 
        BiGraph' SkipOrEvent (AbstrEvent' expr) 
                 SkipOrEvent (ConcrEvent' expr) 
                 () }
    deriving (Eq,Default,NFData,Generic)

type MachineAST = MachineAST' Expr

type RawMachineAST = MachineAST' RawExpr

type MachineAST' = Compose Checked MachineBase

data MachineBase expr = 
    Mch 
        { _machineBaseName :: Name
        , _theory     :: Theory' expr
        , _variables  :: Map Name Var
        , _oldDefs    :: Map Name expr
        , _machineBaseDefs     :: Map Name expr
        , _machineBaseAbs_vars :: Map Name Var
        , _del_vars   :: Map Name Var
        , _init_witness :: Map Name (Witness' expr)
        , _del_inits  :: Map Label expr
        , _inits      :: Map Label expr
        , _event_table :: EventMap expr
        , _inh_props  :: PropertySet' expr
        , _props      :: PropertySet' expr
        , _derivation :: Map ProgId ProofTree         
        , _comments   :: Map DocItem String 
        , _machineBaseTimeout :: Float }
    deriving (Eq,Show,Typeable,Functor,Foldable,Traversable,Generic,Generic1)

instance ZoomEq expr => ZoomEq (MachineBase expr) where
instance ZoomEq expr => ZoomEq (EventMap expr) where

instance Eq1 MachineBase where
#if MIN_VERSION_transformers(0,5,0)
    (==#) x y = x == y
#else
    eq1 x y = x == y
#endif

#if MIN_VERSION_transformers(0,5,0)
instance F.Eq1 EventMap where
    liftEq f (EventMap m0) (EventMap m1) = 
            liftEqGraph 
                (==) (F.liftEq f) 
                (==) (F.liftEq f)
                (==) 
                m0 m1
instance F.Show1 EventMap where
    liftShowsPrec showA _showAs = lmap _table . 
            liftShowsGraph 
                showsPrec (F.liftShowsPrec showA $ G.liftShowsListPrec showA 0)
                showsPrec (F.liftShowsPrec showA $ G.liftShowsListPrec showA 0)
                showsPrec
instance F.Show1 MachineBase where
    liftShowsPrec = genericLiftShowsPrec
instance F.Eq1 MachineBase where
    liftEq = genericLiftEq
#endif

instance Show1 MachineBase where
    showsPrec1 n m = showsPrec n m

newtype MachineId = MId { getMId :: Name }
    deriving (Eq,Ord,Typeable,Generic,Hashable)

instance PrettyPrintable MachineId where
    pretty = render . getMId

instance Show MachineId where
    show = render . getMId

instance IsString MachineId where
    fromString = MId . makeName

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

instance Show expr => Show (EventMap expr) where
    show (EventMap m) = show m
instance Functor EventMap where
    fmap f (EventMap g) = EventMap $ mapBoth (fmap f) (fmap f) g
instance Foldable EventMap where
    foldMap f (EventMap m) = 
                foldMap (foldMap f) (leftMap m) 
            `mappend` foldMap (foldMap f) (rightMap m)
instance Traversable EventMap where
    traverse f (EventMap g) = EventMap <$> acrossBoth 
            (traverse f) (traverse f) 
            pure g 

instance Show DocItem where
    show (DocVar xs) = [s|%s (variable)|] $ render xs
    show (DocEvent xs) = [s|%s (event)|] $ show xs
    show (DocInv xs) = [s|%s (invariant)|] $ show xs
    show (DocProg xs) = [s|%s (progress)|] $ show xs

makeLenses ''EventMap
makeClassy ''MachineBase
makeFields ''MachineBase
mkCons ''MachineBase

class (Controls mch (Internal mch expr)
        , HasExpr expr
        , HasMachineBase (Internal mch expr) expr
        , HasName (Internal mch expr) Name 
        , HasAbs_vars (Internal mch expr) (Map Name Var) ) 
        => HasMachine mch expr | mch -> expr where
    type Internal mch expr :: *
    empty_machine :: Name -> mch

instance (HasExpr expr,ZoomEq expr) => HasMachine (MachineAST' expr) expr where
    type Internal (MachineAST' expr) expr = MachineBase expr
    empty_machine = empty_machine'

instance (HasExpr expr,ZoomEq expr) => HasMachine (MachineBase expr) expr where
    type Internal (MachineBase expr) expr = MachineBase expr
    empty_machine = view content' . empty_machine'

instance (HasExpr expr,ZoomEq expr) => HasName (MachineAST' expr) Name where
    name = content.name

instance (HasExpr expr,ZoomEq expr) => HasInvariant (MachineBase expr) where
    invariant m = withPrefix (render $ m^.name) $ do
            "inv0" ## F.all ((`isSubmapOf` (m^.variables)).frame.view (new.actions)) (conc_events m) 
            "inv1" ## F.all validEvent (m^.props.transient)
            "inv2" ## F.all tr_wit_enough (m^.props.transient)
                -- valid witnesses
            "inv3" ## G.member (Left SkipEvent) (Left SkipEvent) (m^.events)  
                -- has skip and (a)skip refined by (b)skip
                -- valid scopes
            forM_ (scopeCorrect m) $ \(x,y) -> 
                [s|inv4: %s\n%s|] x y ## False
            "inv5" ## ((m^.abs_vars) `M.difference` (m^.variables)) `isSubmapOf'` (m^.del_vars)
                -- Inv5 is not an equality because del_vars is cummulative
            "inv6" ## ((m^.abs_vars) `M.difference` (m^.del_vars)) `isSubmapOf'` (m^.variables)
            "inv7" ## noClashes (m^.inh_props) (m^.props)
            withPrefix "inv8" $ forM_ (all_refs m) $ \ev -> 
                [s|%s - %s|] (pretty $ ev^.abstract._1) (pretty $ ev^.concrete._1) 
                    ## (ev^.old.actions) .== (ev^.abs_actions)
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

instance (HasExpr expr,ZoomEq expr) => HasScope (MachineBase expr) where
    scopeCorrect' m = mconcat 
        [ withVars (symbols $ m^.theory) $ mconcat 
            [ withPrefix "inherited"
                $ withVars' vars ((m^.del_vars) `M.union` absVarsNdefs)
                $ scopeCorrect' $ m^.inh_props 
            , withVars' vars (varsNdefs `M.union` absVarsNdefs)
                $ scopeCorrect' $ m^.props 
            , withVars' vars ((m^.variables) `M.union` (m^.del_vars))
                $ foldMapWithKey scopeCorrect'' $ m^.defs 
            , withPrefix "del init"
                $ withVars' vars (m^.abs_vars)
                $ foldMapWithKey scopeCorrect'' $ m^.del_inits
            , withPrefix "init" 
                $ withVars' vars varsNdefs
                $ foldMapWithKey scopeCorrect'' $ m^.inits
            , withPrefix "witnesses (var)" 
                $ withVars ((m^.abs_vars) `M.difference` (m^.variables))
                $ areVisible [constants] 
                        (M.elems $ witVar <$> m^.init_witness) 
                        (M.elems $ witVar <$> m^.init_witness)
            , withPrefix "witnesses (expr)" 
                $ withVars (varsNdefs `M.union` (m^.abs_vars))
                $ foldMapWithKey scopeCorrect'' $ m^.init_witness
            , withPrefix "abstract events"
                $ withVars' vars absVarsNdefs
                $ foldMapWithKey scopeCorrect'' $ m^.events.to leftMap
            , withPrefix "concrete events"
                $ withVars' abs_vars (m^.abs_vars)
                $ withVars' vars varsNdefs
                $ foldMapWithKey scopeCorrect'' $ m^.events.to rightMap
            , withPrefix "splitting events"
                $ withVars' abs_vars (m^.abs_vars)
                $ withVars' vars varsNdefs
                $ foldMapWithKey scopeCorrect'' $ all_downwards m
            ]
        , withPrefix "theory"
            $ scopeCorrect' $ m^.theory
        ]
        where
            varsNdefs = (m^.variables) `M.union` (m^.definedSymbols)
            absVarsNdefs = (m^.abs_vars) `M.union` (m^.oldDefinedSymbols)

definedSymbols :: HasExpr expr 
               => Getter (MachineBase expr) (Map Name Var)
definedSymbols = defs.to (M.mapWithKey (\n -> Var n.type_of.getExpr))

oldDefinedSymbols :: HasExpr expr 
               => Getter (MachineBase expr) (Map Name Var)
oldDefinedSymbols = oldDefs.to (M.mapWithKey (\n -> Var n.type_of.getExpr))

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

upward_event :: Pre 
             => MachineAST' expr -> SkipOrEvent -> EventMerging expr
upward_event m lbl = readGraph (m!.events) $ do
        v  <- rightVertex lbl
        es <- predecessors v
        EvtM <$> T.forM es (\e -> (,) <$> leftKey (source e) <*> leftInfo (source e))
             <*> ((,) <$> rightKey v <*> rightInfo v)

downward_event :: Pre 
               => MachineAST' expr -> SkipOrEvent -> EventSplitting expr
downward_event m lbl = readGraph (m!.events) $ do
        v  <- leftVertex lbl
        es <- successors v
        EvtS <$> ((,) <$> leftKey v <*> leftInfo v)
             <*> T.forM es (\e -> (,) <$> rightKey (target e) <*> rightInfo (target e))

new_event_set :: HasExpr expr
              => Map Name Var
              -> Map EventId (Event' expr)
              -> EventMap expr
new_event_set vs es = EventMap $ fromJust' $ makeGraph $ do
        skip <- newLeftVertex (Left SkipEvent) skip_abstr
        forM_ (M.toList es) $ \(lbl,e) -> do
            v <- newRightVertex (Right lbl) $ 
                def & new .~ e 
                    & witness .~ makeWitness vs e
            newEdge skip v
        newEdge skip =<< newRightVertex (Left SkipEvent) def

makeWitness :: HasExpr expr
            => Map Name Var 
            -> Event' expr -> Map Name (Witness' expr)
makeWitness vs = view $ actions.to frame.to f -- .to (traverse._2.namesOf %~ asInternal)
    where 
        wit v = WitEq v $ zword v
        f m = M.fromList $ L.map (view name &&& wit) $ M.elems $ m `M.difference` vs

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

eventMap :: forall expr. HasExpr expr
           => (forall s0 s1. GraphBuilder SkipOrEvent (AbstrEvent' expr) SkipOrEvent (ConcrEvent' expr) () s0 s1 ())
           -> EventMap expr
eventMap gr = EventMap $ fromJust $ makeGraph $ do
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

split_event :: (HasExpr expr, Pre)
            => EventId 
            -> State (AbstrEvent' expr) ()
            -> [(EventId,State (ConcrEvent' expr) ())]
            -> GraphBuilder SkipOrEvent (AbstrEvent' expr) SkipOrEvent (ConcrEvent' expr) () s0 s1 ()
split_event eid ae ces = do
        a  <- newLeftVertex (Right eid) (create ae)
        cs <- mapM (uncurry newRightVertex.(Right *** create)) ces
        mapM_ (newEdge a) cs

merge_event :: (HasExpr expr, Pre)
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
          -> EventMap expr
newEvents xs = eventMap $ mapM_ (uncurry event . over _2 put) xs

variableSet :: MachineAST -> S.Set Var
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
        $ L.foldl' OP.combine empty_notation 
        $ L.map (view Th.notation) th
    where
        th = (getExpr <$> m!.theory) : elems (_extends $ m!.theory)

instance (HasExpr expr,ZoomEq expr) => Named (MachineAST' expr) where
    type NameOf (MachineAST' expr) = Name
    decorated_name' = adaptName . view name

_name :: (HasMachine machine expr)
      => machine -> MachineId
_name = MId . view' machineBaseName

ba_predicate :: (HasConcrEvent' event RawExpr,Show expr)
             => MachineAST' expr 
             -> event -> Map Label RawExpr
ba_predicate m evt =          ba_predicate' (m!.variables) (evt^.new.actions :: Map Label RawAction)
                    --`M.union` ba_predicate' (m^.del_vars) (evt^.abs_actions)
                    `M.union` M.mapKeys (label.render) (witnessDef <$> evt^.witness)
                    `M.union` M.mapKeys (skipLbl.render) (M.map eqPrime noWitness)
    where
        skipLbl :: String -> Label
        skipLbl = label . ("SKIP:"++)
        eqPrime v = Word (prime v) `zeq` Word v
        noWitness = ((m!.del_vars) `M.intersection` (m!.abs_vars)) `M.difference` (evt^.witness)

empty_machine' :: (HasScope expr, HasExpr expr, ZoomEq expr) => Name -> MachineAST' expr
empty_machine' n = check $ flip execState (makeMachineBase n (empty_theory n)) $ do
            -- & events .~ _ $ G.fromList _ _
            events .= G.fromList' [(skip,def)] [(skip,def)] [(skip,skip)]
            theory .= (empty_theory n) { _extends = preludeTheories } 
            timeout .= 1.0
            -- & name
    where
        skip = Left SkipEvent

newMachine :: ( HasMachine machine expr
              , IsChecked machine (Internal machine expr)
              , Pre) 
           => Name
           -> State (MachineBase expr) a
           -> machine
newMachine name f = empty_machine name & content.machineBase %~ execState f

instance NFData DocItem where
instance PrettyPrintable expr => PrettyPrintable (MachineAST' expr) where
instance PrettyPrintable expr => PrettyPrintable (MachineBase expr) where
instance PrettyPrintable DocItem where
    pretty = show
instance NFData expr => NFData (MachineBase expr) where

instance Serialize DocItem where
instance Serialize MachineId where
instance Serialize expr => Serialize (EventMap expr) where
instance Serialize expr => Serialize (MachineBase expr) where
