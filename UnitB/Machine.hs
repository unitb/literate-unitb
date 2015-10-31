{-# LANGUAGE OverloadedStrings
    , ExistentialQuantification
    , ScopedTypeVariables
    , StandaloneDeriving
    #-} 
module UnitB.Machine where

    -- Modules
import Logic.ExpressionStore (ExprStore, empty_store)
import Logic.Operator
import Logic.Proof.POGenerator ( POGen )
import Logic.Theory as Th

import Theories.SetTheory
import Theories.FunctionTheory
import Theories.Arithmetic

import UnitB.Event
import UnitB.Expr hiding (merge,target)
import UnitB.Property

    -- Libraries
import Control.DeepSeq
import Control.Lens

import Control.Monad hiding ( guard )
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Control.Monad.Writer hiding ( guard )

import           Data.Default
import           Data.DeriveTH
import           Data.Foldable as F (all)
import           Data.List as L hiding ( union, inits )
import           Data.List.NonEmpty as NE
import           Data.Map as M
import           Data.Maybe as M
-- import           Data.Maybe as M
import qualified Data.Set as S
import qualified Data.Traversable as T
import           Data.Typeable

import Utilities.BipartiteGraph
import Utilities.Format
import Utilities.HeterogenousEquality
import Utilities.Instances
import Utilities.TH

all_types :: Theory -> Map String Sort
all_types th = unions (_types th : L.map all_types (elems $ _extends th)) 

newtype EventTable expr = EventTable { _table :: 
        BiGraph SkipOrEvent
            (AbstrEvent' expr) 
            (ConcrEvent' expr)}
    deriving (Eq,Default,NFData)

type Machine = Machine' Expr

type RawMachine = Machine' RawExpr

data Machine' expr = 
    Mch 
        { _machine'Name :: String
        , _theory     :: Theory
        , _variables  :: Map String Var
        , _abs_vars   :: Map String Var
        , _del_vars   :: Map String Var
        , _init_witness :: Map Var expr
        , _del_inits  :: Map Label expr
        , _inits      :: Map Label expr
        , _event_table :: EventTable expr
        , _inh_props  :: PropertySet' expr
        , _props      :: PropertySet' expr
        , _derivation :: Map Label Rule         
        , _comments   :: Map DocItem String }
    deriving (Eq,Show,Typeable,Functor,Foldable,Traversable,Generic)

data DocItem = 
        DocVar String 
        | DocEvent Label 
        | DocInv Label
        | DocProg Label
    deriving (Eq,Ord)

data Rule = forall r. RefRule r => Rule r
    deriving Typeable

class (Typeable a, Eq a, Show a, NFData a) => RefRule a where
    refinement_po :: a -> RawMachine -> POGen ()
    rule_name     :: a -> Label
    supporting_evts :: a -> [EventId]

instance Show expr => Show (EventTable expr) where
    show (EventTable m) = show m
instance Functor EventTable where
    fmap f (EventTable g) = EventTable $ mapBoth (fmap f) (fmap f) g
instance Foldable EventTable where
    foldMap f (EventTable m) = 
                foldMap (foldMap f) (leftMap m) 
            `mappend` foldMap (foldMap f) (rightMap m)
instance Traversable EventTable where
    traverse f (EventTable g) = EventTable <$> acrossBoth (traverse f) (traverse f) g 

instance Show DocItem where
    show (DocVar xs) = format "{0} (variable)" xs
    show (DocEvent xs) = format "{0} (event)" xs
    show (DocInv xs) = format "{0} (invariant)" xs
    show (DocProg xs) = format "{0} (progress)" xs

instance Show Rule where
    show (Rule x) = show x

instance Eq Rule where
    Rule x == Rule y = x `h_equal` y

instance RefRule Rule where
    refinement_po (Rule r) = refinement_po r
    rule_name (Rule r) = rule_name r
    supporting_evts (Rule r) = supporting_evts r

makeLenses ''EventTable
makeLenses ''Machine'
makeFields ''Machine'

-- downward :: Machine -> Label -> AbstrEvent -> EventSplitting
-- downward m lbl aevt = assert (sameExpr coarse_sched xs 
--                 && (L.null (L.drop 1 xs) || L.null (aevt^.c_sched_ref))) 
--             $ EvtS (lbl,aevt) cevts
--     where
--         xs    = L.map snd $ NE.toList cevts
--         cevts = NE.map (id &&& (conc_events m !)) (aevt^.ref_evts)

-- downward_events :: Machine -> Label -> EventSplitting
-- downward_events m lbl = downward m lbl aevt
--     where
--         aevt = abs_events m ! lbl

-- neList :: a -> [a] -> NonEmpty a
-- neList x xs = fromMaybe (x :| []) (nonEmpty xs)

all_refs :: Machine' expr -> [EventRef expr]
all_refs m = concat $ elems $ M.map (NE.toList . view evt_pairs) $ all_upwards m

-- sameExpr :: (Ord expr)
--          => Getting (Map Label expr) event (Map Label expr) 
--          -> [event]
--          -> Bool
-- sameExpr ln xs = L.null $ L.drop 1 $ L.groupBy eqAction xs
--     where
--         eqAction x y = acts x == acts y
--         acts x = L.sort (elems $ x^.ln)

conc_events :: Machine' expr -> Map SkipOrEvent (ConcrEvent' expr)
conc_events = M.map fst . backwardEdges . view events

-- upward :: Machine -> Label -> ConcrEvent -> EventMerging
-- upward m lbl cevt = EvtM aevts (lbl,cevt)
--     where
--         xs = L.map (id &&& (abs_events m !)) $ cevt^.abs_evts
--         -- aevts = assert (L.null $ L.drop 1 $ L.groupBy eqAction $ L.map snd xs) 
--         aevts = assert (sameExpr actions $ L.map snd xs) 
--                 $ neList (lbl,skip_abstr lbl) xs

upward_event :: Machine' expr -> SkipOrEvent -> EventMerging expr
upward_event m lbl = M.fromJust $ readGraph (m^.events) $ runMaybeT $ do
        v  <- MaybeT $ hasRightVertex lbl
        lift $ do
            es <- fmap source <$> predecessors v
            EvtM <$> T.forM es (\e -> (,) <$> leftKey e <*> leftInfo e)
                 <*> ((,) <$> rightKey v <*> rightInfo v)

--new_event_set :: Map String Var
--              -> Map Label Event
--              -> BiGraph Label AbstrEvent ConcrEvent
--new_event_set vs es = M.fromJust $ makeGraph $ do
--        skip <- newLeftVertex ":skip:" skip_abstr
--        forM_ (M.toList es) $ \(lbl,e) -> do
--            let f m = M.fromList $ L.map (id &&& Word) $ M.elems $ m `M.difference` vs
--            v <- newRightVertex lbl $ CEvent e (e^.actions.to frame.to f) M.empty
--            newEdge skip v

nonSkipUpwards :: Machine' expr -> Map EventId (EventMerging expr)
nonSkipUpwards m = readGraph (m^.events) $ do
        es <- getRightVertices
        ms <- forM es $ \e -> do
            es' <- fmap source <$> predecessors e
            k   <- rightKey e
            x   <- (EvtM <$> T.forM es' (\e -> (,) <$> leftKey e <*> leftInfo e)
                         <*> ((,) <$> rightKey e <*> rightInfo e))
            return $ either (const []) ((:[]).(,x)) k
        return $ M.fromList $ concat ms

nonSkipDownwards :: Machine' expr -> Map EventId (EventSplitting expr)
nonSkipDownwards m = readGraph (m^.events) $ do
        es <- getLeftVertices
        ms <- forM es $ \e -> do
            es' <- fmap target <$> successors e
            k   <- leftKey e
            x   <- (EvtS <$> ((,) <$> leftKey e <*> leftInfo e)
                         <*> T.forM es' (\e -> (,) <$> rightKey e <*> rightInfo e))
            return $ either (const []) ((:[]).(,x)) k
        return $ M.fromList $ concat ms

all_upwards :: Machine' expr -> Map SkipOrEvent (EventMerging expr)
all_upwards m = readGraph (m^.events) $ do
        es <- getRightVertices
        ms <- forM es $ \e -> do
            es' <- fmap source <$> predecessors e
            (,) <$> rightKey e
                <*> (EvtM <$> T.forM es' (\e -> (,) <$> leftKey e <*> leftInfo e)
                          <*> ((,) <$> rightKey e <*> rightInfo e))
        return $ M.fromList ms
    -- M.mapWithKey (upward m) (conc_events m)

all_downwards :: Machine' expr -> Map SkipOrEvent (EventSplitting expr)
all_downwards m = readGraph (m^.events) $ do
        es <- getLeftVertices
        ms <- forM es $ \e -> do
            es' <- fmap target <$> successors e
            (,) <$> leftKey e
                <*> (EvtS <$> ((,) <$> leftKey e <*> leftInfo e)
                          <*> T.forM es' (\e -> (,) <$> rightKey e <*> rightInfo e))
        return $ M.fromList ms
    -- M.mapWithKey (downward m) (abs_events m)

eventTable :: (forall s0 s1. GraphBuilder SkipOrEvent (AbstrEvent' expr) (ConcrEvent' expr) s0 s1 ())
           -> EventTable expr
eventTable gr = EventTable $ fromJust $ makeGraph $ do
    a <- newLeftVertex (Left SkipEvent) def
    c <- newRightVertex (Left SkipEvent) def
    newEdge a c
    gr

event :: EventId -> State (Event' expr) ()
      -> GraphBuilder SkipOrEvent (AbstrEvent' expr) (ConcrEvent' expr) s0 s1 ()
event eid cmd = do
    askip <- newLeftVertex (Left SkipEvent) def
    evt   <- newRightVertex (Right eid) $ def & new .~ execState cmd def
    newEdge askip evt

refined_event :: EventId -> State (EventRef expr) ()
              -> GraphBuilder SkipOrEvent (AbstrEvent' expr) (ConcrEvent' expr) s0 s1 ()
refined_event eid cmd = do
    let event = execState cmd $ EvtRef (eid',def) (eid',def)
        eid' = Right eid
    aevt <- newLeftVertex eid' $ event^.abstrEvent'
    cevt <- newRightVertex eid' $ event^.concrEvent'
    newEdge aevt cevt

newEvents :: [(EventId,Event' expr)]
          -> EventTable expr
newEvents xs = eventTable $ mapM_ (uncurry event . over _2 put) xs

variableSet :: Machine -> S.Set Var
variableSet m = S.fromList $ M.elems $ m^.variables

events :: Lens' (Machine' expr)
                (BiGraph SkipOrEvent 
                   (AbstrEvent' expr) 
                   (ConcrEvent' expr))
events = event_table . table

-- data Decomposition = Decomposition 
    
data System = Sys 
        {  proof_struct :: [(Label,Label)]
        ,  ref_struct   :: Map Label Label
        ,  expr_store   :: ExprStore
        ,  machines     :: Map String Machine
        ,  theories     :: Map String Theory
        }
    deriving Eq

empty_system :: System
empty_system = Sys [] M.empty empty_store 
        M.empty $ M.fromList 
            [ ("sets",set_theory)
            , ("functions",function_theory)
            , ("arithmetic",arithmetic)
            , ("basic",basic_theory)]

all_notation :: Machine -> Notation
all_notation m = flip precede logical_notation 
        $ L.foldl combine empty_notation 
        $ L.map (view Th.notation) th
    where
        th = (m^.theory) : elems (_extends $ m^.theory)

instance Named (Machine' expr) where
    decorated_name' = return . view name

_name :: Machine' expr -> Label
_name = label . view name

ba_predicate :: HasConcrEvent' event RawExpr
             => Machine' expr -> event -> Map Label RawExpr
ba_predicate m evt =          ba_predicate' (m^.variables) (evt^.new.actions)
                    `M.union` M.mapKeys (label . view name) (evt^.witness)

mkCons ''Machine'

empty_machine :: String -> Machine' expr
empty_machine n = genericDefault
                { _machine'Name = n }
            & theory .~ empty_theory { _extends = M.fromList [
                ("arithmetic",arithmetic), 
                ("basic", basic_theory)] } 
            -- & name

derive makeNFData ''DocItem
derive makeNFData ''Machine'
derive makeNFData ''Rule
derive makeNFData ''System

