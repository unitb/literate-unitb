{-# LANGUAGE DeriveDataTypeable
    , ExistentialQuantification
    , TemplateHaskell
    , OverloadedStrings
    #-} 
module UnitB.AST 
    ( Theory  (..)
    , Machine (..)
    , conc_events
    , variableSet
    , empty_machine
    , empty_theory
    , inv_thm, inv, proofs
    , progress, safety
    , transient, constraint
    , Rule (..)
    , RefRule (..)
    , all_upwards, all_downwards
    , upward_event
    , new_event_set
    , all_refs
    , all_types
    , basic_theory
    , disjoint_union
    , cycles
    , System (..)
    , empty_system
    , all_notation
    , ba_predicate
    , th_notation
    , DocItem (..)
    , module UnitB.Event
    , module UnitB.Property
    ) 
where
 
    -- Modules
import Logic.Expr hiding (merge,target)
import Logic.ExpressionStore (ExprStore, empty_store)
import Logic.Operator
import Logic.Proof.POGenerator ( POGen )
import Logic.Theory as Th hiding (assert)

import Theories.SetTheory
import Theories.FunctionTheory
import Theories.Arithmetic

import UnitB.Event
import UnitB.Property

    -- Libraries
import Control.Applicative
import Control.Arrow
import Control.DeepSeq
import Control.Lens

import Control.Monad hiding ( guard )
import Control.Monad.Trans.Maybe
import Control.Monad.Writer hiding ( guard )

import           Data.DeriveTH
import           Data.List as L hiding ( union, inits )
import           Data.List.NonEmpty as NE
import           Data.Map as M
import           Data.Maybe as M
import qualified Data.Set as S
import qualified Data.Traversable as T
import           Data.Typeable

import Utilities.BipartiteGraph
import Utilities.Format
import Utilities.Graph  (cycles)
import Utilities.HeterogenousEquality
import Utilities.TH

all_types :: Theory -> Map String Sort
all_types th = unions (types th : L.map all_types (elems $ extends th)) 

instance Show ProgId where
    show (PId x) = show x

data Machine = 
    Mch 
        { _name      :: Label
        , theory     :: Theory
        , variables  :: Map String Var
        , abs_vars   :: Map String Var
        , del_vars   :: Map String Var
        , init_witness :: Map Var Expr
        , del_inits  :: Map Label Expr
        , inits      :: Map Label Expr
        , events     :: BiGraph Label AbstrEvent ConcrEvent
        , inh_props  :: PropertySet
        , props      :: PropertySet
        , derivation :: Map Label Rule         
        , comments   :: Map DocItem String }
    deriving (Eq, Show, Typeable)

variableSet :: Machine -> S.Set Var
variableSet m = S.fromList $ M.elems $ variables m




all_refs :: Machine -> [EventRef]
all_refs m = concat $ elems $ M.map (NE.toList . view evt_pairs) $ all_upwards m

conc_events :: Machine -> Map Label ConcrEvent
conc_events = M.map fst . backwardEdges . events

upward_event :: Machine -> Label -> EventMerging
upward_event m lbl = M.fromJust $ readGraph (events m) $ runMaybeT $ do
        v  <- MaybeT $ hasRightVertex lbl
        lift $ do
            es <- fmap source <$> predecessors v
            EvtM <$> T.forM es (\e -> (,) <$> leftKey e <*> leftInfo e)
                 <*> ((,) <$> rightKey v <*> rightInfo v)

new_event_set :: Map String Var
              -> Map Label Event
              -> BiGraph Label AbstrEvent ConcrEvent
new_event_set vs es = M.fromJust $ makeGraph $ do
        skip <- newLeftVertex ":skip:" skip_abstr
        forM_ (M.toList es) $ \(lbl,e) -> do
            let f m = M.fromList $ L.map (id &&& Word) $ M.elems $ m `M.difference` vs
            v <- newRightVertex lbl $ CEvent e (e^.actions.to frame.to f) M.empty
            newEdge skip v

all_upwards :: Machine -> Map Label EventMerging
all_upwards m = readGraph (events m) $ do
        es <- getRightVertices
        ms <- forM es $ \e -> do
            es' <- fmap source <$> predecessors e
            (,) <$> rightKey e
                <*> (EvtM <$> T.forM es' (\e -> (,) <$> leftKey e <*> leftInfo e)
                          <*> ((,) <$> rightKey e <*> rightInfo e))
        return $ M.fromList ms

all_downwards :: Machine -> Map Label EventSplitting
all_downwards m = readGraph (events m) $ do
        es <- getLeftVertices
        ms <- forM es $ \e -> do
            es' <- fmap target <$> successors e
            (,) <$> leftKey e
                <*> (EvtS <$> ((,) <$> leftKey e <*> leftInfo e)
                          <*> T.forM es' (\e -> (,) <$> rightKey e <*> rightInfo e))
        return $ M.fromList ms

data DocItem = 
        DocVar String 
        | DocEvent Label 
        | DocInv Label
        | DocProg Label
    deriving (Eq,Ord)

instance Show DocItem where
    show (DocVar xs) = format "{0} (variable)" xs
    show (DocEvent xs) = format "{0} (event)" xs
    show (DocInv xs) = format "{0} (invariant)" xs
    show (DocProg xs) = format "{0} (progress)" xs

-- data Decomposition = Decomposition 
    
class (Typeable a, Eq a, Show a, NFData a) => RefRule a where
    refinement_po :: a -> Machine -> POGen ()
    rule_name     :: a -> Label
    supporting_evts :: a -> [EventId]

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
        $ L.map Th.notation th
    where
        th = theory m : elems (extends $ theory m)

toEither :: (Eq a, Monoid a) => Writer a b -> Either a b
toEither m
        | w == mempty   = Right x
        | otherwise     = Left w
    where
        (x,w) = runWriter m


disjoint_union :: (Monoid c, Eq c, Ord a) => (a -> c) -> Map a b -> Map a b -> Either c (Map a b)
disjoint_union f x y = do
        toEither $ forM_ zs $ \z ->
            tell $ f z
        return (x `union` y)
    where
        zs = S.toList (keysSet x `S.intersection` keysSet y)

instance Named Machine where
    name m = case _name m of Lbl s -> s
    decorated_name' = return . name

data Rule = forall r. RefRule r => Rule r
    deriving Typeable

instance Show Rule where
    show (Rule x) = show x

instance Eq Rule where
    Rule x == Rule y = x `h_equal` y


instance RefRule Rule where
    refinement_po (Rule r) = refinement_po r
    rule_name (Rule r) = rule_name r
    supporting_evts (Rule r) = supporting_evts r

ba_predicate :: HasConcrEvent event 
             => Machine -> event -> Map Label Expr
ba_predicate m evt =          ba_predicate' (variables m) (evt^.new.actions)
                    `M.union` M.mapKeys (label . name) (evt^.witness)

mkCons ''Machine

empty_machine :: String -> Machine
empty_machine n = makeMachine (label n) 
            empty_theory { extends = M.fromList [
                ("arithmetic",arithmetic), 
                ("basic", basic_theory)] }

makeLenses ''PropertySet

derive makeNFData ''DocItem
derive makeNFData ''Machine
derive makeNFData ''Rule
derive makeNFData ''System

