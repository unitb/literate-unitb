{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE RankNTypes, GADTs      #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeOperators          #-}
module Document.Phase where

    -- Modules
import Document.Proof
import Document.Scope

import Logic.Expr
import Logic.Operator (Notation)
import Logic.Proof

import UnitB.AST

    -- Libraries
-- import Control.Applicative
import Control.Arrow
import Control.Lens as L hiding (Action)

import Control.Monad.State

-- import Data.Functor
import Data.Map as M
import Data.List as L
import Data.Set as S

import Utilities.Error
-- import Utilities.Relation hiding ((!))
import Utilities.Syntactic
import Utilities.TH

infixl 3 .>

type MachinePh0' a = MachinePh0

data MachinePh0 = MachinePh0
        { _pAllMachines :: MTable ()
        , _pMachineId   :: MachineId }
    deriving Show

type MachinePh1 = MachinePh1' EventPh1

data MachinePh1' events = MachinePh1 
    { _p0 :: MachinePh0
    , _pImports   :: Map String Theory
    , _pTypes     :: Map String Sort
    , _pAllTypes  :: Map String Sort
    , _pSetDecl   :: [(String, VarScope)]
    , _pEvents    :: Map EventId events
    -- , _machinePh1'PEvents :: Map Label events
    -- , _pNewEvents :: Map Label EventId
    }
    deriving Show

type MachinePh2 = MachinePh2' EventPh2

data MachinePh2' events = MachinePh2
    { _p1 :: MachinePh1' events
    , _pDefinitions :: Map String Def
    , _pConstants :: Map String Var
    , _pStateVars :: Map String Var             -- machine variables
    , _pAbstractVars :: Map String Var          -- abstract machine variables
    , _pDummyVars :: Map String Var             -- dummy variables
    , _pNotation :: Notation
    , _pCtxSynt :: ParserSetting                  -- parsing assumptions
    , _pMchSynt :: ParserSetting                  -- parsing invariants and properties
    } deriving Show


type MachinePh3 = MachinePh3' EventPh3

data MachinePh3' events = MachinePh3
    { _p2 :: MachinePh2' events
    , _pProgress  :: Map ProgId ProgressProp
    , _pSafety    :: Map Label SafetyProp
    , _pTransient :: Map Label Transient
    , _pAssumptions :: Map Label Expr
    , _pInvariant   :: Map Label Expr                     -- Invariants
    , _pInit        :: Map Label Expr
    , _pOldPropSet  :: PropertySet
    , _pNewPropSet  :: PropertySet
    } deriving Show

type MachinePh4 = MachinePh4' EventPh4

data MachinePh4' events = MachinePh4
    { _p3 :: MachinePh3' events
    -- , _pEvtRef :: Abs EventId <-> Conc EventId
    -- , _pEvtRefProgA :: Abs EventId <-> Abs Label
    -- , _pEvtRefProgC :: Abs EventId <-> Conc Label
    -- , _pLiveProof   :: ProgId  <-> ProgId
    -- , _pLiveImplA   :: Abs Label  <-> Abs EventId
    -- , _pLiveImplC   :: Conc Label <-> Conc EventId
    , _pLiveRule :: Map ProgId Rule
    , _pProofs   :: Map Label (Tactic Proof, LineInfo)
    , _pComments :: Map DocItem String
    } 

data EventPh1 = EventPh1
        { _pEventId :: EventId
        , _pIsNew :: Bool }
    deriving Show

data EventPh2 = EventPh2 
    { _e1 :: EventPh1 
    , _eIndices :: Map String Var
    , _eParams  :: Map String Var
    , _eSchSynt :: ParserSetting
    , _eEvtSynt :: ParserSetting
    } deriving Show

data EventPh3 = EventPh3 
    { _e2 :: EventPh2 
    , _eCoarseSched :: Map Label Expr     -- Schedules
    , _eFineSched   :: Map Label Expr
    , _eOldGuards   :: Map Label Expr
    , _eNewGuards   :: Map Label Expr       -- Guards
    , _eOldActions  :: Map Label Action    -- Actions
    , _eAllActions  :: Map Label Action
    } deriving Show

data EventPh4 = EventPh4 
    { _e3 :: EventPh3 
    , _eRefRule  :: [(Label,ScheduleChange)]
    }

newtype Abs a = Abs { getAbstract :: a }
    deriving (Eq,Ord)

newtype Conc a = Conc { getConcrete :: a }
    deriving (Eq,Ord)

class IsLabel a where
    as_label :: a -> Label

newtype MachineId = MId { getMId :: String }
    deriving (Eq,Ord)

newtype ContextId = CId { getCId :: String }
    deriving (Eq,Ord)

instance Show MachineId where
    show = getMId

instance Show ContextId where
    show = getCId

instance IsLabel MachineId where
    as_label (MId x) = label x

instance IsLabel ContextId where
    as_label (CId x) = label x

instance IsLabel EventId where
    as_label (EventId lbl) = lbl

instance IsLabel ProgId where
    as_label (PId lbl) = lbl

type MTable = Map MachineId
type CTable = Map ContextId

-- type Phase2M = Phase2 MTable
-- type Phase3M = Phase3 MTable

-- type Phase2I = Phase2 Identity
-- type Phase3I = MachinePh3 Identity

    -- we want to encode phases as maps to 
    -- phase records and extract fields
    -- as maps to value
onMap :: forall a b k. Ord k => Lens' a b -> Lens' (Map k a) (Map k b)
onMap ln f ma = fmap (M.intersectionWith (flip $ set ln) ma) mb' -- write (_ $ read m) m
    where
        _ = set ln :: b -> a -> a
        _ = view ln :: a -> b
        mb  = M.map (view ln) ma :: Map k b
        mb' = f mb -- :: forall f. Applicative f => f (Map k b)

onMap' :: forall a b k. Ord k => Getting b a b -> Getter (Map k a) (Map k b)
onMap' ln = to $ M.map $ view ln

zoom :: Ord k => Set k -> Lens' (Map k a) (Map k a)
zoom s f m = fmap (M.union m1) $ f m0
    where
        (m0,m1) = M.partitionWithKey (const . (`S.member` s)) m

focus :: Lens' a b -> State b r -> State a r
focus ln cmd = StateT $ Identity . f 
    where
        f x = second (\y -> set ln y x) $ runState cmd (view ln x)

-- data ZipMap a b where
--     FMap :: (a -> b) -> ZipMap a b
--     Map :: Map a b -> ZipMap a b

-- instance Functor (ZipMap a) where
--     fmap f (Map m) = Map $ M.map f m
--     fmap f (FMap g) = FMap $ \x -> f $ g x

-- instance Ord a => Applicative (Map a) where
    -- pure = FMap . const
    -- (<*>) (FMap f) (FMap g) = FMap $ \x -> f x (g x)
    -- (<*>) (FMap f) (Map m)  = Map $ M.mapWithKey f m
    -- (<*>) (Map m)  (FMap f) = Map $ M.mapWithKey (\k g -> g $ f k) m
    -- (<*>) (Map m0) (Map m1) = Map $ M.intersectionWith id m0 m1

(.>) :: (Ord a) => Map a (b -> c) -> Map a b -> Map a c
(.>) mf mx = M.intersectionWith id mf mx

-- onMachine :: MachineId -> Lens' Phase2M Phase2I
-- onMachine = _

$(makeFields ''MachinePh1')

$(makeClassy ''MachinePh0)

$(makePolyClass ''MachinePh1')

-- $(makeClassy ''MachinePh1')


$(makePolyClass ''MachinePh2')

$(makePolyClass ''MachinePh3')

$(makePolyClass ''MachinePh4')

$(makeClassy ''EventPh1)

$(makeClassy ''EventPh2)

$(makeClassy ''EventPh3)

$(makeClassy ''EventPh4)

$(makeHierarchy 
           ''MachinePh1'
        [ (''MachinePh2' ,'p1)
        , (''MachinePh3' ,'p2)
        , (''MachinePh4' ,'p3)
        -- , (''MachinePh0' ,undefined)
        ] )

$(makeHierarchy
           ''EventPh1
        [ (''EventPh2, 'e1)
        , (''EventPh3, 'e2)
        , (''EventPh4, 'e3)
        ] )

pEventIds :: (HasEventPh1 events, HasMachinePh1' phase) 
          => Lens' (phase events) (Map Label EventId)
pEventIds = pEvents . from pFromEventId . onMap pEventId

type Getter' a b = (b -> Const b b) -> (a -> Const b a)

eGuards :: HasEventPh3 events => Getter events (Map Label Expr)
eGuards = to getter
    where
        getter p = (M.unionWith $ error "eGuards: name clash") old new
            where
                old = L.view eOldGuards p
                new = L.view eNewGuards p

pGuards :: HasMachinePh3 phase events => Getter (phase events) (Map EventId (Map Label Expr))
pGuards = pEvents . onMap' eGuards
        -- coerce $ f $ M.unionWith (M.unionWith $ error "pGuards: name clash") old new
    -- where
    --     old = L.view eOldGuards p
    --     new = L.view eNewGuards p

pSchedules :: HasMachinePh3 phase events => Getter (phase events) (Map EventId (Map Label Expr))       
pSchedules f p = coerce $ f $ M.unionWith (M.unionWith $ error "pSchedules: name clash") csch fsch
    where
        csch = L.view pCoarseSched p
        fsch = L.view pFineSched p

pFromEventId :: HasEventPh1 event => Iso' (Map Label event) (Map EventId event)
pFromEventId = iso 
        (M.fromList . L.map (view pEventId &&& id) . M.elems) 
        (mapKeys as_label)

pIndices  :: HasMachinePh2 mch event => Lens' (mch event) (Map EventId (Map String Var))
pIndices = pEvents . onMap eIndices
pParams   :: HasMachinePh2 mch event => Lens' (mch event) (Map EventId (Map String Var))
pParams = pEvents . onMap eParams
pSchSynt  :: HasMachinePh2 mch event => Lens' (mch event) (Map EventId ParserSetting)    
    -- parsing schedule
pSchSynt = pEvents . onMap eSchSynt
pEvtSynt  :: HasMachinePh2 mch event => Lens' (mch event) (Map EventId ParserSetting)    
    -- parsing guards and actions
pEvtSynt = pEvents . onMap eEvtSynt

pCoarseSched :: HasMachinePh3 mch event 
             => Lens' (mch event) (Map EventId (Map Label Expr))     -- Schedules
pCoarseSched = pEvents . onMap eCoarseSched

pFineSched   :: HasMachinePh3 mch event 
             => Lens' (mch event) (Map EventId (Map Label Expr))
pFineSched = pEvents . onMap eFineSched

pOldGuards   :: HasMachinePh3 mch event 
             => Lens' (mch event) (Map EventId (Map Label Expr))
pOldGuards = pEvents . onMap eOldGuards

pNewGuards   :: HasMachinePh3 mch event 
             => Lens' (mch event) (Map EventId (Map Label Expr))       -- Guards
pNewGuards = pEvents . onMap eNewGuards

pOldActions  :: HasMachinePh3 mch event 
             => Lens' (mch event) (Map EventId (Map Label Action))    -- Actions
pOldActions = pEvents . onMap eOldActions

pAllActions  :: HasMachinePh3 mch event 
             => Lens' (mch event) (Map EventId (Map Label Action))
pAllActions = pEvents . onMap eAllActions

pEventRefRule :: HasMachinePh4 mch event
              => Lens' (mch event) (Map EventId [(Label,ScheduleChange)])
pEventRefRule = pEvents . onMap eRefRule


-- asMap

-- instance HasMachinePh0 MachinePh3 where
--     machinePh0 = p0
    -- func = 

-- class HasMachinePh1 phase where
--     p1' :: phase events -> MachinePh1' events

class (HasMachinePh1' f, HasEventPh1 a) => HasMachinePh1 f a where

instance (HasMachinePh1' f, HasEventPh1 a) => HasMachinePh1 f a where

class (HasMachinePh2' f, HasEventPh2 a, HasMachinePh1 f a) => HasMachinePh2 f a where

instance ( HasMachinePh1' f, HasEventPh1 a
         , HasMachinePh2' f, HasEventPh2 a) 
    => HasMachinePh2 f a where

class (HasMachinePh3' f, HasEventPh3 a, HasMachinePh2 f a) => HasMachinePh3 f a where

instance ( HasMachinePh1' f, HasEventPh1 a
         , HasMachinePh2' f, HasEventPh2 a
         , HasMachinePh3' f, HasEventPh3 a) 
    => HasMachinePh3 f a where

class ( HasMachinePh4' f, HasEventPh4 a
      , HasMachinePh3 f a) => HasMachinePh4 f a where

instance ( HasMachinePh1' f, HasEventPh1 a
         , HasMachinePh2' f, HasEventPh2 a
         , HasMachinePh3' f, HasEventPh3 a 
         , HasMachinePh4' f, HasEventPh4 a) 
    => HasMachinePh4 f a where

instance HasMachinePh0 (MachinePh3' e) where
    machinePh0 = p0

    -- func = 











data Hierarchy k = Hierarchy 
        { order :: [k]
        , edges :: Map k k }
    deriving (Show)

aliases :: Eq b => Lens' a b -> Lens' a b -> Lens' a b
aliases ln0 ln1 = lens getter $ flip setter
    where
        getter z
            | x == y    = x
            | otherwise = $myError
            where
                x = view ln0 z
                y = view ln1 z
        setter x = set ln0 x . set ln1 x

inheritWith :: Ord k 
            => (base -> conc) 
            -> (conc -> abstr)
            -> (conc -> abstr -> conc)
            -> Hierarchy k 
            -> Map k base -> Map k conc
inheritWith decl inh (++) (Hierarchy xs es) m = L.foldl f (M.map decl m) xs
    where
        f m v = case v `M.lookup` es of 
                 Just u -> M.adjust (app $ m ! u) v m
                 Nothing -> m
        app ixs dxs = dxs ++ inh ixs
