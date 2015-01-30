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
import Data.Monoid
import Data.Map as M
import Data.List as L
import Data.Set as S

-- import Utilities.Error
-- import Utilities.Relation hiding ((!))
import Utilities.Syntactic

infixl 3 .>

data Phase0 = Phase0
        { _pAllMachines :: MTable ()
        , _pMachineId   :: MachineId }
    deriving Show

data Phase1 = Phase1 
    { _p0 :: Phase0
    , _pImports   :: Map String Theory
    , _pTypes     :: Map String Sort
    , _pAllTypes  :: Map String Sort
    , _pSetDecl   :: [(String, VarScope)]
    , _pEvents    :: Map Label EventId
    , _pNewEvents :: Map Label EventId
    }
    deriving Show

data Phase2 = Phase2
    { _p1 :: Phase1
    , _pDefinitions :: Map String Def
    , _pConstants :: Map String Var
    , _pStateVars :: Map String Var             -- machine variables
    , _pAbstractVars :: Map String Var          -- abstract machine variables
    , _pDummyVars :: Map String Var             -- dummy variables
    , _pIndices  :: Map EventId (Map String Var) -- event indices
    , _pParams   :: Map EventId (Map String Var)
    , _pNotation :: Notation
    , _pCtxSynt :: ParserSetting                  -- parsing assumptions
    , _pMchSynt :: ParserSetting                  -- parsing invariants and properties
    , _pSchSynt :: Map EventId ParserSetting    -- parsing schedule
    , _pEvtSynt :: Map EventId ParserSetting    -- parsing guards and actions
    }

data Phase3 = Phase3
    { _p2 :: Phase2
    , _pProgress :: Map ProgId ProgressProp
    , _pSafety :: Map Label SafetyProp
    , _pTransient :: Map Label Transient
    , _pAssumptions :: Map Label Expr
    , _pInvariant :: Map Label Expr                     -- Invariants
    , _pInit      :: Map Label Expr
    , _pCoarseSched :: Map EventId (Map Label Expr)     -- Schedules
    , _pFineSched   :: Map EventId (Map Label Expr)
    , _pOldGuards   :: Map EventId (Map Label Expr)
    , _pNewGuards   :: Map EventId (Map Label Expr)       -- Guards
    , _pOldActions  :: Map EventId (Map Label Action)    -- Actions
    , _pAllActions  :: Map EventId (Map Label Action)
    , _pOldPropSet  :: PropertySet
    , _pNewPropSet  :: PropertySet
    }

data Phase4 = Phase4
    { _p3 :: Phase3
    -- , _pEvtRef :: Abs EventId <-> Conc EventId
    -- , _pEvtRefProgA :: Abs EventId <-> Abs Label
    -- , _pEvtRefProgC :: Abs EventId <-> Conc Label
    -- , _pLiveProof   :: ProgId  <-> ProgId
    -- , _pLiveImplA   :: Abs Label  <-> Abs EventId
    -- , _pLiveImplC   :: Conc Label <-> Conc EventId
    , _pEventRefRule  :: Map EventId [(Label,ScheduleChange)]
    , _pLiveRule :: Map ProgId Rule
    , _pProofs   :: Map Label (Tactic Proof, LineInfo)
    , _pComments :: Map DocItem String
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
-- type Phase3I = Phase3 Identity

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

(.>) :: (Ord a, Monoid b) => Map a (b -> c) -> Map a b -> Map a c
(.>) mf mx = M.intersectionWith id mf (mx `M.union` my)
    where
        my = M.map (const mempty) mf

-- onMachine :: MachineId -> Lens' Phase2M Phase2I
-- onMachine = _

$(makeClassy ''Phase0)

$(makeClassy ''Phase1)

$(makeClassy ''Phase2)

$(makeClassy ''Phase3)

$(makeClassy ''Phase4)

type Getter' a b = (b -> Const b b) -> (a -> Const b a)

pGuards :: HasPhase3 phase => Getter phase (Map EventId (Map Label Expr))
pGuards f p = coerce $ f $ M.unionWith (M.unionWith $ error "pGuards: name clash") old new
    where
        old = L.view pOldGuards p
        new = L.view pNewGuards p

pSchedules :: HasPhase3 phase => Getter phase (Map EventId (Map Label Expr))       
pSchedules f p = coerce $ f $ M.unionWith (M.unionWith $ error "pSchedules: name clash") csch fsch
    where
        csch = L.view pCoarseSched p
        fsch = L.view pFineSched p

instance HasPhase0 Phase3 where
    phase0 = p0
    -- func = 

instance HasPhase1 Phase2 where
    phase1 = p1

instance HasPhase1 Phase3 where
    phase1 = p1

instance HasPhase1 Phase4 where
    phase1 = p1

instance HasPhase2 Phase3 where
    phase2 = p2

instance HasPhase2 Phase4 where
    phase2 = p2

instance HasPhase3 Phase4 where
    phase3 = p3

-- class HasPhase2 p MTable => HasPhase2M p where
-- instance HasPhase2M Phase2M where
-- instance HasPhase2M Phase3M where

-- class HasPhase2 p Identity => HasPhase2I p where
-- instance HasPhase2I Phase2I where
-- instance HasPhase2I Phase3I where

-- class HasPhase3 p MTable => HasPhase3M p where
-- instance HasPhase3M Phase3M where

-- class HasPhase3 p Identity => HasPhase3I p where
-- instance HasPhase3I Phase3I where

data Hierarchy k = Hierarchy 
        { order :: [k]
        , edges :: Map k k }
    deriving (Show)

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
