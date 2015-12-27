{-# LANGUAGE StandaloneDeriving,TypeFamilies
    , ConstraintKinds
    #-}
module Document.Phase.Types where

    -- Modules
import Document.Pipeline
import Document.Proof
import Document.Scope

import Logic.Operator (Notation)
import Logic.Proof
import Logic.Proof.Tactics (Tactic)

import UnitB.Expr 
import UnitB.Syntax as AST hiding (Constraint)

    -- Libraries
import Control.DeepSeq
import Control.Lens as L

import Data.Map   as M hiding ((!))
import Data.Typeable

import GHC.Generics (Generic)

import Utilities.BipartiteGraph as G hiding (fromList')
import Utilities.Syntactic
import Utilities.TableConstr
import Utilities.TH

class (MchType a (AEvtType a) (CEvtType a) (ThyType a) ~ a) 
        => IsMachine a where
    type MchType a :: * -> * -> * -> *
    type ThyType a :: *
    type AEvtType a :: *
    type CEvtType a :: *

data MachineP0 = MachineP0
        { _pAllMachines :: MTable ()
        , _pMachineId   :: MachineId }
    deriving (Show,Typeable,Generic,Eq)

type MachineP1 = MachineP1' EventP1 EventP1 TheoryP1

data MachineP1' ae ce thy = MachineP1 
    { _p0 :: MachineP0
    , _pEventRef :: G.BiGraph SkipOrEvent ae ce
    , _pContext  :: thy
    } deriving (Show,Typeable,Generic,Eq)

instance IsMachine (MachineP1' ae ce thy) where
    type MchType (MachineP1' ae ce thy) = MachineP1'
    type AEvtType (MachineP1' ae ce thy) = ae
    type CEvtType (MachineP1' ae ce thy) = ce
    type ThyType (MachineP1' ae ce thy) = thy

type MachineP2 = MachineP2' EventP2 EventP2 TheoryP2

data MachineP2' ae ce thy = MachineP2
    { _p1 :: MachineP1' ae ce thy
    , _pDelVars   :: Map Name (Var,LineInfo)
    , _pStateVars :: Map Name Var             -- machine variables
    , _pAbstractVars :: Map Name Var          -- abstract machine variables
    , _pMchSynt   :: ParserSetting                  -- parsing invariants and properties
    } deriving (Show,Typeable,Generic,Eq)

instance IsMachine (MachineP2' ae ce thy) where
    type MchType (MachineP2' ae ce thy) = MachineP2'
    type AEvtType (MachineP2' ae ce thy) = ae
    type CEvtType (MachineP2' ae ce thy) = ce
    type ThyType (MachineP2' ae ce thy) = thy

type MachineP3 = MachineP3' EventP3 EventP3 TheoryP3

data MachineP3' ae ce thy = MachineP3
    { _p2 :: MachineP2' ae ce thy
    , _pProgress  :: Map ProgId ProgressProp
    , _pSafety    :: Map Label SafetyProp
    , _pTransient :: Map Label Transient
    , _pInvariant   :: Map Label Expr                     -- Invariants
    , _pInitWitness :: Map Name (Var,Expr)
    , _pDelInits    :: Map Label Expr
    , _pInit        :: Map Label Expr
    , _pOldPropSet  :: PropertySet
    , _pNewPropSet  :: PropertySet
    } deriving (Show,Typeable,Generic,Eq)

instance IsMachine (MachineP3' ae ce thy) where
    type MchType (MachineP3' ae ce thy) = MachineP3'
    type AEvtType (MachineP3' ae ce thy) = ae
    type CEvtType (MachineP3' ae ce thy) = ce
    type ThyType (MachineP3' ae ce thy) = thy

type MachineP4 = MachineP4' EventP4 EventP3 TheoryP3

data MachineP4' ae ce thy = MachineP4
    { _p3 :: MachineP3' ae ce thy
    , _pLiveRule :: Map ProgId ProofTree
    , _pProofs   :: Map Label (Tactic Proof, LineInfo)
    , _pComments :: Map DocItem String
    } deriving (Show,Typeable,Generic)

instance (Eq ea,Eq ce,Eq thy) => Eq (MachineP4' ea ce thy) where
    x == y = all ($ (x,y)) 
            [ cmp _p3
            , cmp _pLiveRule
            , cmp _pComments 
            , cmp $ fmap snd . _pProofs ]
        where
            cmp f (x,y) = f x == f y

instance IsMachine (MachineP4' ae ce thy) where
    type MchType (MachineP4' ae ce thy) = MachineP4'
    type AEvtType (MachineP4' ae ce thy) = ae
    type CEvtType (MachineP4' ae ce thy) = ce
    type ThyType (MachineP4' ae ce thy) = thy

data EventP1 = EventP1
         { _eEventId :: SkipOrEvent
         }
    deriving (Show,Typeable,Generic,Eq)

data EventP2 = EventP2 
    { _e1 :: EventP1 
    , _eIndices :: Map Name Var
    , _eParams  :: Map Name Var
    , _eSchSynt :: ParserSetting
    , _eEvtSynt :: ParserSetting
    } deriving (Show,Typeable,Generic,Eq)

data EventP3 = EventP3 
    { _e2 :: EventP2 
    , _eCoarseSched :: Map Label Expr     
    , _eFineSched   :: Map Label Expr
    , _eGuards   :: Map Label Expr       
    , _eActions  :: Map Label Action
    , _eWitness     :: Map Name (Var,RawExpr)
    , _eIndWitness  :: Map Name (Var,RawExpr)
    } deriving (Show,Typeable,Generic,Eq)

data EventP4 = EventP4 
    { _e3 :: EventP3 
    , _eCoarseRef  :: [(Label,ScheduleChange)]
    , _eFineRef    :: Maybe (ProgId,ProgressProp)
    } deriving (Typeable,Show,Generic,Eq)

data Change = AddC | RemoveC
    deriving (Eq,Show)

data TheoryP0 = TheoryP0
    { _tNothing :: ()
    } deriving (Show,Typeable,Generic,Eq)

type PostponedDef = (Def,DeclSource,LineInfo)

data TheoryP1 = TheoryP1
    { _t0 :: TheoryP0
    , _pImports   :: Map Name Theory
    , _pTypes     :: Map Name Sort
    , _pAllTypes  :: Map Name Sort
    , _pSetDecl   :: [(Name, PostponedDef)]
    } deriving (Show,Typeable,Generic,Eq)

data TheoryP2 = TheoryP2
    { _t1 :: TheoryP1 
    , _pDefinitions :: Map Name Def
    , _pConstants :: Map Name Var
    , _pDummyVars :: Map Name Var             -- dummy variables
    , _pNotation  :: Notation
    , _pCtxSynt   :: ParserSetting                  -- parsing assumptions
    } deriving (Show,Typeable,Generic,Eq)

data TheoryP3 = TheoryP3
    { _t2 :: TheoryP2
    , _pAssumptions :: Map Label Expr
    } deriving (Show,Typeable,Generic,Eq)

data SystemP m = SystemP
    { _refineStruct :: Hierarchy MachineId
    , _mchTable :: MTable m }
    deriving (Typeable,Show,Generic,Eq)

instance NFData m => NFData (SystemP m) where
instance NFData m => NFData (Hierarchy m) where

type SystemP1 = SystemP MachineP1
type SystemP2 = SystemP MachineP2
type SystemP3 = SystemP MachineP3
type SystemP4 = SystemP MachineP4

  -- TODO: write contracts
data Hierarchy k = Hierarchy 
        { order :: [k]
        , edges :: Map k k }
    deriving (Show,Typeable,Generic)

instance Eq k => Eq (Hierarchy k) where
    h0 == h1 = edges h0 == edges h1

instance IsLabel ContextId where
    as_label (CId x) = label x

type MTable = Map MachineId
type CTable = Map ContextId

instance NFData MachineP0
instance (NFData ae,NFData ce,NFData thy) 
        => NFData (MachineP1' ae ce thy)
instance (NFData ae,NFData ce,NFData thy) 
        => NFData (MachineP2' ae ce thy)
instance (NFData ae,NFData ce,NFData thy) 
        => NFData (MachineP3' ae ce thy)
instance (NFData ae,NFData ce,NFData thy) 
        => NFData (MachineP4' ae ce thy)

instance NFData EventP1
instance NFData EventP2
instance NFData EventP3
instance NFData EventP4

instance NFData TheoryP0
instance NFData TheoryP1
instance NFData TheoryP2
instance NFData TheoryP3

instance NFData (Tactic Proof) where
    rnf x = seq x () 

makeRecordConstr ''MachineP2'
makeRecordConstr ''MachineP3'
makeRecordConstr ''MachineP4'

makeRecordConstr ''EventP2
makeRecordConstr ''EventP3
makeRecordConstr ''EventP4

makeRecordConstr ''TheoryP2
makeRecordConstr ''TheoryP3

makeLenses ''SystemP

createHierarchy 
        [ (''MachineP1' ,'_p0)
        , (''MachineP2' ,'_p1)
        , (''MachineP3' ,'_p2)
        , (''MachineP4' ,'_p3)
        -- , (''MachineBaseP1, '_pContext)
        , (''TheoryP1, '_t0)
        , (''TheoryP2, '_t1)
        , (''TheoryP3, '_t2)
        -- , (''MachineBaseP0 ,undefined)
        ]

createHierarchy
           --''EventP1
        [ (''EventP2, '_e1)
        , (''EventP3, '_e2)
        , (''EventP4, '_e3)
        ]

instance NFData EventP2Field
instance NFData EventP3Field
deriving instance Generic EventP2Field
deriving instance Generic EventP3Field
deriving instance Generic EventP4Field

deriving instance Show EventP3Field