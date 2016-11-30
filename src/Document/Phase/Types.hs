{-# LANGUAGE StandaloneDeriving,TypeFamilies
    , ConstraintKinds, RecordWildCards
    #-}
module Document.Phase.Types where

    -- Modules
import Document.Pipeline
import Document.Scope

import Logic.Expr.Parser (ParserSetting)
import Logic.Operator (Notation)
import Logic.Proof
import Logic.Proof.Tactics (Tactic)

import UnitB.Expr 
import UnitB.Syntax as AST hiding (Constraint)

    -- Libraries
import Control.DeepSeq
import Control.Lens as L
import Control.Lens.HierarchyTH

import Data.Graph.Bipartite as G hiding (fromList')
import Data.MakeTable
import Data.Map as M
import Data.Typeable

import GHC.Generics (Generic)

import Text.Pretty

import Utilities.Syntactic

class (MchType a (AEvtType a) (CEvtType a) (ThyType a) ~ a) 
        => IsMachine a where
    type DefType a :: *
    type MchType a :: * -> * -> * -> *
    type ThyType a :: *
    type AEvtType a :: *
    type CEvtType a :: *

data MachineP0 = MachineP0
        { _pAllMachines :: MMap ()
        , _pMachineId   :: MachineId }
    deriving (Show,Typeable,Generic,Eq)

type MachineP1 = MachineP1' EventP1 EventP1 TheoryP1

data MachineP1' ae ce thy = MachineP1 
    { _p0 :: MachineP0
    , _pEventRef :: G.BiGraph SkipOrEvent ae ce
    , _pContext  :: thy
    , _pVerTimeOut :: Float
    } deriving (Show,Typeable,Generic,Eq)

instance IsMachine (MachineP1' ae ce thy) where
    type DefType (MachineP1' ae ce thy) = ()
    type MchType (MachineP1' ae ce thy) = MachineP1'
    type AEvtType (MachineP1' ae ce thy) = ae
    type CEvtType (MachineP1' ae ce thy) = ce
    type ThyType (MachineP1' ae ce thy) = thy

type MachineP2  = MachineP2'' Expr EventP2 EventP2 TheoryP2
type MachineP2' = MachineP2'' Expr
type MachineP2RawDef  = MachineP2RawDef' EventP2 EventP2 TheoryP2
type MachineP2RawDef' = MachineP2'' StringLi

data MachineP2'' def ae ce thy = MachineP2
    { _p1 :: MachineP1' ae ce thy
    , _pMchOldDef :: M.Map Name def
    , _pMchDef    :: M.Map Name def
    , _pDelVars   :: M.Map Name (Var,LineInfo)
    , _pStateVars :: M.Map Name Var             -- machine variables
    , _pAbstractVars :: M.Map Name Var          -- abstract machine variables
    , _pMchSynt   :: ParserSetting                  -- parsing invariants and properties
    } deriving (Show,Typeable,Generic,Eq)

instance IsMachine (MachineP2'' def ae ce thy) where
    type DefType (MachineP2'' def ae ce thy) = def
    type MchType (MachineP2'' def ae ce thy) = MachineP2'' def
    type AEvtType (MachineP2'' def ae ce thy) = ae
    type CEvtType (MachineP2'' def ae ce thy) = ce
    type ThyType (MachineP2'' def ae ce thy) = thy

type MachineP3 = MachineP3' EventP3 EventP3 TheoryP3

data MachineP3' ae ce thy = MachineP3
    { _p2 :: MachineP2' ae ce thy
    , _pProgress  :: M.Map ProgId ProgressProp
    , _pSafety    :: M.Map Label SafetyProp
    , _pTransient :: M.Map Label Transient
    , _pInvariant   :: M.Map Label Expr                     -- Invariants
    , _pInitWitness :: M.Map Name Witness
    , _pDelInits    :: M.Map Label Expr
    , _pInit        :: M.Map Label Expr
    , _pOldPropSet  :: PropertySet
    , _pNewPropSet  :: PropertySet
    } deriving (Show,Typeable,Generic,Eq)

instance IsMachine (MachineP3' ae ce thy) where
    type DefType (MachineP3' ae ce thy) = Expr
    type MchType (MachineP3' ae ce thy) = MachineP3'
    type AEvtType (MachineP3' ae ce thy) = ae
    type CEvtType (MachineP3' ae ce thy) = ce
    type ThyType (MachineP3' ae ce thy) = thy

type MachineP4 = MachineP4' EventP4 EventP3 TheoryP3

data MachineP4' ae ce thy = MachineP4
    { _p3 :: MachineP3' ae ce thy
    , _pLiveRule :: M.Map ProgId ProofTree
    , _pProofs   :: M.Map Label (Tactic Proof, LineInfo)
    , _pComments :: M.Map DocItem String
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
    type DefType (MachineP4' ae ce thy) = Expr
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
    , _eIndices :: M.Map Name Var
    , _eDelIndices :: M.Map Name (Var,LineInfo)
    , _eParams  :: M.Map Name Var
    , _eSchSynt :: ParserSetting
    , _eEvtSynt :: ParserSetting
    } deriving (Show,Typeable,Generic,Eq)

data EventP3 = EventP3 
    { _e2 :: EventP2 
    , _eCoarseSched :: M.Map Label Expr     
    , _eFineSched   :: M.Map Label Expr
    , _eGuards   :: M.Map Label Expr       
    , _eActions  :: M.Map Label (NonEmpty LineInfo,Action)
    , _eWitness  :: M.Map Name Witness
    , _eParamWitness :: M.Map Name Witness
    , _eIndWitness   :: M.Map Name Witness
    } deriving (Show,Typeable,Generic,Eq)

data EventP4 = EventP4 
    { _e3 :: EventP3 
    , _eCoarseRef  :: [(Label,ScheduleChange)]
    , _eFineRef    :: Maybe (ProgId,ProgressProp)
    } deriving (Typeable,Show,Generic,Eq)

instance PrettyRecord EventP1 where
    recordFields = genericRecordFields []
instance PrettyPrintable EventP1 where
    pretty = prettyRecord

instance PrettyRecord EventP2 where
    recordFields r = genericRecordFields [[field|_e1|]] r
instance PrettyPrintable EventP2 where
    pretty = prettyRecord

data Change = AddC | RemoveC
    deriving (Eq,Show)

data TheoryP0 = TheoryP0
    { _tNothing :: ()
    } deriving (Show,Typeable,Generic,Eq)

type PostponedDef = (Def,DeclSource,LineInfo)

data TheoryP1 = TheoryP1
    { _t0 :: TheoryP0
    , _pImports   :: M.Map Name Theory
    , _pTypes     :: M.Map Name Sort
    , _pAllTypes  :: M.Map Name Sort
    , _pSetDecl   :: [(Name, PostponedDef)]
    } deriving (Show,Typeable,Generic,Eq)

data TheoryP2 = TheoryP2
    { _t1 :: TheoryP1 
    , _pDefinitions :: M.Map Name Def
    , _pConstants :: M.Map Name Var
    , _pDummyVars :: M.Map Name Var             -- dummy variables
    , _pNotation  :: Notation
    , _pCtxSynt   :: ParserSetting                  -- parsing assumptions
    } deriving (Show,Typeable,Generic,Eq)

data TheoryP3 = TheoryP3
    { _t2 :: TheoryP2
    , _pAssumptions :: M.Map Label Expr
    } deriving (Show,Typeable,Generic,Eq)

data SystemP m = SystemP
    { _refineStruct :: Hierarchy MachineId
    , _mchMap :: MMap m }
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
        , edges :: M.Map k k }
    deriving (Show,Typeable,Generic)

instance Eq k => Eq (Hierarchy k) where
    h0 == h1 = edges h0 == edges h1

type MMap = M.Map MachineId
type CMap = M.Map ContextId

instance NFData MachineP0
instance (NFData ae,NFData ce,NFData thy) 
        => NFData (MachineP1' ae ce thy)
instance (NFData def,NFData ae,NFData ce,NFData thy) 
        => NFData (MachineP2'' def ae ce thy)
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

makeRecordConstr ''MachineP2''
makeRecordConstr ''MachineP3'
makeRecordConstr ''MachineP4'

makeRecordConstr ''EventP2
makeRecordConstr ''EventP3
makeRecordConstr ''EventP4

makeRecordConstr ''TheoryP2
makeRecordConstr ''TheoryP3

instance PrettyPrintable EventP2Field where
    pretty = prettyADT

type MachineP2'Field = MachineP2''Field StringLi

makeLenses ''SystemP

class HasMachineP2' (mch :: * -> * -> * -> *) where
    machineP2' :: -- IsMachine (mch ae0 ce0 thy0)
                Lens (mch ae0 ce0 thy0) (mch ae1 ce1 thy1) 
                       (MachineP2'' (DefType (mch ae0 ce0 thy0)) ae0 ce0 thy0)
                       (MachineP2'' (DefType (mch ae0 ce0 thy0)) ae1 ce1 thy1)

p1 :: HasMachineP2' mch 
   => Lens (mch ae0 ce0 thy0) 
           (mch ae1 ce1 thy1) 
           (MachineP1' ae0 ce0 thy0)
           (MachineP1' ae1 ce1 thy1)
p1 = machineP2' . lens _p1 (\p2 x -> p2 { _p1 = x })

pDelVars   :: HasMachineP2' mch 
           => Lens' (mch ae ce thy) 
                    (Map Name (Var,LineInfo)) 
pDelVars = machineP2' . $(oneLens '_pDelVars)
pDefs  :: Traversal (MachineP2'' def ae ce thy) 
                    (MachineP2'' def' ae ce thy) 
                    (Map Name def)
                    (Map Name def')
pDefs = (\f (MachineP2 { .. }) -> 
               (\x' y' -> MachineP2 _p1 x' y' _pDelVars _pStateVars 
                                 _pAbstractVars _pMchSynt) 
                    <$> f _pMchOldDef <*> f _pMchDef)
pMchDef    :: HasMachineP2' mch 
           => Lens (mch ae ce thy) 
                   (mch ae ce thy) 
                   (Map Name (DefType (mch ae ce thy)))
                   (Map Name (DefType (mch ae ce thy)))
pMchDef = machineP2' . $(oneLens '_pMchDef)
pMchOldDef :: HasMachineP2' mch 
           => Lens (mch ae ce thy) 
                   (mch ae ce thy) 
                   (Map Name (DefType (mch ae ce thy)))
                   (Map Name (DefType (mch ae ce thy)))
pMchOldDef = machineP2' . $(oneLens '_pMchOldDef)
pStateVars :: HasMachineP2' mch 
           => Lens' (mch ae ce thy) 
                    (Map Name Var)
pStateVars = machineP2' . $(oneLens '_pStateVars)
pAbstractVars :: HasMachineP2' mch 
           => Lens' (mch ae ce thy) 
                    (Map Name Var)
pAbstractVars = machineP2' . $(oneLens '_pAbstractVars)
pMchSynt   :: HasMachineP2' mch 
           => Lens' (mch ae ce thy) 
                    ParserSetting 
pMchSynt = machineP2' . $(oneLens '_pMchSynt)

createHierarchy 
        [ (''MachineP1'  ,'_p0)
        , (''MachineP2'  ,'_p1)
        , (''MachineP3'  ,'_p2)
        , (''MachineP4'  ,'_p3)
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

instance HasMachineP1' MachineP2RawDef' where
    machineP1' = $(oneLens '_p1)
instance HasMachineP2' MachineP2RawDef' where
    machineP2' = id
