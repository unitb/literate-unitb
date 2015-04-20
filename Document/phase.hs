{-# LANGUAGE MultiParamTypeClasses          #-}
{-# LANGUAGE TemplateHaskell                #-}
{-# LANGUAGE FunctionalDependencies         #-}
{-# LANGUAGE FlexibleInstances              #-}
{-# LANGUAGE FlexibleContexts               #-}
{-# LANGUAGE RankNTypes, GADTs              #-}
{-# LANGUAGE ScopedTypeVariables            #-}
{-# LANGUAGE TypeOperators,TypeFamilies     #-}
{-# LANGUAGE TupleSections,RecordWildCards  #-}
{-# LANGUAGE StandaloneDeriving             #-}
module Document.Phase where

    -- Modules
import Document.Pipeline
import Document.Proof
import Document.Scope
import Document.Visitor

import Latex.Parser

import Logic.Expr 
import Logic.Operator (Notation)
import Logic.Proof

import UnitB.AST

    -- Libraries
-- import Control.Applicative
import Control.Applicative
import Control.Arrow
import Control.Lens as L

import Control.Monad.Reader.Class 
import Control.Monad.State
import Control.Monad.Trans.Either
import Control.Monad.Trans.State  as ST
import Control.Monad.Trans.Reader as R hiding (local,ask)
import Control.Monad.Trans.RWS    as RWS hiding (local,ask)

-- import Data.Functor
-- import Data.Monoid
import Data.Map as M
import Data.Maybe as M
import Data.Monoid
import Data.List as L
import Data.Set as S

import Utilities.Error
-- import Utilities.Relation hiding ((!))
import Utilities.Syntactic
import Utilities.TH

infixl 3 <.>

-- type MachineP0 = MachineP0' ()

-- data MachineP0' a = MachineP0

trigger :: ( IsTuple a, Trigger (TypeList a)
           , TypeList (Tuple (RetType (TypeList a)))
                      ~ RetType (TypeList a)
           , IsTuple (Tuple (RetType (TypeList a))))
        => a -> Either [Error] (Tuple (RetType (TypeList a)))
trigger x = fromTuple `liftM` trigger' (toTuple x)

triggerM :: ( IsTuple a, Trigger (TypeList a)
            ,   TypeList (Tuple (RetType (TypeList a)))
              ~ RetType (TypeList a)
            , IsTuple (Tuple (RetType (TypeList a))))
         => a -> MM (Tuple (RetType (TypeList a)))
triggerM x = lift $ hoistEither $ trigger x

triggerP :: ( IsTuple a, Trigger (TypeList a)
            ,   TypeList (Tuple (RetType (TypeList a)))
              ~ RetType (TypeList a)
            , IsTuple (Tuple (RetType (TypeList a))))
         => Pipeline MM a (Tuple (RetType (TypeList a)))
triggerP = Pipeline empty_spec empty_spec triggerM

class Trigger a where
    type RetType a :: *
    trigger' :: a -> Either [Error] (RetType a)

instance Trigger () where
    type RetType () = ()
    trigger' () = return ()

instance Trigger as => Trigger (Either [Error] a :+: as) where
    type RetType (Either [Error] a :+: as) = a :+: RetType as
    trigger' (x :+: xs) = 
            case (x, trigger' xs) of
                (Right x, Right xs) -> Right (x:+:xs)
                (x,xs) -> Left $ f x ++ f xs
        where
            f (Left xs) = xs
            f (Right _) = []

instance Readable MachineId where
    read_one = do
        xs <- read_one
        return $ MId $ show (xs :: Label)
    read_args = do
        xs <- read_args
        return $ MId $ show (xs :: Label)

instance Readable ProgId where
    read_one  = liftM PId read_one
    read_args = liftM PId read_args
        
instance Readable (Maybe ProgId) where
    read_one  = liftM (fmap PId) read_one
    read_args = liftM (fmap PId) read_args

cmdSpec :: String -> Int -> DocSpec
cmdSpec cmd nargs = DocSpec M.empty (M.singleton cmd nargs)

envSpec :: String -> Int -> DocSpec
envSpec env nargs = DocSpec (M.singleton env nargs) M.empty

parseArgs :: (IsTuple a, AllReadable (TypeList a))
          => [[LatexDoc]]
          -> M a
parseArgs xs = do
    (x,[]) <- ST.runStateT read_all xs
    return $ fromTuple x

machineCmd :: forall result args ctx. 
              ( Monoid result, IsTuple args
              , IsTypeList  (TypeList args)
              , AllReadable (TypeList args))
           => String
           -> (args -> MachineId -> ctx -> M result) 
           -> Pipeline MM (MTable ctx) (Either [Error] (MTable result))
machineCmd cmd f = Pipeline m_spec empty_spec g
    where
        nargs = len ($myError :: TypeList args)
        m_spec = cmdSpec cmd nargs
        param = Collect 
            { getList = getCmd
            , tag = cmd
            , getInput = getMachineInput
            }
        g = collect param (cmdFun f)

-- type M' = RWS LineInfo [Error] System

cmdFun :: forall a b c d. 
              ( IsTuple b, Ord c
              , IsTypeList  (TypeList b)
              , AllReadable (TypeList b))
           => (b -> c -> d -> M a) 
           -> Cmd
           -> c -> (Map c d) -> M a
cmdFun f xs m ctx = local (const $ cmdLI xs) $ do
        x <- parseArgs (getCmdArgs xs)
        f x m (ctx ! m)

machineEnv :: forall result args ctx.
              ( Monoid result, IsTuple args
              , IsTypeList  (TypeList args)
              , AllReadable (TypeList args))
           => String
           -> (args -> [LatexDoc] -> MachineId -> ctx -> M result)
           -> Pipeline MM (MTable ctx) (Either [Error] (MTable result))
machineEnv env f = Pipeline m_spec empty_spec g
    where
        nargs = len ($myError :: TypeList args)
        m_spec = envSpec env nargs
        param = Collect 
            { getList = getEnv
            , tag = env
            , getInput = getMachineInput
            }
        g = collect param (envFun f)

envFun :: forall a b c d. 
              ( IsTuple b, Ord c
              , IsTypeList  (TypeList b)
              , AllReadable (TypeList b))
           => (b -> [LatexDoc] -> c -> d -> M a) 
           -> Env
           -> c -> (Map c d) -> M a
envFun f xs m ctx = local (const $ envLI xs) $ do
        x <- parseArgs (getEnvArgs xs)
        f x (getEnvContent xs) m (ctx ! m)

contextCmd :: forall a b c. 
              ( Monoid a, IsTuple b
              , IsTypeList  (TypeList b)
              , AllReadable (TypeList b))
           => String
           -> (b -> ContextId -> c -> M a) 
           -> Pipeline MM (CTable c) (Either [Error] (CTable a))
contextCmd cmd f = Pipeline empty_spec c_spec g
    where
        nargs = len ($myError :: TypeList b)
        c_spec = cmdSpec cmd nargs
        param = Collect 
            { getList = getCmd
            , tag = cmd
            , getInput = getContextInput
            }
        g = collect param (cmdFun f)

contextEnv :: forall result args ctx.
              ( Monoid result, IsTuple args
              , IsTypeList  (TypeList args)
              , AllReadable (TypeList args))
           => String
           -> (args -> [LatexDoc] -> ContextId -> ctx -> M result)
           -> Pipeline MM (CTable ctx) (Either [Error] (CTable result))
contextEnv env f = Pipeline empty_spec c_spec g
    where
        nargs = len ($myError :: TypeList args)
        c_spec = envSpec env nargs
        param = Collect 
            { getList = getEnv
            , tag = env
            , getInput = getContextInput
             }
        g = collect param (envFun f)

data Collect a b k t = Collect 
    { getList :: a -> Map k [b] 
    , getInput :: Input -> Map t a 
    -- , getContent :: b -> a
    , tag :: k }

collect :: (Ord k, Monoid z, Ord c)
        => Collect a b k c
        -> (b -> c -> d -> M z) 
        -> d
        -> MM (Either [Error] (Map c z))
collect p f arg = do
            cmp <- ask
            xs <- lift $ lift $ runEitherT $ toEither 
                $ forM (M.toList $ getInput p cmp) $ \(mname, x) -> do
                    xs <- forM (M.findWithDefault [] (tag p) $ getList p x) $ \e -> do
                        fromEither mempty $ f e mname arg 
                    return (mname, mconcat xs)
            return $ fmap (fromListWith mappend) xs

type MM = R.ReaderT Input M

type MachineP0' a = MachineP0

data MachineP0 = MachineP0
        { _pAllMachines :: MTable ()
        , _pMachineId   :: MachineId }
    deriving Show

type MachineP1 = MachineP1' EventP1 TheoryP1

data MachineP1' events theory = MachineP1 
    { _p0 :: MachineP0
    , _pEvents    :: Map EventId events
    , _pContext   :: theory
    -- , _machineP1'PEvents :: Map Label events
    -- , _pNewEvents :: Map Label EventId
    } deriving Show

type MachineP2 = MachineP2' EventP2 TheoryP2

data MachineP2' events theory = MachineP2
    { _p1 :: MachineP1' events theory
    , _pDelVars   :: Map String (Var,LineInfo)
    , _pStateVars :: Map String Var             -- machine variables
    , _pAbstractVars :: Map String Var          -- abstract machine variables
    , _pMchSynt   :: ParserSetting                  -- parsing invariants and properties
    } deriving Show


type MachineP3 = MachineP3' EventP3 TheoryP3

data MachineP3' events theory = MachineP3
    { _p2 :: MachineP2' events theory
    , _pProgress  :: Map ProgId ProgressProp
    , _pSafety    :: Map Label SafetyProp
    , _pTransient :: Map Label Transient
    , _pInvariant   :: Map Label Expr                     -- Invariants
    , _pInitWitness :: Map Var Expr
    , _pDelInits    :: Map Label Expr
    , _pInit        :: Map Label Expr
    , _pOldPropSet  :: PropertySet
    , _pNewPropSet  :: PropertySet
    } deriving Show

type MachineP4 = MachineP4' EventP4 TheoryP3

data MachineP4' events theory = MachineP4
    { _p3 :: MachineP3' events theory
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

data EventP1 = EventP1
        { _pEventId :: EventId
        , _pIsNew :: Bool }
    deriving Show

data EventP2 = EventP2 
    { _e1 :: EventP1 
    , _eIndices :: Map String Var
    , _eParams  :: Map String Var
    , _eSchSynt :: ParserSetting
    , _eEvtSynt :: ParserSetting
    } deriving Show

data EventP3 = EventP3 
    { _e2 :: EventP2 
    , _eCoarseSched :: Map Label Expr     -- Schedules
    , _eFineSched   :: Map Label Expr
    , _eOldGuards   :: Map Label Expr
    , _eNewGuards   :: Map Label Expr       -- Guards
    , _eWitness     :: Map Var Expr
    , _eOldActions  :: Map Label Action    -- Actions
    , _eDelActions  :: Map Label Action
    , _eNewActions  :: Map Label Action
    } deriving Show

data EventP4 = EventP4 
    { _e3 :: EventP3 
    , _eRefRule  :: [(Label,ScheduleChange)]
    , _eOldSched :: [(Label,Change)]
    }

data Change = AddC | RemoveC
    deriving (Eq,Show)

data TheoryP0 = TheoryP0
    { _tNothing :: ()
    }

type PostponedDef = (Def,DeclSource,LineInfo)

data TheoryP1 = TheoryP1
    { _t0 :: TheoryP0
    , _pImports   :: Map String Theory
    , _pTypes     :: Map String Sort
    , _pAllTypes  :: Map String Sort
    , _pSetDecl   :: [(String, PostponedDef)]
    }

data TheoryP2 = TheoryP2
    { _t1 :: TheoryP1 
    , _pDefinitions :: Map String Def
    , _pConstants :: Map String Var
    , _pDummyVars :: Map String Var             -- dummy variables
    , _pNotation  :: Notation
    , _pCtxSynt   :: ParserSetting                  -- parsing assumptions
    }

data TheoryP3 = TheoryP3
    { _t2 :: TheoryP2
    , _pAssumptions :: Map Label Expr
    }

newtype Abs a = Abs { getAbstract :: a }
    deriving (Eq,Ord)

newtype Conc a = Conc { getConcrete :: a }
    deriving (Eq,Ord)

class IsLabel a where
    as_label :: a -> Label

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
-- type Phase3I = MachineP3 Identity

    -- we want to encode phases as maps to 
    -- phase records and extract fields
    -- as maps to value
onMap :: Ord k => Lens' a b -> Lens' (Map k a) (Map k b)
onMap ln f ma = fmap (M.intersectionWith (flip $ set ln) ma) mb' -- write (_ $ read m) m
    where
        mb  = M.map (view ln) ma -- :: Map k b
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

(<.>) :: (Ord a) => Map a (b -> c) -> Map a b -> Map a c
(<.>) mf mx = M.intersectionWith id mf mx

-- onMachine :: MachineId -> Lens' Phase2M Phase2I
-- onMachine = _

$(makeClassy ''EventP1)

$(makeClassy ''EventP2)

$(makeClassy ''EventP3)

$(makeClassy ''EventP4)

createHierarchy 
        [ (''MachineP1' ,'_p0)
        , (''MachineP2' ,'_p1)
        , (''MachineP3' ,'_p2)
        , (''MachineP4' ,'_p3)
        -- , (''MachineP1', '_pContext)
        , (''TheoryP1, '_t0)
        , (''TheoryP2, '_t1)
        , (''TheoryP3, '_t2)
        -- , (''MachineP0' ,undefined)
        ]

$(makeHierarchy
           ''EventP1
        [ (''EventP2, 'e1)
        , (''EventP3, 'e2)
        , (''EventP4, 'e3)
        ] )

mkCons ''TheoryP2

mkCons ''MachineP2'

mkCons ''EventP2

mkCons ''TheoryP3

mkCons ''MachineP3'

mkCons ''EventP3

instance (HasMachineP1' m, HasTheoryP1 t) => HasTheoryP1 (m e t) where
    theoryP1 = pContext . theoryP1

instance (HasMachineP1' m, HasTheoryP2 t) => HasTheoryP2 (m e t) where
    theoryP2 = pContext . theoryP2

instance (HasMachineP1' m, HasTheoryP3 t) => HasTheoryP3 (m e t) where
    theoryP3 = pContext . theoryP3

pEventIds :: (HasEventP1 events, HasMachineP1' phase) 
          => Lens' (phase events t) (Map Label EventId)
pEventIds = pEvents . from pFromEventId . onMap pEventId

getEvent :: (HasMachineP1' phase)
      => EventId
      -> Lens' (phase events t) events
getEvent eid = pEvents . at eid . (\f x -> Just <$> f (M.fromJust x))

newDelVars :: HasMachineP2' phase
           => Getter (phase events t) (Map String Var)
newDelVars = to $ \x -> view pAbstractVars x `M.difference` view pStateVars x

eAddedGuards :: HasEventP3 events => Getter events (Map Label Expr)
eAddedGuards f p = coerce $ f $ M.difference new old
    where
        old = p ^. eOldGuards
        new = p ^. eNewGuards

pAddedGuards :: HasMachineP3 phase events => Getter (phase events t) (Map EventId (Map Label Expr))
pAddedGuards = pEvents . onMap' eAddedGuards

pSchedules :: HasMachineP3 phase events => Getter (phase events t) (Map EventId (Map Label Expr))       
pSchedules f p = coerce $ f $ M.unionWith (M.unionWith $ error "pSchedules: name clash") csch fsch
    where
        csch = L.view pCoarseSched p
        fsch = L.view pFineSched p

pFromEventId :: HasEventP1 event => Iso' (Map Label event) (Map EventId event)
pFromEventId = iso 
        (M.fromList . L.map (view pEventId &&& id) . M.elems) 
        (mapKeys as_label)

pIndices  :: HasMachineP2 mch event => Lens' (mch event t) (Map EventId (Map String Var))
pIndices = pEvents . onMap eIndices
pParams   :: HasMachineP2 mch event => Lens' (mch event t) (Map EventId (Map String Var))
pParams = pEvents . onMap eParams
pSchSynt  :: HasMachineP2 mch event => Lens' (mch event t) (Map EventId ParserSetting)    
    -- parsing schedule
pSchSynt = pEvents . onMap eSchSynt
pEvtSynt  :: HasMachineP2 mch event => Lens' (mch event t) (Map EventId ParserSetting)    
    -- parsing guards and actions
pEvtSynt = pEvents . onMap eEvtSynt

pCoarseSched :: HasMachineP3 mch event 
             => Lens' (mch event t) (Map EventId (Map Label Expr))     -- Schedules
pCoarseSched = pEvents . onMap eCoarseSched

pFineSched   :: HasMachineP3 mch event 
             => Lens' (mch event t) (Map EventId (Map Label Expr))
pFineSched = pEvents . onMap eFineSched

pOldGuards   :: HasMachineP3 mch event 
             => Lens' (mch event t) (Map EventId (Map Label Expr))
pOldGuards = pEvents . onMap eOldGuards

pNewGuards   :: HasMachineP3 mch event 
             => Lens' (mch event t) (Map EventId (Map Label Expr))       -- Guards
pNewGuards = pEvents . onMap eNewGuards

pOldActions  :: HasMachineP3 mch event 
             => Lens' (mch event t) (Map EventId (Map Label Action))    -- Actions
pOldActions = pEvents . onMap eOldActions

pDelActions  :: HasMachineP3 mch event 
             => Lens' (mch event t) (Map EventId (Map Label Action))
pDelActions = pEvents . onMap eDelActions

pNewActions  :: HasMachineP3 mch event 
             => Lens' (mch event t) (Map EventId (Map Label Action))
pNewActions = pEvents . onMap eNewActions

pEventRefRule :: HasMachineP4 mch event
              => Lens' (mch event t) (Map EventId [(Label,ScheduleChange)])
pEventRefRule = pEvents . onMap eRefRule

pWitness :: HasMachineP3 mch event 
         => Lens' (mch event t) (Map EventId (Map Var Expr))
pWitness = pEvents . onMap eWitness

-- asMap

-- instance HasMachineP0 MachineP3 where
--     machineP0 = p0
    -- func = 

-- class HasMachineP1 phase where
--     p1' :: phase events -> MachineP1' events

class (HasMachineP1' f, HasEventP1 a) => HasMachineP1 f a where

instance (HasMachineP1' f, HasEventP1 a) => HasMachineP1 f a where

class (HasMachineP2' f, HasEventP2 a, HasMachineP1 f a) => HasMachineP2 f a where

instance ( HasMachineP1' f, HasEventP1 a
         , HasMachineP2' f, HasEventP2 a) 
    => HasMachineP2 f a where

class (HasMachineP3' f, HasEventP3 a, HasMachineP2 f a) => HasMachineP3 f a where

instance ( HasMachineP1' f, HasEventP1 a
         , HasMachineP2' f, HasEventP2 a
         , HasMachineP3' f, HasEventP3 a) 
    => HasMachineP3 f a where

class ( HasMachineP4' f, HasEventP4 a
      , HasMachineP3 f a) => HasMachineP4 f a where

instance ( HasMachineP1' f, HasEventP1 a
         , HasMachineP2' f, HasEventP2 a
         , HasMachineP3' f, HasEventP3 a 
         , HasMachineP4' f, HasEventP4 a) 
    => HasMachineP4 f a where

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
