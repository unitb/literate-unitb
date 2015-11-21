{-# LANGUAGE Arrows                         #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE ScopedTypeVariables            #-}
{-# LANGUAGE TypeOperators,TypeFamilies     #-}
{-# LANGUAGE RecordWildCards  #-}
{-# LANGUAGE StandaloneDeriving             #-}
module Document.Phase where

    -- Modules
import Document.Pipeline
import Document.Phase.Parameters
import Document.Proof
import Document.Scope

import Latex.Parser

import Logic.Operator (Notation)
import Logic.Proof
import Logic.Proof.Tactics (Tactic)

import UnitB.AST as AST
import UnitB.Expr 

    -- Libraries
import Control.Arrow hiding (ArrowChoice(..))
import Control.DeepSeq
import Control.Lens as L

import Control.Monad.Reader.Class 
import Control.Monad.Reader (Reader,runReader) 
import Control.Monad.RWS (runRWS)
import Control.Monad.State
import Control.Monad.Trans.Either
import Control.Monad.Writer.Class 

import Data.Default
import Data.Either
import Data.Either.Combinators
import Data.List as L
import Data.List.NonEmpty as NE
import Data.Map   as M hiding ((!))
import Data.Maybe as MM
import Data.Proxy
import Data.Semigroup
import Data.Set as S
import qualified Data.Traversable as T
import Data.Typeable

import GHC.Generics (Generic)

import Test.QuickCheck as QC hiding (label,collect)

import Utilities.BipartiteGraph as G hiding (fromList')
import Utilities.Graph (cycles,SCC(..))
import Utilities.Error
import Utilities.Partial
import Utilities.Syntactic
import Utilities.Format
import Utilities.TableConstr
import Utilities.TH
import Utilities.Tuple.Generics

triggerM :: Maybe a -> MM' c a
triggerM = maybe mzero return

triggerP :: Pipeline MM (Maybe a) a
triggerP = Pipeline empty_spec empty_spec triggerM

cmdSpec :: String -> Int -> DocSpec
cmdSpec cmd nargs = DocSpec M.empty (M.singleton cmd nargs)

envSpec :: String -> Int -> DocSpec
envSpec env nargs = DocSpec (M.singleton env nargs) M.empty

read_all :: (IsTuple LatexArg a, Monad m)
         => StateT ([LatexDoc],LineInfo) (EitherT [Error] m) a
read_all = do
    let p = Proxy :: Proxy LatexArg
        read_one' :: forall b m. (LatexArg b, Monad m) 
                  => StateT ([LatexDoc],LineInfo) (EitherT [Error] m) b
        read_one' = do
            (xs,li) <- get
            case xs of
              (x:xs) -> put (xs,after x) >> lift (hoistEither $ read_one x)
              []     -> lift $ left [Error "expecting more arguments" li]
    makeTuple' p read_one'

parseArgs :: (IsTuple LatexArg a)
          => Assert 
          -> ([LatexDoc], LineInfo)
          -> M a
parseArgs arse xs = do
    (x,(xs,_)) <- runStateT read_all xs
    return $ byPred arse "null remainder" L.null xs x

machineCmd :: forall result args ctx. 
              ( Monoid result
              , IsTuple LatexArg args )
           => String
           -> (args -> MachineId -> ctx -> M result) 
           -> Pipeline MM (MTable ctx) (Maybe (MTable result))
machineCmd cmd f = Pipeline m_spec empty_spec g
    where
        nargs = len (Proxy :: Proxy LatexArg) (Proxy :: Proxy args)
        m_spec = cmdSpec cmd nargs
        param = Collect 
            { getList = getCmd
            , tag = cmd
            , getInput = getMachineInput
            }
        g = collect param (cmdFun f)

-- type M' = RWS LineInfo [Error] System

cmdFun :: forall a b c d. 
              ( IsTuple LatexArg b
              , Ord c )
           => (b -> c -> d -> M a) 
           -> Cmd
           -> c -> (Map c d) -> MM (Maybe a)
cmdFun f xs m ctx = case x of
                      Right x -> tell w >> return (Just x)
                      Left es -> tell (w ++ es) >> return Nothing
    where
        (x,(),w) = runRWS (runEitherT $ do
                        x <- parseArgs assert (getCmdArgs xs)
                        f x m (ctx ! m) )
                    (cmdLI xs) 
                    ()

machineEnv :: forall result args ctx.
              ( Monoid result, IsTuple LatexArg args )
           => String
           -> (args -> LatexDoc -> MachineId -> ctx -> M result)
           -> Pipeline MM (MTable ctx) (Maybe (MTable result))
machineEnv env f = Pipeline m_spec empty_spec g
    where
        nargs = len (Proxy :: Proxy LatexArg) (Proxy :: Proxy args)
        m_spec = envSpec env nargs
        param = Collect 
            { getList = getEnv
            , tag = env
            , getInput = getMachineInput
            }
        g = collect param (envFun f)

envFun :: forall a b c d. 
              ( IsTuple LatexArg b, Ord c )
           => (b -> LatexDoc -> c -> d -> M a) 
           -> Env
           -> c -> (Map c d) -> MM (Maybe a)
envFun f xs m ctx = case x of
                      Right x -> tell w >> return (Just x)
                      Left es -> tell (w ++ es) >> return Nothing
    where
        (x,(),w) = runRWS (runEitherT $ do
                        x <- parseArgs assert (getEnvArgs xs)
                        f x (getEnvContent xs) m (ctx ! m))
                    (envLI xs) 
                    ()

contextCmd :: forall a b c. 
              ( Monoid a, IsTuple LatexArg b )
           => String
           -> (b -> ContextId -> c -> M a) 
           -> Pipeline MM (CTable c) (Maybe (CTable a))
contextCmd cmd f = Pipeline empty_spec c_spec g
    where
        nargs = len (Proxy :: Proxy LatexArg) (Proxy :: Proxy b)
        c_spec = cmdSpec cmd nargs
        param = Collect 
            { getList = getCmd
            , tag = cmd
            , getInput = getContextInput
            }
        g = collect param (cmdFun f)

contextEnv :: forall result args ctx.
              ( Monoid result, IsTuple LatexArg args )
           => String
           -> (args -> LatexDoc -> ContextId -> ctx -> M result)
           -> Pipeline MM (CTable ctx) (Maybe (CTable result))
contextEnv env f = Pipeline empty_spec c_spec g
    where
        nargs = len (Proxy :: Proxy LatexArg) (Proxy :: Proxy args)
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

collect :: (Ord k, Monoid z, Ord c, Show c)
        => Collect a b k c
        -> (b -> c -> d -> MM (Maybe z)) 
        -> d
        -> MM (Maybe (Map c z))
collect p f arg = do
            cmp <- ask
            xs <- forM (M.toList $ getInput p cmp) $ \(mname, x) -> do
                    xs <- forM (M.findWithDefault [] (tag p) $ getList p x) $ \e -> do
                        f e mname arg 
                    return (mname, mconcat <$> sequence xs)
            return $  fromListWith mappend 
                  <$> mapM (runKleisli $ second $ Kleisli id) xs

type MachineP0' a = MachineP0

data MachineP0 = MachineP0
        { _pAllMachines :: MTable ()
        , _pMachineId   :: MachineId }
    deriving (Show,Typeable,Generic)

type MachineP1 = MachineP1' EventP1 TheoryP1

data MachineP1' events theory = MachineP1 
    { _p0 :: MachineP0
    , _pEventRef :: G.BiGraph SkipOrEvent events events
    , _pContext  :: theory
    } deriving (Show,Typeable,Generic)

type MachineP2 = MachineP2' EventP2 TheoryP2

data MachineP2' events theory = MachineP2
    { _p1 :: MachineP1' events theory
    , _pDelVars   :: Map String (Var,LineInfo)
    , _pStateVars :: Map String Var             -- machine variables
    , _pAbstractVars :: Map String Var          -- abstract machine variables
    , _pMchSynt   :: ParserSetting                  -- parsing invariants and properties
    } deriving (Show,Typeable,Generic)

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
    } deriving (Show,Typeable,Generic)

type MachineP4 = MachineP4' EventP4 TheoryP3

data MachineP4' events theory = MachineP4
    { _p3 :: MachineP3' events theory
    , _pLiveRule :: Map ProgId ProofTree
    , _pProofs   :: Map Label (Tactic Proof, LineInfo)
    , _pComments :: Map DocItem String
    } deriving (Typeable,Show,Generic)

data EventP1 = EventP1
         { _eEventId :: SkipOrEvent
         }
    deriving (Show,Typeable,Generic)

data EventP2 = EventP2 
    { _e1 :: EventP1 
    , _eIndices :: Map String Var
    , _eParams  :: Map String Var
    , _eSchSynt :: ParserSetting
    , _eEvtSynt :: ParserSetting
    } deriving (Show,Typeable,Generic)

data EventP3 = EventP3 
    { _e2 :: EventP2 
    , _eCoarseSched :: Map Label Expr     
    , _eFineSched   :: Map Label Expr
    , _eGuards   :: Map Label Expr       
    , _eWitness     :: Map Var RawExpr
    , _eActions  :: Map Label Action
    } deriving (Show,Typeable,Generic)

data EventP4 = EventP4 
    { _e3 :: EventP3 
    , _eCoarseRef  :: [(Label,ScheduleChange)]
    , _eFineRef    :: Maybe (ProgId,ProgressProp)
    } deriving (Typeable,Show,Generic)

data Change = AddC | RemoveC
    deriving (Eq,Show)

data TheoryP0 = TheoryP0
    { _tNothing :: ()
    } deriving (Show,Typeable,Generic)

type PostponedDef = (Def,DeclSource,LineInfo)

data TheoryP1 = TheoryP1
    { _t0 :: TheoryP0
    , _pImports   :: Map String Theory
    , _pTypes     :: Map String Sort
    , _pAllTypes  :: Map String Sort
    , _pSetDecl   :: [(String, PostponedDef)]
    } deriving (Show,Typeable,Generic)

data TheoryP2 = TheoryP2
    { _t1 :: TheoryP1 
    , _pDefinitions :: Map String Def
    , _pConstants :: Map String Var
    , _pDummyVars :: Map String Var             -- dummy variables
    , _pNotation  :: Notation
    , _pCtxSynt   :: ParserSetting                  -- parsing assumptions
    } deriving (Show,Typeable,Generic)

data TheoryP3 = TheoryP3
    { _t2 :: TheoryP2
    , _pAssumptions :: Map Label Expr
    } deriving (Show,Typeable,Generic)

data SystemP m = SystemP
    { _refineStruct :: Hierarchy MachineId
    , _mchTable :: MTable m }
    deriving (Typeable,Show,Generic)

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

instance IsLabel ContextId where
    as_label (CId x) = label x

type MTable = Map MachineId
type CTable = Map ContextId

instance NFData MachineP0
instance (NFData e,NFData t) => NFData (MachineP1' e t)
instance (NFData e,NFData t) => NFData (MachineP2' e t)
instance (NFData e,NFData t) => NFData (MachineP3' e t)
instance (NFData e,NFData t) => NFData (MachineP4' e t)

instance NFData EventP1
instance NFData EventP2
instance NFData EventP3
instance NFData EventP4

instance NFData TheoryP0
instance NFData TheoryP1
instance NFData TheoryP2
instance NFData TheoryP3

makeRecordConstr ''MachineP2'
makeRecordConstr ''MachineP3'
makeRecordConstr ''MachineP4'

makeRecordConstr ''EventP2
makeRecordConstr ''EventP3
makeRecordConstr ''EventP4

makeRecordConstr ''TheoryP2
makeRecordConstr ''TheoryP3
--makeRecordConstr ''TheoryP4

instance NFData EventP2Field
instance NFData EventP3Field
deriving instance Generic EventP2Field
deriving instance Generic EventP3Field
deriving instance Generic EventP4Field

makeLenses ''SystemP

deriving instance Show EventP3Field

instance NFData (Tactic Proof) where
    rnf x = seq x () 

-- type Phase2M = Phase2 MTable
-- type Phase3M = Phase3 MTable

-- type Phase2I = Phase2 Identity
-- type Phase3I = MachineP3 Identity

    -- we want to encode phases as maps to 
    -- phase records and extract fields
    -- as maps to value
onMap :: Ord k => Lens' a b -> Lens' (Map k a) (Map k b)
onMap ln f ma = M.intersectionWith (flip $ set ln) ma <$> mb' 
    where
        mb  = M.map (view ln) ma 
        mb' = f mb 

onMap' :: forall a b k. Ord k => Getting b a b -> Getter (Map k a) (Map k b)
onMap' ln = to $ M.map $ view ln

zoom :: Ord k => Set k -> Lens' (Map k a) (Map k a)
zoom s f m = M.union m1 <$> f m0
    where
        (m0,m1) = M.partitionWithKey (const . (`S.member` s)) m




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

infixl 3 <.>

(<.>) :: (Ord a,Default b) 
      => Map a (b -> c) -> Map a b -> Map a c
(<.>) mf mx = uncurry ($) <$> differenceWith g ((,def) <$> mf) mx
    where
        g (f,_) x = Just (f,x) 

zipMap :: (Default a, Default b,Ord k) 
       => Map k a -> Map k b -> Map k (a,b)
zipMap m0 m1 = M.unionWith f ((,def) <$> m0) ((def,) <$> m1)
    where
        f (x,_) (_,y) = (x,y)

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

instance (HasMachineP1' m, HasTheoryP1 t) => HasTheoryP1 (m e t) where
    theoryP1 = pContext . theoryP1

instance (HasMachineP1' m, HasTheoryP2 t) => HasTheoryP2 (m e t) where
    theoryP2 = pContext . theoryP2

instance (HasMachineP1' m, HasTheoryP3 t) => HasTheoryP3 (m e t) where
    theoryP3 = pContext . theoryP3

pEventIds :: (HasEventP1 events, HasMachineP1' phase) 
          => Getter (phase events t) (Map Label EventId)
pEventIds = pEvents . to (M.mapWithKey const) . from pEventId

getEvent :: (HasMachineP1' phase)
         => EventId
         -> Getter (phase events t) events
getEvent eid = pEvents . at eid . (\f x -> Just <$> f (fromJust'' AST.assert x))

eventDifference :: HasMachineP1' phase
                => (NonEmpty (Map Label a) -> Map Label a -> Map Label b)
                -> EventId 
                -> Getting (Map Label a) event (Map Label a)
                -> Getter (phase event t) (Map Label b)
eventDifference f eid field = pEventRef . to f' 
    where
        f' g = readGraph g $ do
            cevt  <- fromJust'' AST.assert <$> hasRightVertex (Right eid)
            es <- T.mapM (leftInfo.G.source) =<< predecessors cevt
            f (view field <$> es) <$> (view field <$> rightInfo cevt)

eventDifferenceWithId :: (HasMachineP1' phase,HasEventP1 event)
                      => (   Map Label (First a,NonEmpty SkipOrEvent) 
                          -> Map Label (First a,NonEmpty SkipOrEvent) 
                          -> Map Label (First b,c))
                      -> EventId 
                      -> Getting (Map Label a) event (Map Label a)
                      -> Getter (phase event t) (Map Label (b,c))
eventDifferenceWithId comp eid field = eventDifference f eid (to field') . to (M.map $ first getFirst)
    where 
        f old new = M.unionsWith (<>) (NE.toList old) `comp` new
        field' e = M.map ((,view eEventId e :| []).First) $ view field e

evtMergeAdded :: HasMachineP1' phase 
              => EventId
              -> Getting (Map Label a) event (Map Label a)
              -> Getter (phase event t) (Map Label a)
evtMergeAdded = eventDifference $ \old new -> new `M.difference` M.unions (NE.toList old)
evtMergeDel :: (HasMachineP1' phase, HasEventP1 event)
            => EventId
            -> Getting (Map Label a) event (Map Label a)
            -> Getter (phase event t) (Map Label (a,NonEmpty SkipOrEvent))
evtMergeDel = eventDifferenceWithId M.difference 
evtMergeKept :: (HasMachineP1' phase, HasEventP1 event)
             => EventId
             -> Getting (Map Label a) event (Map Label a)
             -> Getter (phase event t) (Map Label (a,NonEmpty SkipOrEvent))
evtMergeKept = eventDifferenceWithId M.intersection

evtSplits :: (HasMachineP1 phase event)
          => (Map Label a -> Map Label a -> Map Label a)
          -> Assert -> EventId 
          -> Getting (Map Label a) event (Map Label a) 
          -> Getter (phase event t) [Map Label a]
evtSplits union arse eid ln = to $ \m -> readGraph (m^.pEventRef) $ do
        rs <- NE.toList <$> (successors =<< leftVertex arse (Right eid))
        rs <- forM rs $ \v -> do
            r <- union <$> (view ln <$> leftInfo (G.source v)) 
                       <*> (view ln <$> rightInfo (G.target v))
            eid <- leftKey $ G.source v
            return $ r <$ eid
        return $ rights rs

evtSplitAdded :: HasMachineP1 phase event
              => Assert -> EventId
              -> Getting (Map Label a) event (Map Label a)
              -> Getter (phase event t) [Map Label a]
evtSplitAdded = evtSplits $ flip M.difference
evtSplitDel :: HasMachineP1 phase event
            => Assert -> EventId
            -> Getting (Map Label a) event (Map Label a)
            -> Getter (phase event t) [Map Label a]
evtSplitDel = evtSplits M.difference
evtSplitKept :: HasMachineP1 phase event
             => Assert -> EventId
             -> Getting (Map Label a) event (Map Label a)
             -> Getter (phase event t) [Map Label a]
evtSplitKept = evtSplits M.intersection

newDelVars :: HasMachineP2' phase
           => Getter (phase events t) (Map String Var)
newDelVars = to $ \x -> view pAbstractVars x `M.difference` view pStateVars x

pDefVars :: HasTheoryP2 phase
         => Getter phase (Map String Var)
pDefVars = to $ \x -> M.mapMaybe defToVar $ x^.pDefinitions

defToVar :: Def -> Maybe Var
defToVar (Def _ n [] t _) = Just (Var n t)
defToVar (Def _ _ (_:_) _ _) = Nothing

pAllVars :: HasMachineP2' phase
        => Getter (phase events t) (Map String Var)
pAllVars = to $ \x -> view pAbstractVars x `M.union` view pStateVars x

pEventSplit' :: (HasMachineP1' phase, HasEventP1 event)
             => Getter (phase event t) (Map EventId (event,[(EventId,event)]))
pEventSplit' = pEventRef.to f
    where
        distr (x,y) = (,y) <$> x
        f g = readGraph g $ do
            vs <- getLeftVertices
            fmap (M.fromList.rights) $ forM vs $ \v -> do
                es' <- (fmap G.target <$> successors v )
                    >>= T.mapM (\v -> distr <$> ((,) <$> rightKey v <*> rightInfo v) )
                let es = rights $ NE.toList es'
                k  <- leftKey v
                e  <- leftInfo v
                return $ distr (k,(e,es))

pEventSplit :: (HasMachineP1' phase, HasEventP1 event)
            => Getter (phase event t) (Map EventId (event,[EventId]))
pEventSplit = pEventSplit'.to (over (traverse._2.traverse) fst)

pEventMerge :: (HasMachineP1' phase, HasEventP1 event)
            => Getter (phase event t) (Map EventId (event,[EventId]))
pEventMerge = pEventMerge'.to (over (traverse._2.traverse) fst)

pEventMerge' :: (HasMachineP1' phase, HasEventP1 event)
             => Getter (phase event t) (Map EventId (event,[(EventId,event)]))
pEventMerge' = pEventRef.to f
    where
        distr (x,y) = (,y) <$> x
        f g = readGraph g $ do
            vs <- getRightVertices
            fmap (M.fromList.rights) $ forM vs $ \v -> do
                es' <- (fmap G.source <$> predecessors v )
                    >>= T.mapM (\v -> distr <$> ((,) <$> leftKey v <*> leftInfo v) )
                let es = rights $ NE.toList es'
                k  <- rightKey v
                e  <- rightInfo v
                return $ distr (k,(e,es))

traverseFilter :: Ord k => (a -> Bool) -> Traversal' (Map k a) (Map k a)
traverseFilter p f m = M.union <$> f m' <*> pure (m `M.difference` m')
    where
        m' = M.filter p m

pNewEvents :: (HasMachineP1' phase, HasEventP1 events)
           => Traversal' (phase events t) events
pNewEvents f = (pEventRef.traverseRightWithEdges) g
    where
        g (e,xs) 
            | L.null $ rights (NE.toList xs) = f e
            | otherwise                      = pure e

pOldEvents :: (HasMachineP1' phase, HasEventP1 events)
           => Getter (phase events t) (Map EventId events)
pOldEvents = pEventMerge.to (M.map fst . M.filter (not . L.null . snd))

pEvents :: (HasMachineP1' phase) 
        => Getter (phase event t) (Map EventId event)
pEvents = pEventRef.to rightMap.to f
    where
        f = M.fromList . MM.mapMaybe (rightToMaybe . (runKleisli $ first $ Kleisli id))
                       . M.toList

pEventId :: Iso' (Map Label event) (Map EventId event)
pEventId = iso 
        (M.mapKeys EventId) 
        (M.mapKeys as_label)

pIndices  :: HasMachineP2 mch event 
          => Getter (mch event t) (Map EventId (Map String Var))
pIndices = pEvents . onMap eIndices

pParams   :: HasMachineP2 mch event 
          => Getter (mch event t) (Map EventId (Map String Var))
pParams = pEvents . onMap eParams
pSchSynt  :: HasMachineP2 mch event 
          => Getter (mch event t) (Map EventId ParserSetting)    
    -- parsing schedule
pSchSynt = pEvents . onMap eSchSynt
pEvtSynt  :: HasMachineP2 mch event 
          => Getter (mch event t) (Map EventId ParserSetting)    
    -- parsing guards and actions
pEvtSynt = pEvents . onMap eEvtSynt

eIndParams :: HasEventP2 events => Getter events (Map String Var) 
eIndParams = to $ \e -> (e^.eParams) `M.union` (e^.eIndices)

-- pNewCoarseSched :: HasMachineP3 mch event 
--                 => Getter (mch event t) (Map EventId (Map Label Expr))     -- Schedules
-- pNewCoarseSched = pEvents . onMap eNewCoarseSched

-- pNewFineSched :: HasMachineP3 mch event 
--               => Getter (mch event t) (Map EventId (Map Label Expr))
-- pNewFineSched = pEvents . onMap eNewFineSched

-- pOldCoarseSched :: HasMachineP3 mch event 
--                 => Getter (mch event t) (Map EventId (Map Label Expr))     -- Schedules
-- pOldCoarseSched = pEvents . onMap eOldCoarseSched

-- pOldFineSched :: HasMachineP3 mch event 
--               => Getter (mch event t) (Map EventId (Map Label Expr))
-- pOldFineSched = pEvents . onMap eOldFineSched

-- pDelCoarseSched :: HasMachineP3 mch event 
--                 => Getter (mch event t) (Map EventId (Map Label Expr))     -- Schedules
-- pDelCoarseSched = pEvents . onMap eDelCoarseSched

-- pDelFineSched :: HasMachineP3 mch event 
--               => Getter (mch event t) (Map EventId (Map Label Expr))
-- pDelFineSched = pEvents . onMap eDelFineSched

-- pOldGuards :: HasMachineP3 mch event 
--            => Getter (mch event t) (Map EventId (Map Label Expr))
-- pOldGuards = pEvents . onMap eOldGuards

-- pNewGuards :: HasMachineP3 mch event 
--            => Getter (mch event t) (Map EventId (Map Label Expr))       -- Guards
-- pNewGuards = pEvents . onMap eNewGuards

-- pDelGuards :: HasMachineP3 mch event 
--            => Getter (mch event t) (Map EventId (Map Label Expr))       -- Guards
-- pDelGuards = pEvents . onMap eDelGuards

-- pOldActions :: HasMachineP3 mch event 
--             => Getter (mch event t) (Map EventId (Map Label Action))    -- Actions
-- pOldActions = pEvents . onMap eOldActions

-- pDelActions :: HasMachineP3 mch event 
--             => Getter (mch event t) (Map EventId (Map Label Action))
-- pDelActions = pEvents . onMap eDelActions

-- pNewActions :: HasMachineP3 mch event 
--             => Getter (mch event t) (Map EventId (Map Label Action))
-- pNewActions = pEvents . onMap eNewActions

-- pEventFineRef :: HasMachineP4 mch event
--               => Lens' (mch event t) (Map EventId (Maybe (ProgId, ProgressProp)))
-- pEventFineRef = pFineRef
--         -- pEvents . onMap eFineRef

pEventCoarseRef :: HasMachineP4 mch event
                => Getter (mch event t) (Map EventId [(Label,ScheduleChange)])
pEventCoarseRef = pEvents . onMap eCoarseRef

pWitness :: HasMachineP3 mch event 
         => Getter (mch event t) (Map EventId (Map Var RawExpr))
pWitness = pEvents . onMap eWitness

pEventRenaming :: HasMachineP1 mch event
               => Getter (mch event thy) (Map EventId [EventId])
pEventRenaming = pEventRef . to (g . f) -- to (M.fromListWith (++) . f)
    where
        g = M.fromList . MM.mapMaybe (\(x,y) -> rightToMaybe $ (,) <$> x <*> y)
                       . L.map (second sequence) 
                       . M.toList . M.map NE.toList
        f g = readGraph g $ do
            vs <- getLeftVertices
            fmap M.fromList $ forM vs $ \v -> 
                (,) <$> leftKey v 
                    <*> (T.mapM (rightKey . G.target) =<< successors v)

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

aliases :: Eq b => Lens' a b -> Lens' a b -> Lens' a b
aliases ln0 ln1 = lens getter $ flip setter
    where
        getter z
            | x == y    = x
            | otherwise = $myError ""
            where
                x = view ln0 z
                y = view ln1 z
        setter x = set ln0 x . set ln1 x

inheritWith' :: Ord k 
             => (base -> conc) 
             -> (k -> conc -> abstr)
             -> (conc -> abstr -> conc)
             -> Hierarchy k 
             -> Map k base -> Map k conc
inheritWith' decl inh (++) (Hierarchy _xs es) m = m2 -- _ $ L.foldl f (M.map decl m) xs
    where
        m1 = M.map decl m
        prec k = do
            p <- M.lookup k es 
            inh k <$> p `M.lookup` m2
        m2 = M.mapWithKey (\k c -> fromMaybe c ((c ++) <$> (prec k))) m1

inheritWithAlt :: Ord k 
             => (base -> conc) 
             -> (k -> conc -> abstr)
             -> (conc -> abstr -> conc)
             -> Hierarchy k 
             -> Map k base -> Map k conc
inheritWithAlt decl inh (++) (Hierarchy xs es) m = L.foldl f (M.map decl m) xs
    where
        f m v = case v `M.lookup` es of 
                 Just u -> M.adjustWithKey (app $ m ! u) v m
                 Nothing -> m
        app ixs k dxs = dxs ++ inh k ixs

inheritWith :: Ord k 
            => (base -> conc) 
            -> (conc -> abstr)
            -> (conc -> abstr -> conc)
            -> Hierarchy k 
            -> Map k base -> Map k conc
inheritWith decl inh = inheritWith' decl (const inh)

instance (Ord a, Arbitrary a) => Arbitrary (Hierarchy a) where
    arbitrary = do
        xs <- L.nub <$> arbitrary
        let ms = M.fromList ys
            ys = L.zip [(0 :: Int)..] xs
        zs <- forM ys $ \(i,x) -> do
            j <- QC.elements $ Nothing : L.map Just [0..i-1]
            return (x,(ms!) <$> j)
        return $ Hierarchy xs $ M.mapMaybe id $ M.fromList zs

topological_order :: Pipeline MM
                     (Map MachineId (MachineId,LineInfo)) 
                     (Hierarchy MachineId)
topological_order = Pipeline empty_spec empty_spec $ \es' -> do
        let es = M.map fst es'
            lis = M.map snd es'
            cs = cycles $ M.toList es
        vs <- triggerM =<< sequence <$> mapM (cycl_err_msg lis) cs
        return $ Hierarchy vs es
    where
        struct = "refinement structure" :: String
        cycle_msg = format msg struct -- $ intercalate ", " (map show ys)
        cycl_err_msg _ (AcyclicSCC v) = return $ Just v
        cycl_err_msg lis (CyclicSCC vs) = do
            -- li <- ask
            tell [MLError cycle_msg 
                $ L.map (first show) $ M.toList $ 
                lis `M.intersection` fromList' vs ] 
            return Nothing -- (error "topological_order")
        msg = "A cycle exists in the {0}"

fromList' :: Ord a => [a] -> Map a ()
fromList' xs = M.fromList $ L.zip xs $ L.repeat ()

inherit :: Hierarchy MachineId -> Map MachineId [b] -> Map MachineId [b]
inherit = inheritWith id id (++)

inherit2 :: (Scope s,HasMachineP1' phase,HasEventP1 evt)
         => MTable (phase evt thy)
         -> Hierarchy MachineId
         -> MTable [(t, s)] 
         -> MTable [(t, s)]
inherit2 phase = inheritWith'
            id
            (\m -> concatMap $ second' $ \s -> make_inherited' s >>= rename_events (names ! m))
            (++)
    where
        names = M.map (view pEventRenaming) phase
        make_inherited' = MM.maybeToList . make_inherited
        second' = runKleisli . second . Kleisli
        _ = MM.mapMaybe :: (a -> Maybe a) -> [a] -> [a]

inheritEvents :: Hierarchy MachineId
              -> Map MachineId [(Label, (EventId, [EventId]), t1)]
              -> Map MachineId [(Label, (EventId, [EventId]), t1)]
inheritEvents h m = inheritWith 
            id
            (L.map $ over _2 abstract)
            combine h m
    where
        combine c a = c ++ L.filter unchanged a
            where
                c' = concatMap (view $ _2 . _2) c
                unchanged (_,(x,_),_) = x `notElem` c'
        abstract (eid,_) = (eid,[eid])

run_phase :: [Pipeline MM a (Maybe b)]
          -> Pipeline MM a (Maybe [b])
run_phase xs = run_phase_aux xs >>> arr sequence

run_phase_aux :: [Pipeline MM a b] -> Pipeline MM a [b]
run_phase_aux [] = arr $ const []
run_phase_aux (cmd:cs) = proc x -> do
        y  <- cmd -< x
        ys <- run_phase_aux cs -< x
        returnA -< y:ys

liftP :: (a -> MM b) 
      -> Pipeline MM a b
liftP = Pipeline empty_spec empty_spec

liftP' :: (a -> MM (Maybe b)) 
       -> Pipeline MM (Maybe a) (Maybe b)
liftP' f = Pipeline empty_spec empty_spec 
        $ maybe (return Nothing) f

type MPipeline ph a = Pipeline MM (MTable ph) (Maybe (MTable a))

mapEvents :: (Applicative m, Monad m)
          => (key -> vA -> m vB)
          -> (key -> vA1 -> m v)
          -> G.BiGraph key vA vA1
          -> m (G.BiGraph key vB v)
mapEvents toOldEvent toNewEvent g =
                    G.leftVertices (uncurry toOldEvent) 
                        =<< G.rightVertices (uncurry toNewEvent) g

liftField :: (label -> scope -> [Either Error field]) -> [(label,scope)] -> MM' c [field]
liftField f xs = allResults (uncurry f) xs

liftFieldM :: (label -> scope -> Reader r [Either Error field]) 
           -> r -> [(label,scope)] -> MM' c [field]
liftFieldM f x xs = allResults (flip runReader x . uncurry f) xs

liftFieldMLenient :: (label -> scope -> Reader r [Either Error field]) 
                  -> r -> [(label,scope)] -> MM' c [field]
liftFieldMLenient f x xs = allResultsLenient (flip runReader x . uncurry f) xs

allResults :: (a -> [Either Error b]) -> [a] -> MM' c [b]
allResults f xs 
    | L.null es = return ys
    | otherwise = tell es >> mzero
    where
        (es,ys) = partitionEithers (concatMap f xs)

allResultsLenient :: (a -> [Either Error b]) -> [a] -> MM' c [b]
allResultsLenient f xs = tell es >> return ys
    where
        (es,ys) = partitionEithers (concatMap f xs)

triggerLenient :: MM' c a -> MM' c a
triggerLenient cmd = do
    (x,es) <- listen cmd
    if L.null es 
        then return x
        else mzero

trigger :: Maybe a -> M a
trigger (Just x) = return x
trigger Nothing  = left []

layeredUpgradeRecM :: ( HasMachineP1' mch1, HasMachineP1' mch0
               , Applicative f,MonadFix f,NFData evt1)
            => (thy0 -> thy1 -> f thy1)
            -> (mch0 evt0 thy1 -> mch1 evt0 thy1 -> f (mch1 evt0 thy1))
            -> (mch1 evt0 thy1 -> SkipOrEvent -> evt0 -> evt1 -> f evt1)
            -> (mch1 evt0 thy1 -> SkipOrEvent -> evt0 -> evt1 -> f evt1)
            -> mch0 evt0 thy0 -> f (mch1 evt1 thy1)
layeredUpgradeRecM thyF mchF oldEvF newEvF = layeredUpgradeM
        (mfix.thyF) 
        (mfix.mchF) 
        (fmap (fmap mfix).oldEvF)
        (fmap (fmap mfix).newEvF)

layeredUpgradeM :: ( HasMachineP1' mch1, HasMachineP1' mch0
            , Applicative f,Monad f,NFData evt1)
         => (thy0 -> f thy1)
         -> (mch0 evt0 thy1 -> f (mch1 evt0 thy1))
         -> (mch1 evt0 thy1 -> SkipOrEvent -> evt0 -> f evt1)
         -> (mch1 evt0 thy1 -> SkipOrEvent -> evt0 -> f evt1)
         -> mch0 evt0 thy0 -> f (mch1 evt1 thy1)
layeredUpgradeM thyF mchF oldEvF newEvF m = do
        m' <- mchF =<< (m & pContext thyF)
        m' & pEventRef (\g -> traverseLeftWithKey (uncurry (oldEvF m'))
                     =<< traverseRightWithKey (uncurry (newEvF m')) g)

layeredUpgradeRec :: (HasMachineP1' mch1, HasMachineP1' mch0, NFData evt1)
           => (thy0 -> thy1 -> thy1)
           -> (mch0 evt0 thy1 -> mch1 evt0 thy1 -> mch1 evt0 thy1)
           -> (mch1 evt0 thy1 -> SkipOrEvent -> evt0 -> evt1 -> evt1)
           -> (mch1 evt0 thy1 -> SkipOrEvent -> evt0 -> evt1 -> evt1)
           -> mch0 evt0 thy0 -> mch1 evt1 thy1
layeredUpgradeRec thyF mchF oldEvF newEvF = layeredUpgrade
        (fix.thyF) 
        (fix.mchF) 
        (fmap (fmap fix).oldEvF)
        (fmap (fmap fix).newEvF)

layeredUpgrade :: (HasMachineP1' mch1, HasMachineP1' mch0, NFData evt1)
        => (thy0 -> thy1)
        -> (mch0 evt0 thy1 -> mch1 evt0 thy1)
        -> (mch1 evt0 thy1 -> SkipOrEvent -> evt0 -> evt1)
        -> (mch1 evt0 thy1 -> SkipOrEvent -> evt0 -> evt1)
        -> mch0 evt0 thy0 -> mch1 evt1 thy1
layeredUpgrade thyF mchF oldEvF newEvF = runIdentity . layeredUpgradeM
        (Identity . thyF) (Identity . mchF) 
        (fmap (fmap Identity) . oldEvF)
        (fmap (fmap Identity) . newEvF)

upgradeM :: ( HasMachineP1' mch1, HasMachineP1' mch0
            , Applicative f,Monad f,NFData evt1)
         => (thy0 -> f thy1)
         -> (mch0 evt0 thy0 -> f (mch1 evt0 thy0))
         -> (mch0 evt0 thy0 -> SkipOrEvent -> evt0 -> f evt1)
         -> (mch0 evt0 thy0 -> SkipOrEvent -> evt0 -> f evt1)
         -> mch0 evt0 thy0 -> f (mch1 evt1 thy1)
upgradeM thyF mchF oldEvF newEvF m = do
        m' <- pContext thyF =<< mchF m
        m' & pEventRef (\g -> 
                (traverseLeftWithKey (uncurry (oldEvF m))
                     =<< traverseRightWithKey (uncurry (newEvF m)) g))

upgrade :: (HasMachineP1' mch1, HasMachineP1' mch0, NFData evt1)
        => (thy0 -> thy1)
        -> (mch0 evt0 thy0 -> mch1 evt0 thy0)
        -> (mch0 evt0 thy0 -> SkipOrEvent -> evt0 -> evt1)
        -> (mch0 evt0 thy0 -> SkipOrEvent -> evt0 -> evt1)
        -> mch0 evt0 thy0 -> mch1 evt1 thy1
upgrade thyF mchF oldEvF newEvF = runIdentity . upgradeM
        (Identity . thyF) (Identity . mchF) 
        (fmap (fmap Identity) . oldEvF)
        (fmap (fmap Identity) . newEvF)
