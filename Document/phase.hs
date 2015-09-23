{-# LANGUAGE MultiParamTypeClasses          #-}
{-# LANGUAGE TemplateHaskell                #-}
{-# LANGUAGE DeriveDataTypeable             #-}
{-# LANGUAGE Arrows                         #-}
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
import Logic.Proof.Tactics

import UnitB.AST

    -- Libraries
-- import Control.Applicative
import Control.Applicative
import Control.Arrow hiding (ArrowChoice(..))
import Control.Lens as L

import Control.Monad.Reader.Class 
import Control.Monad.Reader (Reader,runReader) 
import Control.Monad.State
import Control.Monad.Trans.Either
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.State  as ST
import Control.Monad.Trans.RWS    as RWS hiding (local,ask,tell)
import Control.Monad.Writer.Class 

import Data.Either
import Data.Graph
import Data.List as L
import Data.List.NonEmpty as NE
import Data.Map   as M
import Data.Maybe as MM
import Data.Monoid
import Data.Proxy
import Data.Set as S
import qualified Data.Traversable as T
import Data.Typeable

import Utilities.BipartiteGraph as G
import Utilities.Error
-- import Utilities.Relation hiding ((!))
import Utilities.Syntactic
import Utilities.Format
import Utilities.TableConstr
import Utilities.TH

-- type MachineP0 = MachineP0' ()

-- data MachineP0' a = MachineP0

triggerM :: Maybe a -> MM a
triggerM x = MaybeT $ return x

triggerP :: Pipeline MM (Maybe a) a
triggerP = Pipeline empty_spec empty_spec triggerM


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
    read_one  = fmap PId <$> read_one
    read_args = fmap PId <$> read_args

cmdSpec :: String -> Int -> DocSpec
cmdSpec cmd nargs = DocSpec M.empty (M.singleton cmd nargs)

envSpec :: String -> Int -> DocSpec
envSpec env nargs = DocSpec (M.singleton env nargs) M.empty

parseArgs :: (IsTuple a, AllReadable (TypeList a))
          => ([LatexDoc], LineInfo)
          -> M a
parseArgs xs = do
    (x,([],_)) <- ST.runStateT read_all xs
    return $ fromTuple x

machineCmd :: forall result args ctx. 
              ( Monoid result, IsTuple args
              , IsTypeList  (TypeList args)
              , AllReadable (TypeList args))
           => String
           -> (args -> MachineId -> ctx -> M result) 
           -> Pipeline MM (MTable ctx) (Maybe (MTable result))
machineCmd cmd f = Pipeline m_spec empty_spec g
    where
        nargs = len (Proxy :: Proxy (TypeList args))
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
           -> c -> (Map c d) -> MM (Maybe a)
cmdFun f xs m ctx = case x of
                      Right x -> tell w >> return (Just x)
                      Left es -> tell (w ++ es) >> return Nothing
    where
        (x,(),w) = runRWS (runEitherT $ do
                        x <- parseArgs (getCmdArgs xs)
                        f x m (ctx ! m) )
                    (cmdLI xs) 
                    ()

machineEnv :: forall result args ctx.
              ( Monoid result, IsTuple args
              , IsTypeList  (TypeList args)
              , AllReadable (TypeList args))
           => String
           -> (args -> LatexDoc -> MachineId -> ctx -> M result)
           -> Pipeline MM (MTable ctx) (Maybe (MTable result))
machineEnv env f = Pipeline m_spec empty_spec g
    where
        nargs = len (Proxy :: Proxy (TypeList args))
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
           => (b -> LatexDoc -> c -> d -> M a) 
           -> Env
           -> c -> (Map c d) -> MM (Maybe a)
envFun f xs m ctx = case x of
                      Right x -> tell w >> return (Just x)
                      Left es -> tell (w ++ es) >> return Nothing
    where
        (x,(),w) = runRWS (runEitherT $ do
                        x <- parseArgs (getEnvArgs xs)
                        f x (getEnvContent xs) m (ctx ! m))
                    (envLI xs) 
                    ()

contextCmd :: forall a b c. 
              ( Monoid a, IsTuple b
              , IsTypeList  (TypeList b)
              , AllReadable (TypeList b))
           => String
           -> (b -> ContextId -> c -> M a) 
           -> Pipeline MM (CTable c) (Maybe (CTable a))
contextCmd cmd f = Pipeline empty_spec c_spec g
    where
        nargs = len (Proxy :: Proxy (TypeList b))
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
           -> (args -> LatexDoc -> ContextId -> ctx -> M result)
           -> Pipeline MM (CTable ctx) (Maybe (CTable result))
contextEnv env f = Pipeline empty_spec c_spec g
    where
        nargs = len (Proxy :: Proxy (TypeList args))
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
    deriving (Show,Typeable)

type MachineP1 = MachineP1' EventP1 TheoryP1

data MachineP1' events theory = MachineP1 
    { _p0 :: MachineP0
    , _pEventRef :: BiGraph (Maybe EventId) events events
    , _pContext  :: theory
    } deriving (Show,Typeable)

type MachineP2 = MachineP2' EventP2 TheoryP2

data MachineP2' events theory = MachineP2
    { _p1 :: MachineP1' events theory
    , _pDelVars   :: Map String (Var,LineInfo)
    , _pStateVars :: Map String Var             -- machine variables
    , _pAbstractVars :: Map String Var          -- abstract machine variables
    , _pMchSynt   :: ParserSetting                  -- parsing invariants and properties
    } deriving (Show,Typeable)

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
    } deriving (Show,Typeable)

type MachineP4 = MachineP4' EventP4 TheoryP3

data MachineP4' events theory = MachineP4
    { _p3 :: MachineP3' events theory
    , _pLiveRule :: Map ProgId Rule
    , _pFineRef  :: Map EventId (Maybe (ProgId,ProgressProp))
    , _pProofs   :: Map Label (Tactic Proof, LineInfo)
    , _pComments :: Map DocItem String
    } deriving (Typeable)

data EventP1 = EventP1
    deriving (Show,Typeable)

data EventP2 = EventP2 
    { _e1 :: EventP1 
    , _eIndices :: Map String Var
    , _eParams  :: Map String Var
    , _eSchSynt :: ParserSetting
    , _eEvtSynt :: ParserSetting
    } deriving (Show,Typeable)

data EventP3 = EventP3 
    { _e2 :: EventP2 
    , _eCoarseSched :: Map Label Expr     
    , _eFineSched   :: Map Label Expr
    , _eGuards   :: Map Label Expr       
    , _eWitness     :: Map Var Expr
    , _eActions  :: Map Label Action
    } deriving (Show,Typeable)

data EventP4 = EventP4 
    { _e3 :: EventP3 
    , _eCoarseRef  :: [(Label,ScheduleChange)]
    , _eFineRef    :: Maybe (ProgId,ProgressProp)
    } deriving (Typeable)

data Change = AddC | RemoveC
    deriving (Eq,Show)

data TheoryP0 = TheoryP0
    { _tNothing :: ()
    } deriving (Show,Typeable)

type PostponedDef = (Def,DeclSource,LineInfo)

data TheoryP1 = TheoryP1
    { _t0 :: TheoryP0
    , _pImports   :: Map String Theory
    , _pTypes     :: Map String Sort
    , _pAllTypes  :: Map String Sort
    , _pSetDecl   :: [(String, PostponedDef)]
    } deriving (Show,Typeable)

data TheoryP2 = TheoryP2
    { _t1 :: TheoryP1 
    , _pDefinitions :: Map String Def
    , _pConstants :: Map String Var
    , _pDummyVars :: Map String Var             -- dummy variables
    , _pNotation  :: Notation
    , _pCtxSynt   :: ParserSetting                  -- parsing assumptions
    } deriving (Show,Typeable)

data TheoryP3 = TheoryP3
    { _t2 :: TheoryP2
    , _pAssumptions :: Map Label Expr
    } deriving (Show,Typeable)

newtype Abs a = Abs { getAbstract :: a }
    deriving (Eq,Ord)

newtype Conc a = Conc { getConcrete :: a }
    deriving (Eq,Ord)

class IsLabel a where
    as_label :: a -> Label

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

makeRecordConstr ''MachineP2'
makeRecordConstr ''MachineP3'
makeRecordConstr ''MachineP4'

makeRecordConstr ''EventP2
makeRecordConstr ''EventP3
makeRecordConstr ''EventP4

makeRecordConstr ''TheoryP2
makeRecordConstr ''TheoryP3

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

class LensState m0 m1 where
    type StateOf (a :: * -> *) :: *
    -- type StateB m1 :: *
    focus :: Lens' (StateOf m0) (StateOf m1) -> m1 a -> m0 a

instance Monad m => LensState (StateT a m) (StateT b m) where
    type StateOf (StateT a m) = a
    focus ln cmd = StateT f 
        where
            f x = second (\y -> set ln y x) `liftM` runStateT cmd (view ln x)

instance Monad m => LensState (RWST r w a m) (RWST r w b m) where
    type StateOf (RWST r w a m) = a
    focus ln cmd = RWST f
        where
            f r x = over _2 (\y -> set ln y x) `liftM` runRWST cmd r (view ln x)

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
getEvent eid = pEvents . at eid . (\f x -> Just <$> f (MM.fromJust x))

newDelVars :: HasMachineP2' phase
           => Getter (phase events t) (Map String Var)
newDelVars = to $ \x -> view pAbstractVars x `M.difference` view pStateVars x


pEventMerge :: (HasMachineP1' phase, HasEventP1 events)
            => Getter (phase events t) (Map EventId (events,[EventId]))
pEventMerge = pEventRef.to f
    where
        f g = readGraph g $ do
            vs <- getRightVertices
            fmap (M.fromList.catMaybes) $ forM vs $ \v -> do
                es <- (catMaybes.NE.toList) 
                        <$> (    T.mapM (leftKey.G.source) 
                             =<< predecessors v)
                k  <- rightKey v
                e  <- rightInfo v
                return $ (,(e,es)) <$> k

pNewEvents :: (HasMachineP1' phase, HasEventP1 events)
           => Getter (phase events t) (Map EventId events)
pNewEvents = pEventMerge.to (M.map fst . M.filter (L.null . snd))

pOldEvents :: (HasMachineP1' phase, HasEventP1 events)
           => Getter (phase events t) (Map EventId events)
pOldEvents = pEventMerge.to (M.map fst . M.filter (not . L.null . snd))

pEvents :: (HasMachineP1' phase) 
        => Getter (phase event t) (Map EventId event)
pEvents = pEventRef.to rightMap.to f
    where
        f = M.fromList . MM.mapMaybe (runKleisli $ first $ Kleisli id)
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














pEventCoarseRef :: HasMachineP4 mch event
                => Getter (mch event t) (Map EventId [(Label,ScheduleChange)])
pEventCoarseRef = pEvents . onMap eCoarseRef

pWitness :: HasMachineP3 mch event 
         => Getter (mch event t) (Map EventId (Map Var Expr))
pWitness = pEvents . onMap eWitness

pEventRenaming :: HasMachineP1 mch event
               => Getter (mch event thy) (Map EventId [EventId])
pEventRenaming = pEventRef . to (g . f) -- to (M.fromListWith (++) . f)
    where
        g = M.fromList . MM.mapMaybe (\(x,y) -> (,) <$> x <*> y)
                       . L.map (second sequence) 
                       . M.toList . M.map NE.toList
        f g = readGraph g $ do
            vs <- getRightVertices
            fmap M.fromList $ forM vs $ \v -> 
                (,) <$> rightKey v 
                    <*> (T.mapM (leftKey . G.source) =<< predecessors v)

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
    deriving (Show,Typeable)

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
inheritWith' decl inh (++) (Hierarchy xs es) m = L.foldl f (M.map decl m) xs
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

topological_order :: Pipeline MM
                     (Map MachineId (MachineId,LineInfo)) 
                     (Hierarchy MachineId)
topological_order = Pipeline empty_spec empty_spec $ \es' -> do
        let es = M.map fst es'
            lis = M.map snd es'
            cs = cycles $ M.toList es
        vs <- MaybeT $ sequence <$> mapM (cycl_err_msg lis) cs
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

inherit2 :: Scope s
         => MTable (Map EventId [EventId])
         -> Hierarchy MachineId
         -> MTable [(t, s)] 
         -> MTable [(t, s)]
inherit2 evts = inheritWith'
            id
            (\m -> concatMap $ second' $ \s -> make_inherited' s >>= rename_events (evts ! m))
            (++)
    where
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

liftField :: (label -> scope -> [Either Error field]) -> [(label,scope)] -> MM [field]
liftField f xs = allResults (uncurry f) xs

liftFieldM :: (label -> scope -> Reader r [Either Error field]) 
           -> r -> [(label,scope)] -> MM [field]
liftFieldM f x xs = allResults (flip runReader x . uncurry f) xs

allResults :: MonadWriter [e] m 
           => (a -> [Either e b]) -> [a] -> MaybeT m [b]
allResults f xs 
    | L.null es = return ys
    | otherwise = tell es >> mzero
    where
        (es,ys) = partitionEithers (concatMap f xs)

trigger :: Maybe a -> M a
trigger (Just x) = return x
trigger Nothing  = left []
