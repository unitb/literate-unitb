{-# LANGUAGE MultiParamTypeClasses          #-}
{-# LANGUAGE TemplateHaskell                #-}
{-# LANGUAGE FunctionalDependencies         #-}
{-# LANGUAGE FlexibleInstances              #-}
{-# LANGUAGE FlexibleContexts               #-}
{-# LANGUAGE RankNTypes, GADTs              #-}
{-# LANGUAGE ScopedTypeVariables            #-}
{-# LANGUAGE TypeOperators,TypeFamilies     #-}
{-# LANGUAGE TupleSections                  #-}
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
import Control.Arrow
import Control.Parallel.Strategies
import Control.Lens as L

import Control.Monad.Reader.Class 
import Control.Monad.State
import Control.Monad.Trans.Either
import Control.Monad.Trans.State  as ST
import Control.Monad.Trans.Reader as R hiding (local,ask)

-- import Data.Functor
-- import Data.Monoid
import Data.Either
import Data.Either.Combinators
import Data.Map as M
import Data.Monoid
import Data.List as L
import Data.Set as S

import Utilities.Error
-- import Utilities.Relation hiding ((!))
import Utilities.Syntactic
import Utilities.TH
import Utilities.Permutation

infixl 3 <.>

all_errors' :: [Either [e] a] -> Either [e] [a]
all_errors' xs = do
    let es = lefts xs
    unless (L.null es)
        $ Left $ concat es
    return $ L.map fromRight' xs

all_errors :: Ord k => Map k (Either [e] a) -> Either [e] (Map k a)
all_errors m = do
        let es = lefts $ M.elems m
        unless (L.null es)
            $ Left $ concat es
        return $ M.map fromRight' m

make_table' :: forall a b.
               (Ord a, Show a, Scope b) 
            => (a -> String) 
            -> [(a,b)] 
            -> Either [Error] (Map a b)
make_table' f xs = all_errors $ M.mapWithKey g ws
    where
        g k ws
                | all (\xs -> length xs <= 1) ws 
                            = Right $ L.foldl merge_scopes (head xs) (tail xs)
                | otherwise = Left $ L.map (\xs -> MLError (f k) $ L.map error_item xs) 
                                    $ L.filter (\xs -> length xs > 1) ws
            where
                xs = concat ws             
        zs = fromListWith (++) $ L.map (\(x,y) -> (x,[y])) xs
        ws :: Map a [[b]]
        ws = M.map (flip u_scc clashes) zs 

make_table :: (Ord a, Show a) 
           => (a -> String) 
           -> [(a,b,LineInfo)] 
           -> Either [Error] (Map a (b,LineInfo))
make_table f xs = returnOrFail $ fromListWith add $ L.map mkCell xs
    where
        mkCell (x,y,z) = (x,Right (y,z))
        sepError (x,y) = case y of
                 Left z -> Left (x,z)
                 Right (z,li) -> Right (x,(z,li))
        returnOrFail m = failIf $ L.map sepError $ M.toList m
        failIf xs 
            | L.null ys = return $ M.fromList $ rights xs
            | otherwise = Left $ L.map (uncurry err) ys
            where
                ys = lefts xs
        err x li = MLError (f x) (L.map (show x,) li)
        lis (Left xs)     = xs
        lis (Right (_,z)) = [z]
        add x y = Left $ lis x ++ lis y

make_all_tables' :: (Scope b, Show a, Ord a, Ord k) 
                 => (a -> String) 
                 -> Map k [(a,b)] 
                 -> Either [Error] (Map k (Map a b))
make_all_tables' f xs = all_errors (M.map (make_table' f) xs) `using` parTraversable rseq

make_all_tables :: (Show a, Ord a, Ord k) 
                => (a -> String)
                -> Map k [(a, b, LineInfo)] 
                -> Either [Error] (Map k (Map a (b,LineInfo)))
make_all_tables f xs = all_errors (M.map (make_table f) xs) `using` parTraversable rseq

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

type MachinePh0' a = MachinePh0

data MachinePh0 = MachinePh0
        { _pAllMachines :: MTable ()
        , _pMachineId   :: MachineId }
    deriving Show

type MachinePh1 = MachinePh1' EventPh1 TheoryP1

data MachinePh1' events theory = MachinePh1 
    { _p0 :: MachinePh0
    , _pEvents    :: Map EventId events
    , _pContext   :: theory
    -- , _machinePh1'PEvents :: Map Label events
    -- , _pNewEvents :: Map Label EventId
    } deriving Show

type MachinePh2 = MachinePh2' EventPh2 TheoryP2

data MachinePh2' events theory = MachinePh2
    { _p1 :: MachinePh1' events theory
    , _pDefinitions :: Map String Def
    , _pConstants :: Map String Var
    , _pDelVars   :: Map String (Var,LineInfo)
    , _pStateVars :: Map String Var             -- machine variables
    , _pAbstractVars :: Map String Var          -- abstract machine variables
    , _pDummyVars :: Map String Var             -- dummy variables
    , _pNotation  :: Notation
    , _pCtxSynt   :: ParserSetting                  -- parsing assumptions
    , _pMchSynt   :: ParserSetting                  -- parsing invariants and properties
    } deriving Show


type MachinePh3 = MachinePh3' EventPh3 TheoryP2

data MachinePh3' events theory = MachinePh3
    { _p2 :: MachinePh2' events theory
    , _pProgress  :: Map ProgId ProgressProp
    , _pSafety    :: Map Label SafetyProp
    , _pTransient :: Map Label Transient
    , _pAssumptions :: Map Label Expr
    , _pInvariant   :: Map Label Expr                     -- Invariants
    , _pInit        :: Map Label Expr
    , _pOldPropSet  :: PropertySet
    , _pNewPropSet  :: PropertySet
    } deriving Show

type MachinePh4 = MachinePh4' EventPh4 TheoryP2

data MachinePh4' events theory = MachinePh4
    { _p3 :: MachinePh3' events theory
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
    , _eDelActions  :: Map Label ()
    , _eNewActions  :: Map Label Action
    } deriving Show

data EventPh4 = EventPh4 
    { _e3 :: EventPh3 
    , _eRefRule  :: [(Label,ScheduleChange)]
    , _eOldSched :: [(Label,Change)]
    }

data Change = AddC | RemoveC
    deriving (Eq,Show)

data TheoryP0 = TheoryP0
    { _tNothing :: ()
    }

data TheoryP1 = TheoryP1
    { _t0 :: TheoryP0
    , _pImports   :: Map String Theory
    , _pTypes     :: Map String Sort
    , _pAllTypes  :: Map String Sort
    , _pSetDecl   :: [(String, VarScope)]
    }

data TheoryP2 = TheoryP2
    { _t1 :: TheoryP1 
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

(<.>) :: (Ord a) => Map a (b -> c) -> Map a b -> Map a c
(<.>) mf mx = M.intersectionWith id mf mx

-- onMachine :: MachineId -> Lens' Phase2M Phase2I
-- onMachine = _








$(makeClassy ''EventPh1)

$(makeClassy ''EventPh2)

$(makeClassy ''EventPh3)

$(makeClassy ''EventPh4)

createHierarchy 
        [ (''MachinePh1' ,'_p0)
        , (''MachinePh2' ,'_p1)
        , (''MachinePh3' ,'_p2)
        , (''MachinePh4' ,'_p3)
        -- , (''MachinePh1', '_pContext)
        , (''TheoryP1, '_t0)
        , (''TheoryP2, '_t1)
        -- , (''MachinePh0' ,undefined)
        ]


$(makeHierarchy
           ''EventPh1
        [ (''EventPh2, 'e1)
        , (''EventPh3, 'e2)
        , (''EventPh4, 'e3)
        ] )

instance (HasMachinePh1' m, HasTheoryP1 t) => HasTheoryP1 (m e t) where
    theoryP1 = pContext . theoryP1

instance (HasMachinePh1' m, HasTheoryP2 t) => HasTheoryP2 (m e t) where
    theoryP2 = pContext . theoryP2

pEventIds :: (HasEventPh1 events, HasMachinePh1' phase) 
          => Lens' (phase events t) (Map Label EventId)
pEventIds = pEvents . from pFromEventId . onMap pEventId

eGuards :: HasEventPh3 events => Getter events (Map Label Expr)
eGuards = to getter
    where
        getter p = (M.unionWith $ error "eGuards: name clash") old new
            where
                old = L.view eOldGuards p
                new = L.view eNewGuards p

pGuards :: HasMachinePh3 phase events => Getter (phase events t) (Map EventId (Map Label Expr))
pGuards = pEvents . onMap' eGuards
        -- coerce $ f $ M.unionWith (M.unionWith $ error "pGuards: name clash") old new
    -- where
    --     old = L.view eOldGuards p
    --     new = L.view eNewGuards p

pSchedules :: HasMachinePh3 phase events => Getter (phase events t) (Map EventId (Map Label Expr))       
pSchedules f p = coerce $ f $ M.unionWith (M.unionWith $ error "pSchedules: name clash") csch fsch
    where
        csch = L.view pCoarseSched p
        fsch = L.view pFineSched p

pFromEventId :: HasEventPh1 event => Iso' (Map Label event) (Map EventId event)
pFromEventId = iso 
        (M.fromList . L.map (view pEventId &&& id) . M.elems) 
        (mapKeys as_label)

pIndices  :: HasMachinePh2 mch event => Lens' (mch event t) (Map EventId (Map String Var))
pIndices = pEvents . onMap eIndices
pParams   :: HasMachinePh2 mch event => Lens' (mch event t) (Map EventId (Map String Var))
pParams = pEvents . onMap eParams
pSchSynt  :: HasMachinePh2 mch event => Lens' (mch event t) (Map EventId ParserSetting)    
    -- parsing schedule
pSchSynt = pEvents . onMap eSchSynt
pEvtSynt  :: HasMachinePh2 mch event => Lens' (mch event t) (Map EventId ParserSetting)    
    -- parsing guards and actions
pEvtSynt = pEvents . onMap eEvtSynt

pCoarseSched :: HasMachinePh3 mch event 
             => Lens' (mch event t) (Map EventId (Map Label Expr))     -- Schedules
pCoarseSched = pEvents . onMap eCoarseSched

pFineSched   :: HasMachinePh3 mch event 
             => Lens' (mch event t) (Map EventId (Map Label Expr))
pFineSched = pEvents . onMap eFineSched

pOldGuards   :: HasMachinePh3 mch event 
             => Lens' (mch event t) (Map EventId (Map Label Expr))
pOldGuards = pEvents . onMap eOldGuards

pNewGuards   :: HasMachinePh3 mch event 
             => Lens' (mch event t) (Map EventId (Map Label Expr))       -- Guards
pNewGuards = pEvents . onMap eNewGuards

pOldActions  :: HasMachinePh3 mch event 
             => Lens' (mch event t) (Map EventId (Map Label Action))    -- Actions
pOldActions = pEvents . onMap eOldActions

pDelActions  :: HasMachinePh3 mch event 
             => Lens' (mch event t) (Map EventId (Map Label ()))
pDelActions = pEvents . onMap eDelActions

pNewActions  :: HasMachinePh3 mch event 
             => Lens' (mch event t) (Map EventId (Map Label Action))
pNewActions = pEvents . onMap eNewActions

pEventRefRule :: HasMachinePh4 mch event
              => Lens' (mch event t) (Map EventId [(Label,ScheduleChange)])
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
