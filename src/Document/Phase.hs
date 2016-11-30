{-# LANGUAGE Arrows                         #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE ScopedTypeVariables            #-}
{-# LANGUAGE TypeOperators,TypeFamilies     #-}
{-# LANGUAGE RecordWildCards  #-}
{-# LANGUAGE StandaloneDeriving, UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Document.Phase where

    -- Modules
import Document.Pipeline
import Document.Phase.Types
import Document.Phase.Parameters
import Document.Scope
import Document.Visitor (M,runM,left,hoistEither,bind,bind_all)

import Latex.Parser

import Logic.Expr.Parser (ParserSetting)
import Logic.Proof

import UnitB.Expr
import UnitB.Syntax as AST

    -- Libraries
import Control.Applicative
import Control.Arrow hiding (ArrowChoice(..))
import Control.CoApplicative
import Control.Lens as L hiding ((<.>))
import Control.Lens.Misc

import Control.Monad.Except (MonadError)
import Control.Monad.Reader.Class 
import Control.Monad.Reader (Reader,runReader) 
import Control.Monad.State
import Control.Monad.Writer.Class 
import Control.Precondition

import Data.Default
import Data.Either
import Data.Graph.Bipartite as G hiding (fromList')
import Data.Hashable
import Data.List as L
import Data.List.NonEmpty as NE
import Data.Map as M hiding ((!))
import Data.Maybe as MM
import Data.Semigroup
import qualified Data.Traversable as T
import Data.Tuple.Generics

import GHC.Generics.Instances

import Test.QuickCheck as QC hiding (label,collect)

import Text.Printf.TH

import Utilities.Graph (cycles,SCC(..))
import Utilities.Error (myError)
import Utilities.Syntactic

triggerM :: Maybe a -> MM' c a
triggerM = maybe mzero return

triggerP :: Pipeline MM (Maybe a) a
triggerP = Pipeline empty_spec empty_spec triggerM

cmdSpec :: IsTuple LatexArg a 
        => String -> Proxy a -> DocSpec
cmdSpec cmd p = DocSpec M.empty (M.singleton cmd $ ArgumentSpec nargs p)
    where
        nargs = len latexArgProxy p

envSpec :: IsTuple LatexArg a 
        => String -> Proxy a -> DocSpec
envSpec env p = DocSpec (M.singleton env $ ArgumentSpec nargs p) M.empty
    where
        nargs = len latexArgProxy p

read_all :: (IsTuple LatexArg a)
         => StateT ([LatexDoc],LineInfo) M a
read_all = do
    let p = Proxy :: Proxy LatexArg
        read_one' :: forall b. (LatexArg b) 
                  => StateT ([LatexDoc],LineInfo) M b
        read_one' = do
            (xs,li) <- get
            case xs of
              (x:xs) -> put (xs,after x) >> lift (hoistEither $ read_one x)
              []     -> lift $ left [Error "expecting more arguments" li]
    makeTuple' p read_one'

parseArgs :: (IsTuple LatexArg a,Pre)
          => ([LatexDoc], LineInfo)
          -> M a
parseArgs xs = do
    (x,(xs,_)) <- runStateT read_all xs
    return $ byPred "null remainder" L.null xs x

machineCmd :: forall result args ctx. 
              ( Monoid result
              , IsTuple LatexArg args )
           => String
           -> (args -> MachineId -> ctx -> M result) 
           -> Pipeline MM (MMap ctx) (Maybe (MMap result))
machineCmd cmd f = Pipeline m_spec empty_spec g
    where
        m_spec = cmdSpec cmd (Proxy :: Proxy args)
        param = Collect 
            { getList = getInputMap . getFunctor . getCmd
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
        (x,w) = runM (do
                    x <- parseArgs (getCmdArgs xs)
                    f x m (ctx ! m) )
                (cmdLI xs) 

machineEnv :: forall result args ctx.
              ( Monoid result, IsTuple LatexArg args )
           => String
           -> (args -> LatexDoc -> MachineId -> ctx -> M result)
           -> Pipeline MM (MMap ctx) (Maybe (MMap result))
machineEnv env f = Pipeline m_spec empty_spec g
    where
        m_spec = envSpec env (Proxy :: Proxy args)
        param = Collect 
            { getList = getInputMap . getFunctor . getEnv
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
        (x,w) = runM (do
                        x <- parseArgs (getEnvArgs xs)
                        f x (getEnvContent xs) m (ctx ! m))
                    (envLI xs) 

contextCmd :: forall a b c. 
              ( Monoid a, IsTuple LatexArg b )
           => String
           -> (b -> ContextId -> c -> M a) 
           -> Pipeline MM (CMap c) (Maybe (CMap a))
contextCmd cmd f = Pipeline empty_spec c_spec g
    where
        c_spec = cmdSpec cmd (Proxy :: Proxy b)
        param = Collect 
            { getList = getInputMap . getFunctor . getCmd
            , tag = cmd
            , getInput = getContextInput
            }
        g = collect param (cmdFun f)

contextEnv :: forall result args ctx.
              ( Monoid result, IsTuple LatexArg args )
           => String
           -> (args -> LatexDoc -> ContextId -> ctx -> M result)
           -> Pipeline MM (CMap ctx) (Maybe (CMap result))
contextEnv env f = Pipeline empty_spec c_spec g
    where
        c_spec = envSpec env (Proxy :: Proxy args)
        param = Collect 
            { getList = getInputMap . getFunctor . getEnv
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

--zoom :: Ord k => Set k -> Lens' (Map k a) (Map k a)
--zoom s f m = M.union m1 <$> f m0
--    where
--        (m0,m1) = M.partitionWithKey (const . (`S.member` s)) m

infixl 3 <.>

{-# SPECIALIZE (<.>) :: (Ord a,Default b) => Map a (b -> c) -> Map a b -> Map a c #-}
{-# SPECIALIZE (<.>) :: (Ord a,Default b) => Map a (b -> c) -> Map a b -> Map a c #-}
(<.>) :: (Default b,Ord a) 
      => Map a (b -> c) -> Map a b -> Map a c
(<.>) mf mx = uncurry ($) <$> differenceWith g ((,def) <$> mf) mx
    where
        g (f,_) x = Just (f,x) 

zipMap :: (Default a, Default b,Ord k) 
       => Map k a -> Map k b -> Map k (a,b)
zipMap m0 m1 = M.unionWith f ((,def) <$> m0) ((def,) <$> m1)
    where
        f (x,_) (_,y) = (x,y)

instance (HasMachineP1 (m a c t), HasTheoryP1 t) => HasTheoryP1 (m a c t) where
    theoryP1 = pContext . theoryP1

instance (HasMachineP1 (m a c t), HasTheoryP2 t) => HasTheoryP2 (m a c t) where
    theoryP2 = pContext . theoryP2

instance (HasMachineP1 (m a c t), HasTheoryP3 t) => HasTheoryP3 (m a c t) where
    theoryP3 = pContext . theoryP3

pEventIds :: (HasMachineP1 phase) 
          => Getter phase (Map Label EventId)
pEventIds = pEvents . to (M.mapWithKey const) . from pEventId

getEvent :: (HasMachineP1 phase)
         => EventId
         -> Getter phase (CEvtType phase)
getEvent eid = pEvents . at eid . (\f x -> Just <$> f (fromJust' x))

eventDifference :: (HasMachineP1 phase, AEvtType phase ~ CEvtType phase)
                => (NonEmpty (Map label a) -> Map label a -> Map label b)
                -> EventId 
                -> Getting (Map label a) (AEvtType phase) (Map label a)
                -- -> Getting (Map label a) event (Map label a)
                -> Getter phase (Map label b)
eventDifference f eid field = pEventRef . to f'
    where
        f' g = readGraph g $ do
            cevt  <- fromJust' <$> hasRightVertex (Right eid)
            es <- T.mapM (leftInfo.G.source) =<< predecessors cevt
            f (view field <$> es) <$> (view field <$> rightInfo cevt)

eventDifferenceWithId :: (HasMachineP1 phase,Ord label,AEvtType phase ~ CEvtType phase)
                      => (   Map label (First a,NonEmpty SkipOrEvent) 
                          -> Map label (First a,NonEmpty SkipOrEvent) 
                          -> Map label (First b,c))
                      -> EventId 
                      -> Getting (Map label a) (AEvtType phase) (Map label a)
                      -> Getter phase (Map label (b,c))
eventDifferenceWithId comp eid field = eventDifference f eid (to $ field' field) . to (M.map $ first getFirst)
    where 
        f old new = M.unionsWith (<>) (NE.toList old) `comp` new
        field' ln e = M.map ((,view eEventId e :| []).First) $ view ln e

evtMergeAdded :: (HasMachineP1 phase, Ord label,AEvtType phase ~ CEvtType phase)
              => EventId
              -> Getting (Map label a) (AEvtType phase) (Map label a)
              -> Getter phase (Map label a)
evtMergeAdded = eventDifference $ \old new -> new `M.difference` M.unions (NE.toList old)
evtMergeDel :: (HasMachineP1 phase, Ord label,AEvtType phase ~ CEvtType phase)
            => EventId
            -> Getting (Map label a) (AEvtType phase) (Map label a)
            -- -> Getter phase (Map label (a,NonEmpty SkipOrEvent))
            -> Getter phase (Map label a)
evtMergeDel eid ln = eventDifferenceWithId M.difference eid ln . to (fmap fst)
evtMergeKept :: (HasMachineP1 phase,AEvtType phase ~ CEvtType phase)
             => EventId
             -> Getting (Map Label a) (AEvtType phase) (Map Label a)
             -> Getter (phase) (Map Label (a,NonEmpty SkipOrEvent))
evtMergeKept = eventDifferenceWithId M.intersection

evtSplits :: (HasMachineP1 phase,AEvtType phase ~ CEvtType phase,Pre)
          => (Map Label a -> Map Label a -> Map Label a)
          -> EventId 
          -> Getting (Map Label a) (AEvtType phase) (Map Label a) 
          -> Getter phase [Map Label a]
evtSplits union eid ln = to $ \m -> readGraph (m^.pEventRef) $ do
        rs <- NE.toList <$> (successors =<< leftVertex (Right eid))
        rs <- forM rs $ \v -> do
            r <- union <$> (view ln <$> leftInfo (G.source v)) 
                       <*> (view ln <$> rightInfo (G.target v))
            eid <- leftKey $ G.source v
            return $ r <$ eid
        return $ rights rs

evtSplitConcrete :: (HasMachineP1 phase,AEvtType phase ~ CEvtType phase,Pre)
                 => EventId
                 -> Getting (Map Label a) (AEvtType phase) (Map Label a)
                 -> Getter phase [Map Label a]
evtSplitConcrete = evtSplits $ flip const
evtSplitAdded :: (HasMachineP1 phase,AEvtType phase ~ CEvtType phase,Pre)
              => EventId
              -> Getting (Map Label a) (AEvtType phase) (Map Label a)
              -> Getter phase [Map Label a]
evtSplitAdded = evtSplits $ flip M.difference
evtSplitDel :: (HasMachineP1 phase,AEvtType phase ~ CEvtType phase,Pre)
            => EventId
            -> Getting (Map Label a) (AEvtType phase) (Map Label a)
            -> Getter phase [Map Label a]
evtSplitDel = evtSplits M.difference
evtSplitKept :: (HasMachineP1 phase,AEvtType phase ~ CEvtType phase,Pre)
             => EventId
             -> Getting (Map Label a) (AEvtType phase) (Map Label a)
             -> Getter phase [Map Label a]
evtSplitKept = evtSplits M.intersection

newDelVars :: HasMachineP2 phase
           => Getter phase (Map Name Var)
newDelVars = to $ \x -> view pAbstractVars x `M.difference` view pStateVars x

pDefVars :: HasTheoryP2 phase
         => Getter phase (Map Name Var)
pDefVars = to $ \x -> M.mapMaybe defToVar $ x^.pDefinitions

defToVar :: Def -> Maybe Var
defToVar (Def _ n [] t _) = Just (Var n t)
defToVar (Def _ _ (_:_) _ _) = Nothing

pAllVars :: HasMachineP2' phase
         => Getter (phase ae ce t) (Map Name Var)
pAllVars = to $ \x -> view pAbstractVars x `M.union` view pStateVars x

pEventSplit' :: (HasMachineP1 phase)
             => Getter phase (Map EventId (AEvtType phase,[(EventId,CEvtType phase)]))
pEventSplit' = pEventRef . to f
    where
        f g = readGraph g $ do
            vs <- getLeftVertices
            fmap (M.fromList.rights) $ forM vs $ \v -> do
                es' <- (fmap G.target <$> successors v )
                    >>= T.mapM (\v -> view distrLeft <$> liftA2 (,) (rightKey v) (rightInfo v) )
                let es = rights $ NE.toList es'
                k  <- leftKey v
                e  <- leftInfo v
                return $ (k,(e,es))^.distrLeft

pEventSplit :: (HasMachineP1 phase)
            => Getter phase (Map EventId (AEvtType phase,[EventId]))
pEventSplit = pEventSplit'.to (over (traverse._2.traverse) fst)

pEventMerge :: (HasMachineP1 phase)
            => Getter phase (Map EventId (CEvtType phase,[EventId]))
pEventMerge = pEventMerge'.to (over (traverse._2.traverse) fst)

pEventMerge' :: (HasMachineP1 phase)
             => Getter phase (Map EventId (CEvtType phase,[(EventId,AEvtType phase)]))
pEventMerge' = pEventRef.to f
    where
        f g = readGraph g $ do
            vs <- getRightVertices
            fmap (M.fromList.rights) $ forM vs $ \v -> do
                es' <- (fmap G.source <$> predecessors v )
                    >>= T.mapM (\v -> view distrLeft <$> ((,) <$> leftKey v <*> leftInfo v) )
                let es = rights $ NE.toList es'
                k  <- rightKey v
                e  <- rightInfo v
                return $ (k,(e,es))^.distrLeft

traverseFilter :: Ord k => (a -> Bool) -> Traversal' (Map k a) (Map k a)
traverseFilter p f m = M.union <$> f m' <*> pure (m `M.difference` m')
    where
        m' = M.filter p m

pNewEvents :: (HasMachineP1 phase)
           => Traversal' phase (CEvtType phase)
pNewEvents f = (pEventRef.traverseRightWithEdges) g
    where
        g (e,xs) 
            | L.null $ rights (NE.toList xs) = f e
            | otherwise                      = pure e

-- | Concrete events that are inherited from refined machine
pOldEvents :: (HasMachineP1 phase)
           => Getter phase (Map EventId (CEvtType phase))
pOldEvents = pEventMerge.to (M.map fst . M.filter (not . L.null . snd))

pEvents :: (HasMachineP1 phase) 
        => Getter phase (Map EventId (CEvtType phase))
pEvents = pEventRef.to rightMap.to f
    where
        f = M.fromList . MM.mapMaybe (rightToMaybe . (runKleisli $ first $ Kleisli id))
                       . M.toList

pEventId :: Iso' (Map Label event) (Map EventId event)
pEventId = iso 
        (M.mapKeys EventId) 
        (M.mapKeys as_label)

pIndices  :: HasMachineP2 mch
          => Getter mch (Map EventId (Map Name Var))
pIndices = pEvents . onMap eIndices

get_event :: (HasMachineP1 phase,MonadReader LineInfo m,MonadError [Error] m) 
          => phase -> Label -> m EventId
get_event p2 ev_lbl = do
        let evts = p2^.pEventIds
        bind
            ([s|event '%s' is undeclared|] $ pretty ev_lbl)
            $ ev_lbl `M.lookup` evts

get_abstract_event :: HasMachineP1 phase => phase -> EventId -> M EventId
get_abstract_event p2 ev_lbl = do
        let evts = p2^.pEventSplit & M.mapKeys as_label . M.mapWithKey const
        bind
            ([s|event '%s' is undeclared|] $ pretty ev_lbl)
            $ as_label ev_lbl `M.lookup` evts

get_concrete_event :: HasMachineP1 phase => phase -> EventId -> M EventId
get_concrete_event p2 ev_lbl = do
        let evts = p2^.pEventMerge & M.mapKeys as_label . M.mapWithKey const
        bind
            ([s|event '%s' is undeclared|] $ pretty ev_lbl)
            $ as_label ev_lbl `M.lookup` evts

get_events :: ( Traversable f
              , MonadReader r m
              , Syntactic r
              , HasMachineP2 mch
              , MonadError [Error] m)
           => mch -> f Label -> m (f EventId)
get_events p2 ev_lbl = do
            let evts = p2^.pEventIds
            bind_all ev_lbl
                ([s|event '%s' is undeclared|] . pretty)
                $ (`M.lookup` evts)

--pParams   :: HasMachineP2 mch
--          => Getter mch (Map EventId (Map String Var))
--pParams = pEvents . onMap eParams
pSchSynt  :: HasMachineP2 mch 
          => Getter mch (Map EventId ParserSetting)    
    -- parsing schedule
pSchSynt = pEvents . onMap eSchSynt
pEvtSynt  :: HasMachineP2 mch 
          => Getter mch (Map EventId ParserSetting)    
    -- parsing guards and actions
pEvtSynt = pEvents . onMap eEvtSynt

eIndParams :: HasEventP2 events => Getter events (Map Name Var) 
eIndParams = to $ \e -> (e^.eParams) `M.union` (e^.eIndices)

pEventRenaming :: HasMachineP1 mch
               => Getter mch (Map EventId [EventId])
pEventRenaming = pEventRef . to (g . f) 
    where
        g :: Map SkipOrEvent (NonEmpty SkipOrEvent)
          -> Map EventId [EventId]
        g = asListWith const %~ MM.mapMaybe (\(x,y) -> rightToMaybe $ (,) <$> x <*> y)
                                   . L.map (second $ sequence . NE.toList)
        f g = readGraph g $ do
            vs <- getLeftVertices
            fmap (M.fromListWith (<>)) $ forM vs $ \v -> do
                (,) <$> leftKey v 
                    <*> (T.mapM (rightKey . G.target) =<< successors v)

class ( IsMachine p
      , HasMachineP1' (MchType p)
      , HasEventP1 (AEvtType p)
      , HasEventP1 (CEvtType p)
      , HasTheoryP1 (ThyType p) ) 
    => HasMachineP1 p where

instance ( IsMachine p
         , HasMachineP1' (MchType p)
         , HasEventP1 (AEvtType p)
         , HasEventP1 (CEvtType p)
         , HasTheoryP1 (ThyType p) ) => HasMachineP1 p where

class ( IsMachine p
      , HasMachineP2' (MchType p)
      , HasEventP2 (AEvtType p)
      , HasEventP2 (CEvtType p)
      , HasTheoryP2 (ThyType p) 
      , HasMachineP1 p
      ) => HasMachineP2 p where

instance ( IsMachine p
          , HasMachineP1 p
          , HasMachineP2' (MchType p)
          , HasEventP2  (AEvtType p)
          , HasEventP2  (CEvtType p)
          , HasTheoryP2 (ThyType p) ) 
    => HasMachineP2 p where

class ( IsMachine p
      , HasMachineP3' (MchType p)
      , HasEventP3 (AEvtType p)
      , HasEventP3 (CEvtType p)
      , HasTheoryP3 (ThyType p) ) 
    => HasMachineP3 p where

instance ( IsMachine p
          , HasMachineP3' (MchType p)
          , HasEventP3 (AEvtType p)
          , HasEventP3 (CEvtType p)
          , HasTheoryP3 (ThyType p) ) 
    => HasMachineP3 p where

class ( IsMachine p
      , HasMachineP4' (MchType p)
      , HasEventP4 (AEvtType p)
      , HasEventP3 (CEvtType p)
      , HasTheoryP3 (ThyType p) ) => HasMachineP4 p where

instance ( IsMachine p
          , HasMachineP4' (MchType p)
          , HasEventP4 (AEvtType p)
          , HasEventP3 (CEvtType p)
          , HasTheoryP3 (ThyType p) ) 
    => HasMachineP4 p where

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
inheritWith' decl inh (++) (Hierarchy _xs es) m = m2 -- _ $ L.foldl' f (M.map decl m) xs
    where
        m1 = M.map decl m
        prec k = do
            p <- M.lookup k es 
            inh k <$> p `M.lookup` m2
        m2 = M.mapWithKey (\k c -> maybe c (c ++) (prec k)) m1

inheritWithAlt :: Ord k 
             => (base -> conc) 
             -> (k -> conc -> abstr)
             -> (conc -> abstr -> conc)
             -> Hierarchy k 
             -> Map k base -> Map k conc
inheritWithAlt decl inh (++) (Hierarchy xs es) m = L.foldl' f (M.map decl m) xs
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

instance (Ord a,Hashable a,Arbitrary a) => Arbitrary (Hierarchy a) where
    arbitrary = do
        xs <- L.nub <$> arbitrary
        let ms = M.fromList ys :: Map Int a
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
            lis :: Map MachineId LineInfo
            lis = M.map snd es'
            cs = cycles $ M.toList es
        vs <- triggerM =<< sequence <$> mapM (cycl_err_msg lis) cs
        return $ Hierarchy vs es
    where
        struct = "refinement structure" :: String
        cycle_msg = msg struct
        cycl_err_msg :: MonadWriter [Error] m 
                     => Map MachineId LineInfo 
                     -> SCC MachineId -> m (Maybe MachineId)
        cycl_err_msg _ (AcyclicSCC v) = return $ Just v
        cycl_err_msg lis (CyclicSCC vs) = do
            tell [MLError cycle_msg $ nonEmpty'
                $ L.map (first pretty) $ M.toList
                $ lis `M.intersection` fromList' vs ] 
            return Nothing -- (error "topological_order")
        msg = [s|A cycle exists in the %s|]

fromList' :: Ord a => [a] -> Map a ()
fromList' xs = M.fromList $ L.zip xs $ L.repeat ()

inherit :: Hierarchy MachineId -> Map MachineId [b] -> Map MachineId [b]
inherit = inheritWith id id (++)

inherit2 :: (Scope s,HasMachineP1 phase)
         => MMap (phase)
         -> Hierarchy MachineId
         -> MMap [(t, s)] 
         -> MMap [(t, s)]
inherit2 phase = inheritWith'
            id
            (\m -> concatMap $ second' (make_inherited' >=> rename_events (names ! m)))
            (++)
    where
        names = M.map (view pEventRenaming) phase
        make_inherited' = MM.maybeToList . make_inherited
        _ = MM.mapMaybe :: (a -> Maybe a) -> [a] -> [a]

second' :: Monad m => (a -> m b) -> (d, a) -> m (d, b)
second' = runKleisli . second . Kleisli

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

type MPipeline ph a = Pipeline MM (MMap ph) (Maybe (MMap a))

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
               , MonadFix f)
            => (thy0 -> thy1 -> f thy1)
            -> (mch0 aevt0 cevt0 thy1 -> mch1 aevt0 cevt0 thy1 -> f (mch1 aevt0 cevt0 thy1))
            -> (mch1 aevt0 cevt0 thy1 -> SkipOrEvent -> aevt0 -> aevt1 -> f aevt1)
            -> (mch1 aevt0 cevt0 thy1 -> SkipOrEvent -> cevt0 -> cevt1 -> f cevt1)
            -> mch0 aevt0 cevt0 thy0 -> f (mch1 aevt1 cevt1 thy1)
layeredUpgradeRecM thyF mchF oldEvF newEvF = layeredUpgradeM
        (mfix.thyF) 
        (mfix.mchF) 
        (fmap (fmap mfix).oldEvF)
        (fmap (fmap mfix).newEvF)

layeredUpgradeM :: ( HasMachineP1' mch1, HasMachineP1' mch0
            , Monad f)
         => (thy0 -> f thy1)
         -> (mch0 aevt0 cevt0 thy1 -> f (mch1 aevt0 cevt0 thy1))
         -> (mch1 aevt0 cevt0 thy1 -> SkipOrEvent -> aevt0 -> f aevt1)
         -> (mch1 aevt0 cevt0 thy1 -> SkipOrEvent -> cevt0 -> f cevt1)
         -> mch0 aevt0 cevt0 thy0 -> f (mch1 aevt1 cevt1 thy1)
layeredUpgradeM thyF mchF oldEvF newEvF m = do
        m' <- mchF =<< (m & pContext thyF)
        m' & pEventRef (\g -> acrossBothWithKey 
                        (oldEvF m')
                        (newEvF m') 
                        pure g)

layeredUpgradeRec :: (HasMachineP1' mch1, HasMachineP1' mch0)
           => (thy0 -> thy1 -> thy1)
           -> (mch0 aevt0 cevt0 thy1 -> mch1 aevt0 cevt0 thy1 -> mch1 aevt0 cevt0 thy1)
           -> (mch1 aevt0 cevt0 thy1 -> SkipOrEvent -> aevt0 -> aevt1 -> aevt1)
           -> (mch1 aevt0 cevt0 thy1 -> SkipOrEvent -> cevt0 -> cevt1 -> cevt1)
           -> mch0 aevt0 cevt0 thy0 -> mch1 aevt1 cevt1 thy1
layeredUpgradeRec thyF mchF oldEvF newEvF = layeredUpgrade
        (fix.thyF) 
        (fix.mchF) 
        (fmap (fmap fix).oldEvF)
        (fmap (fmap fix).newEvF)

layeredUpgrade :: (HasMachineP1' mch1, HasMachineP1' mch0)
        => (thy0 -> thy1)
        -> (mch0 aevt0 cevt0 thy1 -> mch1 aevt0 cevt0 thy1)
        -> (mch1 aevt0 cevt0 thy1 -> SkipOrEvent -> aevt0 -> aevt1)
        -> (mch1 aevt0 cevt0 thy1 -> SkipOrEvent -> cevt0 -> cevt1)
        -> mch0 aevt0 cevt0 thy0 -> mch1 aevt1 cevt1 thy1
layeredUpgrade thyF mchF oldEvF newEvF = runIdentity . layeredUpgradeM
        (Identity . thyF) (Identity . mchF) 
        (fmap (fmap Identity) . oldEvF)
        (fmap (fmap Identity) . newEvF)

upgradeM :: ( HasMachineP1' mch1, HasMachineP1' mch0
            , Monad f)
         => (thy0 -> f thy1)
         -> (mch0 aevt0 cevt0 thy0 -> f (mch1 aevt0 cevt0 thy0))
         -> (mch0 aevt0 cevt0 thy0 -> SkipOrEvent -> aevt0 -> f aevt1)
         -> (mch0 aevt0 cevt0 thy0 -> SkipOrEvent -> cevt0 -> f cevt1)
         -> mch0 aevt0 cevt0 thy0 -> f (mch1 aevt1 cevt1 thy1)
upgradeM thyF mchF oldEvF newEvF m = do
        m' <- pContext thyF =<< mchF m
        m' & pEventRef (\g -> acrossBothWithKey
                         (oldEvF m)
                         (newEvF m) 
                         pure g)

upgrade :: (HasMachineP1' mch1, HasMachineP1' mch0)
        => (thy0 -> thy1)
        -> (mch0 aevt0 cevt0 thy0 -> mch1 aevt0 cevt0 thy0)
        -> (mch0 aevt0 cevt0 thy0 -> SkipOrEvent -> aevt0 -> aevt1)
        -> (mch0 aevt0 cevt0 thy0 -> SkipOrEvent -> cevt0 -> cevt1)
        -> mch0 aevt0 cevt0 thy0 -> mch1 aevt1 cevt1 thy1
upgrade thyF mchF oldEvF newEvF = runIdentity . upgradeM
        (Identity . thyF) (Identity . mchF) 
        (fmap (fmap Identity) . oldEvF)
        (fmap (fmap Identity) . newEvF)
