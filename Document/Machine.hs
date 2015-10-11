{-# LANGUAGE RecursiveDo, LambdaCase #-}
{-# LANGUAGE BangPatterns, FlexibleContexts     #-}
{-# LANGUAGE TupleSections, ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances, Arrows          #-}
{-# LANGUAGE TypeOperators, TypeFamilies        #-}
{-# LANGUAGE MultiParamTypeClasses              #-}
{-# LANGUAGE TemplateHaskell, OverloadedStrings #-}
{-# LANGUAGE RecordWildCards, RankNTypes        #-}
module Document.Machine where

    --
    -- Modules
    --
import Document.ExprScope as ES
import Document.Pipeline
import Document.Phase as P
import Document.Refinement as Ref
import Document.Scope
import Document.Visitor


import Logic.Expr
import Logic.Proof.Tactics hiding ( with_line_info )

import UnitB.AST as AST
import UnitB.PO


    --
    -- Libraries
    --
import Control.Arrow hiding (left,app) -- (Arrow,arr,(>>>))
import           Control.Applicative 

import           Control.Monad 
import           Control.Monad.Trans.RWS as RWS ( RWS )

import Control.Lens as L hiding ((|>),(<.>),(<|),indices,Context)

import           Data.Map   as M hiding ( map, foldl, (\\) )
import qualified Data.Map   as M
import qualified Data.Maybe as MM
import           Data.Monoid
import           Data.List as L hiding ( union, insert, inits )
import           Data.List.NonEmpty ( NonEmpty(..) )
import qualified Data.List.NonEmpty as NE

import qualified Utilities.BipartiteGraph as G
import Utilities.Format
import Utilities.Syntactic
        


make_machine :: MachineId -> MachineP4
             -> MM' c Machine
make_machine (MId m) p4 = mch'
    where
        types   = p4 ^. pTypes
        -- evtSet  = p4 ^. pEvents
        imp_th  = p4 ^. pImports
        ref_prog :: Map Label Rule
        ref_prog = M.mapKeys as_label $ p4 ^. pLiveRule
        proofs   = p4 ^. pProofs
        -- _ = evt_refs :: Map EventId [(Label,ScheduleChange,LineInfo)]
        ab_var = p4 ^. pAbstractVars
        ctx = empty_theory 
            { _extends  = imp_th
            , _types    = types
            , _funs = M.empty
            , _defs = p4 ^. pDefinitions
            , _consts   = p4 ^. pConstants
            , _theorems = M.empty
            , _thm_depend = []
            , _theoryDummies = p4^.pDummyVars
            -- , notation =  empty_notation
            , _fact = p4^.pAssumptions & traverse %~ getExpr }
        props = p4 ^. pNewPropSet
        mch = Mch 
            { _machine'Name = m
            , _theory = ctx
            , _variables = p4 ^. pStateVars
            , _abs_vars  = ab_var
            , _del_vars  = M.map fst $ p4 ^. pDelVars
            , _init_witness = p4 ^. pInitWitness
            , _del_inits = p4 ^. pDelInits
            , _inits = p4 ^. pInit
            , _props = props 
            , _derivation = (ref_prog 
                    `union` M.map (const $ Rule Add) (_progress props)) 
            , _inh_props = p4 ^. pOldPropSet
            , _comments  = p4 ^. pComments
            , _event_table = EventTable evts -- M.mapKeys as_label evts 
                -- adep: in a abstract machine, prog_a <- evt_a
                -- live: in a concrete machine, prog_c <- prog_c
                -- cdep:                        prog_c <- evt_c
                -- eref: in a refinement, evt_a <- evt_c
                -- pref_a:                evt_a <- prog_a
                -- pref_c:                evt_a <- prog_c
                --   adep;eref \/ (live\/id);cdep
                --   (adep;pref_a)+ /\ id ⊆ {}

                -- = (live;adep \/ adep) ; eref \/ cdep
            -- , prog_evt = _ 
            } -- R.mapDomain getConcrete cdep' }
        mch' :: MM' c Machine
        mch' = do
            let pos = raw_machine_pos mch
                po_err = proofs `difference` pos
            all_errors $ flip map (toList po_err) $ \(lbl,(_,li)) -> 
                Left [Error (format "proof obligation does not exist: {0}" lbl) li]
            xs <- all_errors $ flip map (toList proofs) $ \(k,(tac,li)) -> do
                p <- runTactic li (pos ! k) tac
                return (k,p)
            xs <- triggerM xs
            return $ mch & AST.props.AST.proofs .~ fromList xs
        events = p4 ^. pEventRef
        evts = events & G.traverseLeft %~ abstrEvt
                      -- & G.traverseRight %~ g
                      & G.traverseRightWithEdgeInfo %~ uncurry concrEvt
        abstrEvt :: EventP4 -> AbstrEvent
        abstrEvt evt = AbsEvent
                { _old = g evt 
                , _c_sched_ref = map snd (evt ^. eCoarseRef)
                , _f_sched_ref = (first as_label) <$> evt ^. eFineRef
                }
        concrEvt :: EventP4 -> NonEmpty (SkipOrEvent, AbstrEvent) -> ConcrEvent
        concrEvt evt olds = CEvent
                { _new = g evt
                , _witness   = evt ^. eWitness
                , _eql_vars = keep' ab_var oldAction
                             `M.intersection` frame (evt^.eActions)
                }
            where oldAction = snd (NE.head olds)^.actions
        g :: EventP4 -> Event
        g evt
            = Event
                { _indices   = evt^.eIndices
                , _params    = evt^.eParams
                , _guards    = evt^.eGuards
                , _actions  = evt^.eActions
                , _coarse_sched = evt^.eCoarseSched
                , _fine_sched = evt^.eFineSched
                }

uncurryMap :: (Ord a,Ord b) => Map a (Map b c) -> Map (a,b) c
uncurryMap m = fromList $ do
        (x,ys) <- toList m
        (y,z)  <- toList ys
        return ((x,y),z)

flipMap :: (Ord a, Ord b) => Map a (Map b c) -> Map b (Map a c)
flipMap m = M.map fromList $ fromListWith (++) $ do
    (x,xs) <- toList $ M.map toList m
    (y,z)  <- xs
    return (y,[(x,z)])

-- type MM = R.ReaderT Input M

class Ord k => WithMap k a m where
    type ElementOf k a m :: *
    -- type FunOf k a m :: *
    for_each :: Map k (ElementOf k a m) -> Map k a -> m

instance Ord k => WithMap k a (Map k b) where
    type ElementOf k a (Map k b) = a -> b
    -- type FunOf k a (Map k b) = Map k a
    for_each f m = M.intersectionWith id f m

instance (Monoid b, WithMap k b m) => WithMap k a (Map k b -> m) where
    type ElementOf k a (Map k b -> m) = a -> ElementOf k b m
    -- type FunOf k a (Map k b -> m) = Map k a -> FunOf k b m
    for_each f m0 m1 = M.intersectionWith id f m0 `for_each` (m1 `union` M.map (const mempty) m0)

-- trigger_errors 

type family ElementMap a :: *
type instance ElementMap (Map k ()) = ()
type instance ElementMap (Map k (x :+: xs) ) = Map k x :+: ElementMap (Map k xs)

-- type family MapOf a :: *
-- type instance MapOf [(a,b,LineInfo)] = Either [Error] (Map a b)


class ElementLists a where
    split_tables' :: Map k a -> ElementMap (Map k a)

instance ElementLists () where
    split_tables' _ = ()

instance ElementLists as => ElementLists (a:+:as) where
    split_tables' m = M.map f m :+: split_tables' (M.map g m)
        where
            f (x :+: _) = x
            g (_ :+: xs) = xs

    -- Todo: detect when the same variable is declared twice
    -- in the same declaration block.


progress_props :: MachineP3 -> Map ProgId ProgressProp
progress_props p3 = p3 ^. pProgress

type OneOrTwo a = Either (a,a) a

fieldA :: Lens' (OneOrTwo a) a
fieldA f (Left x) = Left <$> _1 f x
fieldA f (Right x) = (Left . (,x)) <$> f x

fieldB :: Lens' (OneOrTwo a) a
fieldB f (Left x) = Left <$> _2 f x
fieldB f (Right x) = (Left . (x,)) <$> f x

parseEvtExprChoice :: ( HasInhStatus decl (InhStatus expr)
                      , HasDeclSource decl DeclSource 
                      , Ord label)
              => Lens' MachineP3 (Map EventId (Map label expr))
              -> Lens' MachineP3 (Map EventId (Map label expr))
              -> ((Label,decl) -> label)
              -> [(Maybe EventId, [(Label, decl)])]
              -> RWS () [Error] MachineP3 ()
parseEvtExprChoice oldLn newLn f = parseEvtExprChoice' oldLn newLn newLn f

parseEvtExprChoice' :: ( HasInhStatus decl (InhStatus expr)
                      , HasDeclSource decl DeclSource 
                      , Ord label)
              => Lens' MachineP3 (Map EventId (Map label expr))
              -> Lens' MachineP3 (Map EventId (Map label expr))
              -> Lens' MachineP3 (Map EventId (Map label expr))
              -> ((Label,decl) -> label)
              -> [(Maybe EventId, [(Label, decl)])]
              -> RWS () [Error] MachineP3 ()
parseEvtExprChoice' oldLn delLn newLn = parseEvtExprChoiceImp 
        (Just (LensT oldLn)) 
        (Just (LensT delLn))
        (Just (LensT newLn))

parseEvtExprChoiceImp :: ( HasInhStatus decl (InhStatus expr)
                         , HasDeclSource decl DeclSource 
                         , Ord label)
              => Maybe (LensT MachineP3 (Map EventId (Map label expr)))
              -> Maybe (LensT MachineP3 (Map EventId (Map label expr)))
              -> Maybe (LensT MachineP3 (Map EventId (Map label expr)))
              -> ((Label,decl) -> label)
              -> [(Maybe EventId, [(Label, decl)])]
              -> RWS () [Error] MachineP3 ()
parseEvtExprChoiceImp oldLn delLn newLn f xs = do
    let route (Just k) x@(_,decl) = case (decl ^. inhStatus, decl ^. declSource) of
                                (InhAdd _, Inherited) -> ([(k,[x])],[],[(k,[x])])
                                (InhAdd _, Local)     -> ([],[],[(k,[x])])
                                (InhDelete _, Inherited) -> ([],[],[])
                                (InhDelete _, Local)     -> ([(k,[x])],[(k,[x])],[])
        route Nothing _ = ([],[],[])
        -- is_new _ = True
        (old_xs, del_xs, new_xs) = mconcat $ L.map (uncurry $ \k -> mconcat . map (route k)) xs
        getLabelExpr = runKleisli $ arr f &&& Kleisli (contents . snd)
        g        = L.map (second $ MM.mapMaybe getLabelExpr)
            -- arr (map $ f &&& (view evtExpr . snd)))
        assign ln f = maybe (return ()) (\(LensT ln) -> ln %= f) ln
    oldLn `assign` doubleUnion (g old_xs)
    delLn `assign` doubleUnion (g del_xs)
    newLn `assign` doubleUnion (g new_xs)

doubleUnion :: (Ord k0,Ord k1)
            => [(k0,[(k1,a)])]
            -> Map k0 (Map k1 a)
            -> Map k0 (Map k1 a)
doubleUnion xs = M.unionWith M.union (M.map M.fromList $ M.fromListWith (++) xs)


parseEvtExprDefault :: (HasEvtExpr decl expr, Ord label)
              => Lens' MachineP3 (Map EventId (Map label expr))
              -> ((Label,decl) -> label)
              -> [(Maybe EventId, [(Label, decl)])]
              -> RWS () [Error] MachineP3 ()
parseEvtExprDefault ln f xs = do
    let toEntry = f &&& (view evtExpr . snd)
        xs'  = MM.mapMaybe (runKleisli $ Kleisli id *** arr (map toEntry)) xs
        xs'' = M.map M.fromList $ M.fromListWith (++) xs'
    ln %= flip (M.unionWith M.union) xs''

parseInitExpr :: (HasEvtExpr decl expr, Ord label)
              => Lens' MachineP3 (Map label expr)
              -> ((Label,decl) -> label)
              -> [(Maybe EventId, [(Label, decl)])]
              -> RWS () [Error] MachineP3 ()
parseInitExpr ln f xs = do

    let toEntry = f &&& (view evtExpr . snd)
        ys' = concat $ MM.mapMaybe (\(x,y) -> guard (MM.isNothing x) >> return (map toEntry y)) xs
    ln %= M.union (M.fromList ys')

mapA :: Monad m => Kleisli m b c -> Kleisli m [b] [c]
mapA (Kleisli m) = Kleisli $ mapM m

modifyProps :: ( HasMchExpr b a, HasDeclSource b DeclSource
               , Scope b
               , Show a)
            => Lens' PropertySet (Map Label a)
            -> [(Label,b)]
            -> RWS () [Error] MachineP3 ()
modifyProps ln xs = do
    let 
        xs' = L.partition ((== Local) . view declSource . snd) xs
        (ys',zs') = (both `over` L.map (second $ view mchExpr)) xs'
    pNewPropSet.ln %= M.union (M.fromList ys')
    pOldPropSet.ln %= M.union (M.fromList zs')
