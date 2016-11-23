{-# LANGUAGE RecursiveDo, LambdaCase #-}
{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Arrows              #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE TypeOperators, TypeFamilies        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
module Document.Machine where

    --
    -- Modules
    --
import Document.ExprScope as ES
import Document.Pipeline
import Document.Phase.Types
import Document.Refinement as Ref
import Document.Scope

import Logic.Expr

import UnitB.UnitB
import UnitB.Expr

    --
    -- Libraries
    --
import Control.Arrow hiding (left,app) -- (Arrow,arr,(>>>))

import           Control.Monad 
import           Control.Monad.Trans.RWS as RWS ( RWS )

import Control.Lens as L hiding ((|>),(<.>),(<|),indices,Context)
import Control.Lens.Misc 

import qualified Data.Graph.Bipartite as G
import           Data.List as L hiding ( union, insert, inits )
import qualified Data.List.NonEmpty as NE
import           Data.Map   as M hiding ( map, (\\) )
import qualified Data.Map   as M
import qualified Data.Maybe as MM
import           Data.Semigroup

import Text.Printf.TH

import Utilities.Syntactic

make_machine :: MachineId -> MachineP4
             -> MM' c Machine
make_machine (MId m) p4 = mch'
    where
        types   = p4^.pTypes
        imp_th  = p4^.pImports
        ref_prog :: Map ProgId Rule
        ref_prog = p4^.pLiveRule
        proofs   = p4^.pProofs
        ctx = (empty_theory m)
            { _extends  = imp_th
            , _types    = types
            , _funs = M.empty
            , _theory'Defs = p4^.pDefinitions
            , _consts   = p4^.pConstants
            , _theorems = M.empty
            , _thm_depend = []
            , _theory'Dummies = p4^.pDummyVars
            , _fact = p4^.pAssumptions }
        mch = do
          es <- evts
          return $ newMachine m $ do
            theory .= ctx
            oldDefs .= p4^.pMchOldDef
            defs .= p4^.pMchDef
            variables .= p4^.pStateVars
            abs_vars  .= p4^.pAbstractVars
            del_vars  .= M.map fst (p4^.pDelVars)
            init_witness .= p4^.pInitWitness
            del_inits .= p4^.pDelInits
            inits .= p4^.pInit
            props .= p4^.pNewPropSet 
            derivation .= (ref_prog 
                    `union` (makeRule Add <$> (p4^.pNewPropSet.progress))) 
            inh_props .= p4^.pOldPropSet
            comments  .= p4^.pComments
            timeout   .= p4^.pVerTimeOut
            event_table .= es
                -- adep: in a abstract machine, prog_a <- evt_a
                -- live: in a concrete machine, prog_c <- prog_c
                -- cdep:                        prog_c <- evt_c
                -- eref: in a refinement, evt_a <- evt_c
                -- pref_a:                evt_a <- prog_a
                -- pref_c:                evt_a <- prog_c
                --   adep;eref \/ (live\/id);cdep
                --   (adep;pref_a)+ /\ id ⊆ {}

                -- = (live;adep \/ adep) ; eref \/ cdep
        mch' :: MM' c Machine
        mch' = do
            liftEither $ withPOs proofs =<< mch
        events = p4^.pEventRef
        evts :: Either [Error] (EventMap DispExpr)
        evts = fmap EventMap $
               events & ( G.traverseLeft (pure . abstrEvt)
                      <=< G.traverseRightWithEdgeInfo (Indexed $ uncurry . concrEvt))
        abstrEvt :: EventP4 -> AbstrEvent
        abstrEvt evt = AbsEvent
                { _old = g $ evt^.eventP3
                , _ind_witness = evt^.eIndWitness
                , _c_sched_ref = map snd (evt^.eCoarseRef)
                , _f_sched_ref = (first as_label) <$> evt^.eFineRef
                }
        concrEvt :: SkipOrEvent
                 -> EventP3 
                 -> NonEmpty (SkipOrEvent, EventP4) 
                 -> Either [Error] ConcrEvent
        concrEvt eid evt olds = do
            let n = length olds
                absEvents = intercalate "," $ (traverse %~ prettyEvent.fst) $ NE.toList olds
                missingErr e = [s|The events merged into %s (%s) do not all have an action labelled %s|] e absEvents
                oneActErr    = [s|Event %s, action %s|]
                diffActsErr  = [s|The action %s of the events merged into %s differ|]
                collapseActions :: Label
                                -> NonEmpty (SkipOrEvent, (NonEmpty LineInfo, Action))
                                -> Either [Error] Action
                collapseActions lbl acts 
                    | length acts == n && length (group $ (traverse %~ view (_2._2)) . NE.toList $ acts) == 1 
                        = Right . snd . snd $ NE.head acts
                    | length acts /= n = Left . pure
                        $ MLError ( missingErr (prettyEvent eid) (pretty lbl) ) 
                          [ (oneActErr (prettyEvent e) (pretty lbl),li)
                            | (e,(lis,_act)) <- acts, li <- lis ]
                    | otherwise        = Left . pure
                        $ MLError ( diffActsErr (pretty lbl) (prettyEvent eid) ) 
                          [ (oneActErr (prettyEvent e) (pretty lbl),li)
                              | (e,(lis,_act)) <- acts, li <- lis ]
            oldAction <- itraverseValidation collapseActions
                        $ M.unionsWith (<>) . NE.toList 
                        $ olds & mapped %~ fmap pure . uncurry (fmap . (,)) . (_2 %~ view eActions)
            let _ = oldAction :: Map Label Action
            Right $ CEvent
                { _new = g evt
                , _witness   = evt^.eWitness
                , _param_witness   = evt^.eParamWitness
                , _eql_vars  = keep' (p4^.pAbstractVars) oldAction
                                `M.intersection` frame (evt^.eActions & traverse %~ snd)
                , _abs_actions = oldAction
                }
            -- where oldAction = snd (NE.head olds)^.actions
        g :: EventP3 -> Event
        g evt
            = Event
                { _indices   = evt^.eIndices
                , _params    = evt^.eParams
                , _raw_guards    = evt^.eGuards
                , _actions  = evt^.eActions & traverse %~ snd
                , _raw_coarse_sched = Nothing
                , _fine_sched = evt^.eFineSched
                } & coarse_sched .~ evt^.eCoarseSched

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

    -- Todo: detect when the same variable is declared twice
    -- in the same declaration block.

progress_props :: MachineP3 -> Map ProgId ProgressProp
progress_props p3 = p3^.pProgress

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
        (Just (Lens oldLn)) 
        (Just (Lens delLn))
        (Just (Lens newLn))

parseEvtExprChoiceImp :: ( HasInhStatus decl (InhStatus expr)
                         , HasDeclSource decl DeclSource 
                         , Ord label)
              => Maybe (ReifiedLens' MachineP3 (Map EventId (Map label expr)))
              -> Maybe (ReifiedLens' MachineP3 (Map EventId (Map label expr)))
              -> Maybe (ReifiedLens' MachineP3 (Map EventId (Map label expr)))
              -> ((Label,decl) -> label)
              -> [(Maybe EventId, [(Label, decl)])]
              -> RWS () [Error] MachineP3 ()
parseEvtExprChoiceImp oldLn delLn newLn f xs = do
    let route (Just k) x@(_,decl) = case (decl^.inhStatus, decl^.declSource) of
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
        assign ln f = maybe (return ()) (\(Lens ln) -> ln %= f) ln
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
