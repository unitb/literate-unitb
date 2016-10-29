{-# LANGUAGE Arrows
        , TypeOperators
        , RecordWildCards
        , OverloadedStrings
        #-}
module Document.Phase.Structures where

    --
    -- Modules
    --
import Document.Pipeline
import Document.Phase as P
import Document.Phase.Parameters
import Document.Phase.Types
import Document.Scope

import Logic.Expr

import UnitB.Syntax as AST

import Logic.Theories

    --
    -- Libraries
    --
import Control.Arrow hiding (left,app) -- (Arrow,arr,(>>>))
import Control.Lens as L hiding ((|>),(<.>),(<|),indices,Context)

import           Control.Monad 
import           Control.Monad.Except
import           Control.Monad.Reader.Class 

import qualified Data.Graph.Bipartite as G
import           Data.List as L hiding ( union, insert, inits )
import           Data.Map   as M hiding ( map, (\\) )
import qualified Data.Map   as M

import Text.Printf.TH

import Utilities.Syntactic

run_phase0_blocks :: Pipeline MM () (MMap MachineP0)
run_phase0_blocks = withInput $ proc doc -> do
                let mch = M.map (const ()) $ getMachineInput doc
                    _ctx = M.map (const ()) $ getContextInput doc
                    m0 = M.mapWithKey (const . MachineP0 mch) mch
                    _c0 = M.map (const $ TheoryP0 ()) _ctx    
                returnA -< m0

run_phase1_types :: Pipeline MM (MMap MachineP0) SystemP1
run_phase1_types = proc p0 -> do
    ts <- set_decl      -< p0
    e <- arr (fmap $ unionsWith (++)) <<< run_phase 
        [ event_splitting
        , event_decl
        , event_merging  ] -< p0
    r  <- refines_mch   -< p0
    verifSet <- verif_setting_mch   -< p0
    it <- import_theory -< p0
    refs <- triggerP <<< liftP' (make_all_tables refClash) -< r
    verifSet' <- triggerP <<< liftP' (make_all_tables verifClash) -< verifSet
    let _ = refs :: MMap (Map () (MachineId,LineInfo))
    r_ord <- topological_order -< mapMaybe (M.lookup ()) refs
    let t = M.map fst <$> ts
        s = M.map snd <$> ts
        -- f = _ :: Int
    evts' <- liftP' $ make_all_tables evtClash  -< inheritEvents r_ord <$> e
    types <- liftP' $ make_all_tables setClash  -< inherit r_ord  <$> t
    imp_th <- liftP' $ make_all_tables thyClash -< inherit r_ord  <$> it
    let f m = G.fromList 
                (leftVerts m) (rightVerts m)
                (edges m)                 
        leftVerts m = concatMap (L.map (,()).snd) m
        rightVerts m = L.map ((,()).fst) m
        edges m = concatMap (\(x,xs) -> L.map (,x) xs) m
        makeGraphs = traverse f 
    evts'   <- triggerP -< evts'   
    let evts'' :: MMap [(SkipOrEvent, [SkipOrEvent])]
        evts'' = addSkip evts'
        addSkip = M.map (((Left SkipEvent,[Left SkipEvent]):).M.elems.M.map ((Right *** ifEmpty).fst))
        ifEmpty [] = [Left SkipEvent]
        ifEmpty xs = L.map Right xs
    evts'   <- triggerP -< makeGraphs evts''
    -- let _ = _
    types   <- triggerP -< types
    imp_th' <- triggerP -< imp_th
    s       <- triggerP -< s
    --     -- BIG FLAG
    --     -- the creation of p1 won't detect clashes between type names, it will merely overshadow
    --     -- some types with (hopefully) the most local types
    --     -- BIG FLAG
    let _ = evts' :: MMap (G.BiGraph SkipOrEvent () ())
        f th = M.unions $ map (view AST.types) $ M.elems th
        basic = preludeTheories
        imp_th = M.map (union basic . M.map fst) imp_th'
        all_types = M.intersectionWith (\ts th -> M.map fst ts `union` f th) types imp_th
        p1 = make_phase1 <$> p0 <.> imp_th 
                         <.> (M.map (M.map fst) types) 
                         <.> all_types 
                         <.> (verifSet' & traverse.traverse %~ fst)
                         <.> s <.> evts'
    returnA -< SystemP r_ord p1
  where
    evtClash = [s|Multiple events with the name %s|] . pretty
    setClash = [s|Multiple sets with the name %s|] . render
    thyClash _   = "Theory imported multiple times"
    refClash _   = "Multiple refinement clauses"
    verifClash _ = "Multiple verification timeouts"

make_phase1 :: MachineP0
            -> Map Name Theory
            -> Map Name Sort
            -> Map Name Sort
            -> Map () Float
            -> [(Name, PostponedDef)]
            -> G.BiGraph SkipOrEvent () () -- Map Label (EventId, [EventId])
            -> MachineP1
make_phase1 _p0 _pImports _pTypes _pAllTypes  
        timeout _pSetDecl evts = MachineP1 { .. }
    where
        _pEventRef = G.mapBothWithKey (const.EventP1) (const.EventP1) evts
        _pContext    = TheoryP1 { .. }
        _t0          = TheoryP0 ()
        _pVerTimeOut = M.findWithDefault 1 () timeout

set_decl :: MPipeline MachineP0 
            ( [(Name,Sort,LineInfo)]
            , [(Name,PostponedDef)] )
set_decl = machineCmd "\\newset" $ \(Identity (SetName tag)) _m _ -> do
            let name     = tag 
                new_sort = Sort tag (asInternal name) 0
                new_type = Gen new_sort []
                new_def = makeDef [] name [] (set_type new_type)
                                    $ zlift (set_type new_type) ztrue
            li <- ask
            return ([(tag,new_sort,li)],[(tag,(new_def,Local,li))])

event_splitting :: MPipeline MachineP0 [(Label, (EventId,[EventId]), LineInfo)]
event_splitting = machineCmd "\\splitevent" $ \(Abs aevt, cevts) _m _p0 -> do
    let _ = aevt  :: EventId
        _ = cevts :: [Conc EventId]
    li <- ask
    when (any (Conc "skip" ==) cevts) $ do
        throwError [Error "invalid event name: 'skip' is a reserved name" li]
    return [(as_label c,(c,[aevt]),li) | Conc c <- cevts]

event_merging :: MPipeline MachineP0 [(Label, (EventId,[EventId]), LineInfo)]
event_merging = machineCmd "\\mergeevents" $ \(aevts, Conc cevt) _m _p0 -> do
    let _ = aevts :: [Abs EventId]
        _ = cevt  :: EventId
    li <- ask
    when (cevt == "skip") $ do
        throwError [Error "invalid event name: 'skip' is a reserved name" li]
    return [(as_label cevt,(cevt,map getAbstract aevts),li)]

event_decl :: MPipeline MachineP0 [(Label, (EventId,[EventId]), LineInfo)]
event_decl = machineCmd "\\newevent" $ \(Identity (Conc evt)) _m _ -> do 
            li <- ask 
            when (evt == "skip") $ do
                throwError [Error "invalid event name: 'skip' is a reserved name" li]
            return [(as_label evt,(evt,[]),li)]

verif_setting_mch :: MPipeline MachineP0 [((), Float, LineInfo)]
verif_setting_mch = machineCmd "\\setTimeout" $ \(Identity (Factor to)) _cmch (MachineP0 _ms _) -> do
            li <- ask
            return [((),to,li)]

refines_mch :: MPipeline MachineP0 [((), MachineId, LineInfo)]
refines_mch = machineCmd "\\refines" $ \(Identity amch) cmch (MachineP0 ms _) -> do
            li <- ask
            unless (amch `M.member` ms) 
                $ throwError [Error ([s|Machine %s refines a non-existant machine: %s|] (pretty cmch) (pretty amch)) li]
                -- check that mch is a machine
            return [((),amch,li)]

import_theory :: MPipeline MachineP0 [(Name, Theory, LineInfo)]
import_theory = machineCmd "\\with" $ \(Identity (TheoryName th_name)) _m _ -> do
        let th = supportedTheories
            msg = [s|Undefined theory: %s |]
                -- add suggestions
        li <- ask
        case th_name `M.lookup` th of
            Nothing -> throwError [Error (msg $ render th_name) li]
            Just th -> return [(th_name,th,li)]
