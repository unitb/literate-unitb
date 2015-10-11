{-# LANGUAGE Arrows
        , TypeOperators
        , TupleSections 
        , RecordWildCards
        , OverloadedStrings
        #-}
module Document.Phase.Structures where

    --
    -- Modules
    --
import Document.Pipeline
import Document.Phase as P
import Document.Scope
import Document.Visitor

import Logic.Expr

import UnitB.AST as AST

import Theories.Arithmetic
import Theories.FunctionTheory
import Theories.IntervalTheory
import Theories.PredCalc
import Theories.RelationTheory
import Theories.SetTheory

    --
    -- Libraries
    --
import Control.Arrow hiding (left,app) -- (Arrow,arr,(>>>))
import           Control.Applicative 

import           Control.Monad 
import           Control.Monad.Reader.Class 
import           Control.Monad.Trans
import           Control.Monad.Trans.Either

import Control.Lens as L hiding ((|>),(<.>),(<|),indices,Context)

import           Data.List as L hiding ( union, insert, inits )
import           Data.Map   as M hiding ( map, foldl, (\\) )
import qualified Data.Map   as M

import qualified Utilities.BipartiteGraph as G
import Utilities.Format
import Utilities.Syntactic

run_phase0_blocks :: Pipeline MM () (MTable MachineP0)
run_phase0_blocks = withInput $ proc doc -> do
                let mch = M.map (const ()) $ getMachineInput doc
                    _ctx = M.map (const ()) $ getContextInput doc
                    m0 = M.mapWithKey (const . MachineP0 mch) mch
                    _c0 = M.map (const $ TheoryP0 ()) _ctx    
                returnA -< m0

run_phase1_types :: Pipeline MM (MTable MachineP0) SystemP1
run_phase1_types = proc p0 -> do
    ts <- set_decl      -< p0
    e <- arr (fmap $ unionsWith (++)) <<< run_phase 
        [ event_splitting
        , event_decl
        , event_merging  ] -< p0
    r  <- refines_mch   -< p0
    it <- import_theory -< p0
    refs <- triggerP <<< liftP' (make_all_tables refClash) -< r
    let _ = refs :: Map MachineId (Map () (MachineId,LineInfo))
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
    let evts'' :: MTable [(SkipOrEvent, [SkipOrEvent])]
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
    let _ = evts' :: MTable (G.BiGraph SkipOrEvent () ())
        f th = M.unions $ map (view AST.types) $ M.elems th
        basic = fromList [("arithmetic",arithmetic),("basic",basic_theory)]
        imp_th = M.map (union basic . M.map fst) imp_th'
        all_types = M.intersectionWith (\ts th -> M.map fst ts `union` f th) types imp_th
        p1 = make_phase1 <$> p0 <.> imp_th 
                         <.> (M.map (M.map fst) types) 
                         <.> all_types 
                         <.> s <.> evts'
    -- p1 <- triggerP -< p1
    returnA -< SystemP r_ord p1
  where
    evtClash = format "Multiple events with the name {0}"
    setClash = format "Multiple sets with the name {0}"
    thyClash = format "Theory imported multiple times"
    refClash = format "Multiple refinement clauses"

make_phase1 :: MachineP0
            -> Map String Theory
            -> Map String Sort
            -> Map String Sort
            -> [(String, PostponedDef)]
            -> G.BiGraph SkipOrEvent () () -- Map Label (EventId, [EventId])
            -> MachineP1
make_phase1 _p0 _pImports _pTypes _pAllTypes _pSetDecl evts = MachineP1 { .. }
        -- _pEventRef <- G.fromList _ _ 
        --     (concatMap (uncurry $ L.map.(,)) $ M.elems evts)
    where
        _pEventRef = G.mapBothWithKey (const.EventP1) (const.EventP1) evts
        -- f = _ :: G.BiGraph Label EventId EventId
        -- _pEvents    = M.map (uncurry EventP1) evts ^. pFromEventId
        _pContext   = TheoryP1 { .. }
        _t0         = TheoryP0 ()
        -- _pImports
        -- _pNewEvents = M.map fst $ M.filter ((== Local) . snd) evts

set_decl :: MPipeline MachineP0 
            ( [(String,Sort,LineInfo)]
            , [(String,PostponedDef)] )
set_decl = machineCmd "\\newset" $ \(One (String tag)) _m _ -> do
            let name     = tag 
                new_sort = Sort tag (z3_escape name) 0
                new_type = Gen new_sort []
                new_def = Def [] (z3_escape name) [] (set_type new_type)
                                    $ zlift (set_type new_type) ztrue
            li <- lift ask
            return ([(tag,new_sort,li)],[(tag,(new_def,Local,li))])

event_splitting :: MPipeline MachineP0 [(Label, (EventId,[EventId]), LineInfo)]
event_splitting = machineCmd "\\splitevent" $ \(aevt, cevts) _m _p0 -> do
    let _ = aevt  :: Label
        _ = cevts :: [Label]
    li <- ask
    when (any ("skip" ==) cevts) $ do
        left [Error "invalid event name: 'skip' is a reserved name" li]
    return [(c,(EventId c,[EventId aevt]),li) | c <- cevts]

event_merging :: MPipeline MachineP0 [(Label, (EventId,[EventId]), LineInfo)]
event_merging = machineCmd "\\mergeevents" $ \(aevts, cevt) _m _p0 -> do
    let _ = aevts :: [Label]
        _ = cevt  :: Label
    li <- ask
    when (cevt == "skip") $ do
        left [Error "invalid event name: 'skip' is a reserved name" li]
    return [(cevt,(EventId cevt,map EventId aevts),li)]

event_decl :: MPipeline MachineP0 [(Label, (EventId,[EventId]), LineInfo)]
event_decl = machineCmd "\\newevent" $ \(One evt) _m _ -> do 
            li <- lift ask 
            when (evt == "skip") $ do
                left [Error "invalid event name: 'skip' is a reserved name" li]
            return [(evt,(EventId evt,[]),li)]

refines_mch :: MPipeline MachineP0 [((), MachineId, LineInfo)]
refines_mch = machineCmd "\\refines" $ \(One amch) cmch (MachineP0 ms _) -> do
            li <- lift ask
            unless (amch `M.member` ms) 
                $ left [Error (format "Machine {0} refines a non-existant machine: {1}" cmch amch) li]
                -- check that mch is a machine
            return [((),amch,li)]


import_theory :: MPipeline MachineP0 [(String, Theory, LineInfo)]
import_theory = machineCmd "\\with" $ \(One (String th_name)) _m _ -> do
        let th = [ ("sets"       , set_theory)
                 , ("functions"  , function_theory)
                 , ("relations"  , relation_theory)
                 , ("arithmetic" , arithmetic)
                 , ("predcalc"   , pred_calc)
                 , ("intervals"  , interval_theory) ]
            msg = "Undefined theory: {0} "
                -- add suggestions
        li <- lift ask
        case th_name `L.lookup` th of
            Nothing -> left [Error (format msg th_name) li]
            Just th -> return [(th_name,th,li)]
