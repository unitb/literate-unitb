{-# LANGUAGE OverloadedStrings
    , ConstraintKinds
    #-}
module Document.Phase.Test where

    --
    -- Modules
    --
import Document.Machine
import Document.Phase
import Document.Phase.Types
import Document.Phase.Declarations
import Document.Phase.Expressions
import Document.Phase.Proofs
import Document.Phase.Structures
import Document.Pipeline
import Document.Scope
import Document.ExprScope hiding (var)
import Document.VarScope  hiding (var)

import Latex.Monad

import Logic.Expr.Parser
import Logic.Theory

import Logic.Theories

import Test.UnitTest

import UnitB.Expr 
import UnitB.QuasiQuote
import UnitB.Syntax as AST 
import UnitB.UnitB

    --
    -- Libraries
    --
import Control.Arrow
import Control.Lens hiding ((<.>))
import Control.Lens.Misc
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Control.Precondition

import Data.Default
import Data.Existential
import Data.Graph.Bipartite as G
import Data.List as L
import Data.List.NonEmpty as NE
import Data.Map  as M
import Data.Maybe
import Data.Semigroup

import Test.QuickCheck
import Test.QuickCheck.Report

import Utilities.MapSyntax
import Utilities.Syntactic

mkMap :: (Arbitrary a,Ord k) => Hierarchy k -> Gen (Map k [a])
mkMap (Hierarchy xs _) = M.fromList.L.zip xs <$> replicateM (L.length xs) arbitrary

prop_inherit_equiv :: Hierarchy Int
                   -> Property
prop_inherit_equiv h = forAll (mkMap h) $ \m -> 
    inheritWith' id (L.map.(+)) (++) h m === inheritWithAlt id (L.map.(+)) (++) h (m :: Map Int [Int])

return []

runMap :: (Ord k, Scope a, Pre) 
       => MapSyntax k a b 
       -> Map k a
runMap = runMapWith merge_scopes

test_case :: TestCase
test_case = test

test :: TestCase
test = $(makeTestSuite "Unit tests for the parser")

name0 :: TestName
name0 = testName "test 0, phase 1 (structure), create object" 

mId :: String -> MachineId
mId = MId . makeName

case0 :: IO (MMap MachineP1)
case0 = do
    let ms = M.fromList [(mId "m0",()),(mId "m1",())]
        p0 = mapWithKey (const . MachineP0 ms) ms
        thy = M.fromList 
                [ (mId "m0", symbol_table $ arithmetic:thy2) 
                , (mId "m1", symbol_table $ set_theory:thy2) ]
        thy2 = M.elems preludeTheories
        s0 = z3Sort "S0" "S0" 0
        s0' = make_type s0 [] 
        se new_type = zlift (set_type new_type) ztrue
        s1 = z3Sort "\\S1" "sl$S1" 0
        s1' = make_type s1 [] 
        li = LI "file.ext" 1 1
        sorts = M.fromList
                [ (mId "m0",symbol_table [s0]) 
                , (mId "m1",symbol_table [s0,s1])]
        f th = M.unions $ L.map (view AST.types) $ M.elems th
        allSorts = M.intersectionWith (\ts th -> ts `M.union` f th) sorts thy
        pdef  = M.fromList
                [ (mId "m0",L.map (as_pair' $ view _1) [(z3Def [] "S0" [] (set_type s0') (se s0'),Local,li)]) 
                , (mId "m1",L.map (as_pair' $ view _1) [(z3Def [] "sl$S1" [] (set_type s1') (se s1'),Local,li)])]
        evts = M.fromList 
                [ (mId "m0",evts0)
                , (mId "m1",evts1) ]
        skipEvt = Left SkipEvent
        evts0 = fromJust $ makeGraph $ do
            ae0  <- newRightVertex (Right "ae0") ()
            ae1a <- newRightVertex (Right "ae1a") ()
            ae1b <- newRightVertex (Right "ae1b") ()
            cskip <- newRightVertex skipEvt ()
            askip <- newLeftVertex skipEvt ()
            forM_ [ae0,ae1a,ae1b,cskip] $ newEdge askip
        evts1 = fromJust $ makeGraph $ do
            ae0 <- newLeftVertex (Right "ae0") ()
            ae1a <- newLeftVertex (Right "ae1a") ()
            ae1b <- newLeftVertex (Right "ae1b") ()
            askip <- newLeftVertex skipEvt ()
            ce0a <- newRightVertex (Right "ce0a") ()
            ce0b <- newRightVertex (Right "ce0b") ()
            ce1 <- newRightVertex (Right "ce1") ()
            ce2 <- newRightVertex (Right "ce2") ()
            cskip <- newRightVertex skipEvt ()
            newEdge ae0 ce0a
            newEdge ae0 ce0b
            newEdge ae1a ce1
            newEdge ae1b ce1
            newEdge askip ce2
            newEdge askip cskip
    return $ make_phase1 <$> p0 
                         <.> thy 
                         <.> sorts 
                         <.> allSorts 
                         <.> (ms & traverse .~ M.empty)
                         <.> pdef 
                         <.> evts

result0 :: MMap MachineP1
result0 = M.fromList 
        [ (mId "m0",m0) 
        , (mId "m1",m1) ]
    where
        ms = M.fromList 
            [ (mId "m0",()) 
            , (mId "m1",()) ]
        skipEvt = Left SkipEvent
        newAEvent eid = newLeftVertex  (Right eid) (EventP1 $ Right eid)
        newCEvent eid = newRightVertex (Right eid) (EventP1 $ Right eid)
        abstractSkip = newLeftVertex  skipEvt (EventP1 skipEvt)
        concreteSkip = newRightVertex skipEvt (EventP1 skipEvt)

        evts0 = fromJust $ makeGraph $ do
            ae0 <- newCEvent "ae0"
            ae1a <- newCEvent "ae1a"
            ae1b <- newCEvent "ae1b"
            cskip <- concreteSkip
            askip <- abstractSkip
            forM_ [ae0,ae1a,ae1b,cskip] $ newEdge askip
        evts1 = fromJust $ makeGraph $ do
            ae0 <- newAEvent "ae0"
            ae1a <- newAEvent "ae1a"
            ae1b <- newAEvent "ae1b"
            askip <- abstractSkip
            ce0a <- newCEvent "ce0a"
            ce0b <- newCEvent "ce0b"
            ce1 <- newCEvent "ce1"
            ce2 <- newCEvent "ce2"
            cskip <- concreteSkip
            newEdge ae0 ce0a
            newEdge ae0 ce0b
            newEdge ae1a ce1
            newEdge ae1b ce1
            newEdge askip ce2
            newEdge askip cskip
        p0 = MachineP0 ms . mId
        tp0 = TheoryP0 ()
        m0 = MachineP1 (p0 "m0") evts0 (TheoryP1 tp0 thy0 sorts0 allSorts0 pdef0) 1
        m1 = MachineP1 (p0 "m1") evts1 (TheoryP1 tp0 thy1 sorts1 allSorts1 pdef1) 1
        s0 = z3Sort "S0" "S0" 0
        s0' = make_type s0 [] 
        se new_type = zlift (set_type new_type) ztrue
        s1 = z3Sort "\\S1" "sl$S1" 0
        s1' = make_type s1 [] 
        sorts0 = symbol_table [s0]
        sorts1 = symbol_table [s1] `M.union` sorts0
        f th = M.unions $ L.map (view AST.types) $ M.elems th
        allSorts0 = sorts0 `M.union` f thy0
        allSorts1 = sorts1 `M.union` f thy1
        pdef0  = [as_pair' (view _1) (z3Def [] "S0" [] (set_type s0') (se s0'),Local,li)]
        pdef1  = [as_pair' (view _1) (z3Def [] "sl$S1" [] (set_type s1') (se s1'),Local,li)]
        thy0 = symbol_table $ arithmetic:thy2
        thy1 = symbol_table $ set_theory:thy2
        thy2 = M.elems preludeTheories
        li = LI "file.ext" 1 1

name1 :: TestName
name1 = testName "test 1, phase 1, parsing"

case1 :: IO (Either [Error] SystemP1)
case1 = return $ runPipeline' ms cs () $ run_phase0_blocks >>> run_phase1_types
    where
        ms = M.map (:[]) $ M.fromList 
                [ ([tex|m0|],makeLatex "file.ext" $ do       
                            command "newset" [text "S0"]                 
                            command "newevent" [text "ae0"]
                            command "newevent" [text "ae1a"]
                            command "newevent" [text "ae1b"]
                        ) 
                    -- what if we split or merge non-existant events?
                , ([tex|m1|],makeLatex "file.ext" $ do
                            command "newset" [text "\\S1"]                 
                            command "refines" [text "m0"]
                            command "with" [text "sets"]
                            command "splitevent" [text "ae0",text "ce0a,ce0b"]
                            command "mergeevents" [text "ae1a,ae1b",text "ce1"]
                            command "newevent" [text "ce2"]
                        )]
        cs = M.empty

result1 :: Either [Error] SystemP1
result1 = Right (SystemP h result0)
    where
        h = Hierarchy ["m0","m1"] $ M.singleton "m1" "m0"

name2 :: TestName
name2 = testName "test 2, phase 2 (variables), creating state"

-- {-# SPECIALIZE lnZip' :: (Ord k) => Map k (a -> b) -> Traversal (Map k a) (Map k c) b c #-}
-- {-# INLINE lnZip' :: forall a k b c. (Ord k) => Map k (a -> b) -> Traversal (Map k a) (Map k c) b c #-}
{-# INLINE lnZip' #-}
lnZip' :: (Ord k) => Map k (a -> b) -> Traversal (Map k a) (Map k c) b c
lnZip' m f m' = traverse f $ M.intersectionWith (flip id) m' m

-- {-# SPECIALIZE lnZip :: (Ord k) => Map k b -> Traversal (Map k a) (Map k c) (a,b) c #-}
-- {-# SPECIALIZE lnZip :: (Ord k) => Map k b -> Traversal (Map k a) (Map k c) (a,b) c #-}
{-# INLINE lnZip #-}
lnZip :: (Ord k) 
      => Map k b -> Traversal (Map k a) (Map k c) (a,b) c
lnZip m = lnZip' $ flip (,) <$> m

-- {-# SPECIALIZE lnZip5 :: (Ord k) => Map k b0 -> Map k b1 -> Map k b2 -> Map k b3 -> Map k b4
--                       -> Traversal (Map k a) (Map k z) (a,b0,b1,b2,b3,b4) z #-}
-- {-# SPECIALIZE lnZip5 :: (Ord k) => Map k b0 -> Map k b1 -> Map k b2 -> Map k b3 -> Map k b4
--                       -> Traversal (Map k a) (Map k z) (a,b0,b1,b2,b3,b4) z #-}
{-# INLINE lnZip5 #-}
lnZip5 :: (Ord k)
       => Map k b0 -> Map k b1 -> Map k b2 -> Map k b3 -> Map k b4
       -> Traversal (Map k a) (Map k z) (a,b0,b1,b2,b3,b4) z
lnZip5 m0 m1 m2 m3 m4 = lnZip' $ (f <$> m0) `op` m1 `op` m2 `op` m3 `op` m4
    where
        f x0 x1 x2 x3 x4 y = (y,x0,x1,x2,x3,x4)
        op = M.intersectionWith ($)

case2 :: IO (Either [Error] SystemP2)
case2 = return $ do
        r <- result1
        runMM (r & (mchMap.lnZip vs) (uncurry make_phase2)) ()
    where
        li = LI "file.ext" 1 1
        s0 = z3Sort "S0" "S0" 0
        s0' = make_type s0 [] 
        se new_type = zlift (set_type new_type) ztrue
        s1 = z3Sort "\\S1" "sl$S1" 0
        s1' = make_type s1 [] 
        vs0 = M.fromList
                [ ([tex|x|],makeCell $ MchVar (z3Var "x" int) Local li) 
                , ([tex|y|],makeCell $ MchVar (z3Var "y" int) Local li)
                , ([tex|p|],makeCell $ Evt $ M.singleton (Right "ae1b") (EventDecl (Param $ z3Var "p" bool) (Right "ae1b":|[]) Local li))
                , ([tex|S0|],makeCell $ TheoryDef (z3Def [] "S0" [] (set_type s0') (se s0')) Local li) ]
        vs1 = M.fromList
                [ ([tex|z|],makeCell $ MchVar (z3Var "z" int) Local li) 
                , ([tex|y|],makeCell $ MchVar (z3Var "y" int) Inherited li) 
                , ([tex|p|],makeCell $ Evt $ M.singleton (Right "ce1") (EventDecl (Param $ z3Var "p" bool) (Right "ae1b":|[]) Inherited li))
                , ([tex|q|],makeCell $ Evt $ M.singleton (Right "ce2") (EventDecl (Index . InhAdd $ z3Var "q" int) (Right "ce2":|[]) Local li))
                , ([tex|x|],makeCell $ DelMchVar (Just $ z3Var "x" int) Local li) 
                , ([tex|S0|],makeCell $ TheoryDef (z3Def [] "S0" [] (set_type s0') (se s0')) Local li)
                , ([tex|\S1|],makeCell $ TheoryDef (z3Def [] "sl$S1" [] (set_type s1') (se s1')) Local li) ]
        vs = M.fromList 
                [ ("m0",vs0) 
                , ("m1",vs1)]

result2 :: Either [Error] SystemP2
result2 = do
        sys <- result1
        let 
            var n = Var (fromString'' n) int
            notation m = th_notation' $ m^.pImports
            parser m = default_setting (notation m)
            li = LI "file.ext" 1 1
            s0 = z3Sort "S0" "S0" 0
            s0' = make_type s0 [] 
            se new_type = zlift (set_type new_type) ztrue
            s1 = z3Sort "\\S1" "sl$S1" 0
            s1' = make_type s1 [] 
            fieldsM mid
                | mid == "m0" = [ make' PStateVars "x" $ var "x"
                                , make' PStateVars "y" $ var "y" ]
                | otherwise   = [ make' PStateVars "z" $ var "z"
                                , make' PDelVars "x" (var "x",li)
                                , make' PAbstractVars "x" $ var "x" 
                                , make' PAbstractVars "y" $ var "y" 
                                , make' PStateVars "y" $ var "y" ]
            fieldsT mid
                | mid == "m0" = [ make' PDefinitions "S0" (z3Def [] "S0" [] (set_type s0') (se s0')) ]
                | otherwise   = [ make' PDefinitions "S0" (z3Def [] "S0" [] (set_type s0') (se s0')) 
                                , make' PDefinitions "\\S1" (z3Def [] "sl$S1" [] (set_type s1') (se s1')) ]
            upMachine :: MachineId 
                      -> MachineP1' EventP1 EventP1 TheoryP2
                      -> MachineP2' EventP1 EventP1 TheoryP2
                      -> MachineP2' EventP1 EventP1 TheoryP2
            upMachine mid m m' = makeMachineP2'' m 
                        (m^.pCtxSynt & decls %~ M.union (m'^.pAllVars) 
                                     & primed_vars %~ M.union (m'^.pAllVars)) 
                        (fieldsM mid)
            upTheory mid t t' = makeTheoryP2 t (notation t) 
                        (parser t & decls %~ M.union ((t'^.pConstants) `M.union` (t'^.pDefVars))
                                  & sorts %~ M.union (t'^.pTypes)) 
                        (fieldsT mid)
            upEvent m eid e _ = makeEventP2 e 
                        (withIndSynt eid $ m^.pMchSynt) 
                        (withParamSynt eid $ m^.pMchSynt) (eventFields eid)
            withIndSynt eid p 
                | eid == Right "ce2" = p & decls %~ insert_symbol (z3Var "q" int)
                | otherwise          = p
            withParamSynt eid = withIndSynt eid . withParamSynt' eid
            withParamSynt' eid p 
                | eid `elem` [Right "ae1b",Right "ce1"] = p & decls %~ insert_symbol (z3Var "p" bool)
                | otherwise                             = p
            eventFields eid 
                | eid == Right "ae1b" = [make' EParams "p" (z3Var "p" bool)]
                | eid == Right "ce1"  = [make' EParams "p" (z3Var "p" bool)]
                | eid == Right "ce2"  = [make' EIndices "q" (z3Var "q" int)]
                | otherwise           = []
        return $ sys & mchMap.withKey.traverse %~ \(mid,m) -> 
                    layeredUpgradeRec (upTheory mid) (upMachine mid) upEvent upEvent m
        -- (\m -> makeMachineP2' (f m) _ [])

name3 :: TestName
name3 = testName "test 3, phase 2, parsing"

case3 :: IO (Either [Error] SystemP2)
case3 = return $ do
    let ms = M.fromList [(fromString'' "m0",[ms0]),(fromString'' "m1",[ms1])]
        ms0 = makeLatex "file.ext" $ do       
                  command "variable" [text "x,y : \\Int"]                 
                  command "param" [text "ae1b",text "p : \\Bool"]
        ms1 = makeLatex "file.ext" $ do       
                  command "variable" [text "z : \\Int"]                 
                  command "removevar" [text "x"]
                  command "indices" [text "ce2",text "q : \\Int"]
        cs = M.empty
    r <- result1
    runPipeline' ms cs r run_phase2_vars

result3 :: Either [Error] SystemP2
result3 = result2

name4 :: TestName
name4 = testName "test 4, phase 3 (expressions), create object"

case4 :: IO (Either [Error] SystemP3)
case4 = return $ do
        r <- result2
        runMM (r & (mchMap.lnZip es) (uncurry make_phase3)) ()
    where
        decl x con y = do
            scope <- ask
            lift $ x ## makeCell (con y scope $ li 1)
        event evt lbl con x = event' evt lbl [(evt,li $ -3)] con x
        mkEvent evt lbl es con x inh = do
            scope <- ask
            lift $ lbl ## makeEvtCell (Right evt) (con (inh (nonEmptyListSet $ fromMaybe ((evt,li (-1)) :| []) $ nonEmpty es,x)) scope $ listSet $ snd <$> es)
        event' evt lbl es con x = mkEvent evt lbl es con x InhAdd
        del_event evt lbl es con = mkEvent evt lbl es con (assertFalse' "del_event") $ InhDelete . const Nothing
        li = LI "file.ext" 1
        declVar n t = decls %= insert_symbol (z3Var n t)
        c_aux b = ctx $ do
            declVar "x" int
            declVar "y" int
            when b $ expected_type `assign` Nothing
        c  = c_aux False
        c' = c_aux True
        es = M.fromList [("m0",es0),("m1",es1)]
        es0 = runMap $ flip runReaderT Local $ do
                decl "inv0" Invariant $ c [expr| x \le y |]
                --event 
                event "ae0"  "grd0" Guard $ c [expr| x = 0 |]
                event "ae0"  "sch0" CoarseSchedule $ c [expr| y = y |]
                event "ae0"  "sch2" CoarseSchedule $ c [expr| y = 0 |]
                forM_ [("ae1a",li 108,li 164),("ae1b",li 136,li 192)] $ \(evt,l0,l1) -> do
                    event evt "default"  CoarseSchedule zfalse
                    event' evt "act0" [(evt,l0)] Action $ c' [act| y := y + 1 |] 
                    event' evt "act1" [(evt,l1)] Action $ c' [act| x := x - 1 |] 
        es1 = runMap $ flip runReaderT Inherited $ do
                local (const Local) $ do
                    decl "prog0" ProgressProp $ LeadsTo [] (c [expr| x \le y |]) (c [expr| x = y |])
                    decl "prog1" ProgressProp $ LeadsTo [] (c [expr| x \le y |]) (c [expr| x = y |])
                    decl "saf0" SafetyProp $ Unless [] (c [expr| x \le y |]) (c [expr| x = y |])
                decl "inv0" Invariant $ c [expr| x \le y |]
                event' "ce0a" "grd0" [("ae0",li 1)] Guard $ c [expr|x = 0|]
                event' "ce0b" "grd0" [("ae0",li 1)] Guard $ c [expr|x = 0|]
                local (const Local) $ do
                    del_event "ce0a" "grd0" [] Guard
                    del_event "ce0b" "grd0" [] Guard
                event' "ce0a"  "sch1" [("ce0a",li 1)] CoarseSchedule $ c [expr| y = y |]
                event' "ce0a"  "sch2" [("ae0",li 1)]  CoarseSchedule $ c [expr| y = 0 |]
                event' "ce0b"  "sch0" [("ae0",li 1)]  CoarseSchedule $ c [expr| y = y |]
                event' "ce0b"  "sch2" [("ae0",li 1)]  CoarseSchedule $ c [expr| y = 0 |]

                forM_ [("ce1",[("ae1a",li 1),("ae1b",li 1)]),("ce2",[])] $ \(evt,es) -> 
                    event' evt "default" es CoarseSchedule zfalse
                event' "ce1" "act0" [("ae1a",li 108),("ae1b",li 136)] Action $ c [act| y := y + 1 |]
                event' "ce1" "act1" [("ae1a",li 164),("ae1b",li 192)] Action $ c' [act| x := x - 1 |] 
                local (const Local) $
                    del_event "ce1" "act1" [("ae1a",li 6),("ae1b",li 7)] Action -- $ c [act| x := x - 1 |]

decl :: String -> GenericType -> State ParserSetting ()
decl n t = decls %= insert_symbol (z3Var n t)

result4 :: Either [Error] SystemP3
result4 = (mchMap.withKey.traverse %~ uncurry upgradeAll) <$> result3
    where
        upgradeAll mid = upgrade newThy (newMch mid) (newEvt mid) (newEvt mid)
        xvar = Var [tex|x|] int
        decl n t = decls %= insert_symbol (z3Var n t)
        c_aux b = ctx $ do
            decl "x" int
            decl "y" int
            when b $ expected_type `assign` Nothing
        c  = c_aux False
        c' = c_aux True
        newMch :: MachineId 
               -> MachineP2' ae ce thy 
               -> MachineP3' ae ce thy 
        newMch mid m 
            | mid == "m0" = makeMachineP3' m
                    empty_property_set 
                    (makePropertySet' [Inv "inv0" $ c [expr| x \le y |]])
                    [PInvariant "inv0" $ c [expr| x \le y |]]
            | otherwise = makeMachineP3' m
                    (makePropertySet' [Inv "inv0" $ c [expr| x \le y |]])
                    (makePropertySet' 
                        [ Progress "prog1" prog1
                        , Progress "prog0" prog0
                        , Safety "saf0" saf0 ])
                    [ PInvariant "inv0" $ c [expr| x \le y |]
                    , PProgress "prog1" prog1
                    , PProgress "prog0" prog0
                    , PSafety "saf0" saf0 ]
        prog0 = LeadsTo [] (c [expr| x \le y |]) (c [expr| x = y |])
        prog1 = LeadsTo [] (c [expr| x \le y |]) (c [expr| x = y |])
        saf0  = Unless [] (c [expr| x \le y |]) (c [expr| x = y |]) 
        newThy m = makeTheoryP3 m []
        newEvt mid _m (Right eid) e 
            | eid `elem` ["ae0","ce0a","ce0b"] = makeEventP3 e $ evtField mid eid
            | otherwise = makeEventP3 e $ [ ECoarseSched "default" zfalse] ++ evtField mid eid
        newEvt _mid _m (Left SkipEvent) e = makeEventP3 e [ECoarseSched "default" zfalse]
        lis = pure . LI "file.ext" 1
        evtField mid eid
            | eid == "ae0"                 = [ EGuards  "grd0" $ c [expr|x = 0|]
                                             , ECoarseSched "sch0" $ c [expr|y = y|] 
                                             , ECoarseSched "sch2" $ c [expr|y = 0|]]
            | eid == "ae1a"                = [ EActions "act0" (lis 108,c' [act| y := y + 1 |]) 
                                             , EActions "act1" (lis 164,c' [act| x := x - 1 |]) ]
            | eid == "ae1b"                = [ EActions "act0" (lis 136,c' [act| y := y + 1 |]) 
                                             , EActions "act1" (lis 192,c' [act| x := x - 1 |]) ]
            | eid == "ce0a"                = [ ECoarseSched "sch1" $ c [expr|y = y|] 
                                             , ECoarseSched "sch2" $ c [expr|y = 0|]]
            | eid == "ce0b"                = [ ECoarseSched "sch0" $ c [expr|y = y|] 
                                             , ECoarseSched "sch2" $ c [expr|y = 0|]]
            | eid == "ce1" && mid == "m1"  = [ EActions "act0" (lis 108 <> lis 136,c' [act| y := y + 1 |]) 
                                             , make' EWitness "x" (WitEq xvar $ c' [expr|x - 1|]) ]
            | otherwise = []

name5 :: TestName
name5 = testName "test 5, phase 3, parsing"

case5 :: IO (Either [Error] SystemP3)
case5 = return $ do
    let ms = M.fromList [(fromString'' "m0",[ms0]),(fromString'' "m1",[ms1])]
        ms0 = makeLatex "file.ext" $ do       
                  command "invariant" [text "inv0",text "x \\le y"]                 
                  command "evguard" [text "ae0", text "grd0", text "x = 0"]
                  command "cschedule" [text "ae0", text "sch0", text "y = y"]
                  command "cschedule" [text "ae0", text "sch2", text "y = 0"]
                  command "evbcmeq" [text "ae1a", text "act0", text "y", text "y+1"]
                  command "evbcmeq" [text "ae1b", text "act0", text "y", text "y+1"]
                  command "evbcmeq" [text "ae1a", text "act1", text "x", text "x-1"]
                  command "evbcmeq" [text "ae1b", text "act1", text "x", text "x-1"]
        ms1 = makeLatex "file.ext" $ do       
                  command "removeguard"  [text "ce0a",text "grd0"]
                  command "removeguard"  [text "ce0b",text "grd0"]
                  command "removecoarse" [text "ce0a",text "sch0"]
                  command "cschedule" [text "ce0a", text "sch1", text "y = y"]
                  command "progress"  [text "prog0",text "x \\le y",text "x = y"]
                  command "progress"  [text "prog1",text "x \\le y",text "x = y"]
                  command "safety" [text "saf0",text "x \\le y",text "x = y"]
                  command "removeact" [text "ce1", text "act1"] 
        cs = M.empty
    r <- result2
    runPipeline' ms cs r run_phase3_exprs

result5 :: Either [Error] SystemP3
result5 = result4

name6 :: TestName
name6 = testName "test 6, phase 4 (proofs), create object"

case6 :: IO (Either [Error] SystemP4)
case6 = return $ do
        r <- result4
        return $ r & (mchMap.lnZip5 cSchRef fSchRef liveProof comment proof) %~ 
                    uncurry6 make_phase4
    where
        li = LI "file.ext" 1 1
        ms = M.fromList [("m0",()),("m1",())]
        ch = ScheduleChange 
                (M.singleton "sch1" ()) 
                ("prog1", prog1) 
        cSchRef = runMap' $ do
            "m0" ## M.empty
            "m1" ## runMap' (do
                "ae0" ## [(("SCH/m1",ch),li)])
        fSchRef = runMap' $ do
            "m0" ## M.empty
            "m1" ## runMap' (do
                "ae0" ## Just (("prog1",prog1),li))
        liveProof = M.insert "m1" (runMap' $ do
            "prog0" ## ((makeRule' Monotonicity prog1 "prog1" (getExpr <$> prog1),[("prog0","prog1")]),li))
            $ M.empty <$ ms
        comment = M.empty <$ ms
        proof = M.empty <$ ms
        prog1 = LeadsTo [] (c [expr|x \le y|]) (c [expr|x = y|])
        c  = ctx $ do
            decl "x" int
            decl "y" int
        uncurry6 f (x0,x1,x2,x3,x4,x5) = f x0 x1 x2 x3 x4 x5

result6 :: Either [Error] SystemP4
result6 = (mchMap.withKey.traverse %~ uncurry upgradeAll) <$> result5
    where
        upgradeAll :: MachineId -> MachineP3 -> MachineP4
        upgradeAll mid = upgrade id (newMch mid) (newEvt mid) (const $ const id)
        --newThy t = 
        newEvt mid _m eid e 
            | eid == Right "ae0" && mid == "m1" = makeEventP4 e [("SCH/m1",ch)] (Just ("prog1",prog1)) []
            | otherwise           = makeEventP4 e [] Nothing []
        newMch mid m 
            | mid == "m1" = makeMachineP4' m [PLiveRule "prog0" (makeRule' Monotonicity prog1 "prog1" prog1)]
            | otherwise   = makeMachineP4' m []
        ch = ScheduleChange 
                (M.singleton "sch1" ()) 
                ("prog1", prog1) 
        prog1 = LeadsTo [] (c [expr|x \le y|]) (c [expr|x = y|])
        c  = ctx $ do
            decl "x" int
            decl "y" int

name7 :: TestName
name7 = testName "test 7, phase 4, parsing"

case7 :: IO (Either [Error] SystemP4)
case7 = return $ do
    let ms = M.fromList [(fromString'' "m0",[ms0]),(fromString'' "m1",[ms1])]
        ms0 = makeLatex "file.ext" $ do       
                  command "invariant" [text "inv0",text "x \\le y"]                 
                  command "evguard" [text "ae0", text "grd0", text "x = 0"]
                  command "evbcmeq" [text "ae1a", text "act0", text "y", text "y+1"]
        ms1 = makeLatex "file.ext" $ do       
                  command "replace" [text "ae0",text "sch1",text "prog1",text "saf0"]
                  command "replacefine" [text "ae0",text "prog1"]
                  command "refine" [text "prog0",text "monotonicity",text "prog1",text ""]
                  --command "removeguard" [text "ce0b",text "grd0"]
        cs = M.empty
    r <- result5
    runPipeline' ms cs r run_phase4_proofs

result7 :: Either [Error] SystemP4
result7 = result6

name8 :: TestName
name8 = testName "test 8, make machine"

case8 :: IO (Either [Error] (SystemP Machine))
case8 = return $ do
    r <- result7 
    runMM (r & mchMap (M.traverseWithKey make_machine)) ()

result8 :: Either [Error] (SystemP Machine)
result8 = Right $ SystemP h $ fromSyntax <$> ms
    where
        h = Hierarchy ["m0","m1"] (singleton "m1" "m0")
        xvar = Var [tex|x|] int
        ms = M.fromList [("m0",m0),("m1",m1)]
        s0 = z3Sort "S0" "S0" 0
        s1 = z3Sort "\\S1" "sl$S1" 0
        setS0 = set_type $ make_type s0 []
        setS1 = set_type $ make_type s1 []
        sorts0 = symbol_table [s0]
        sorts1 = symbol_table [s0,s1]
        defs0 = symbol_table [z3Def [] "S0" [] setS0 (zlift setS0 ztrue)]
        defs1 = symbol_table [ (z3Def [] "S0" [] setS0 (zlift setS0 ztrue))
                             , (z3Def [] "sl$S1" [] setS1 (zlift setS1 ztrue))]
        vars0 = symbol_table [z3Var "x" int,z3Var "y" int]
        vars1 = symbol_table [z3Var "z" int,z3Var "y" int]
        c' f = c $ f.(expected_type .~ Nothing)
        c = ctx $ do
            decl "x" int
            decl "y" int
        m0 = newMachine (fromString'' "m0") $ do
                theory.types .= sorts0
                theory.defs  .= defs0
                variables .= vars0
                events    .= evts0
                props.inv .= M.fromList [("inv0",c [expr| x \le y |])]
        p = c [expr| x \le y |]
        q = c [expr| x = y |]
        pprop = LeadsTo [] p q
        pprop' = getExpr <$> pprop
        sprop = Unless [] p q 
        m1 = newMachine (fromString'' "m1") $ do
                theory.types .= sorts1
                theory.defs .= defs1
                theory.extends %= insert_symbol set_theory
                del_vars .= symbol_table [z3Var "x" int]
                abs_vars .= vars0
                variables .= vars1
                events .= evts1
                inh_props.inv  .= M.fromList [("inv0",c [expr| x \le y |])]
                props.progress .= M.fromList [("prog0",pprop),("prog1",pprop)]
                props.safety .= M.singleton "saf0" sprop
                derivation .= M.fromList [("prog0",makeRule' Monotonicity pprop "prog1" pprop'),("prog1",makeRule Add pprop)]
        --y = Var "y" int
        skipLbl = Left SkipEvent
        ae0sched = create $ do
                        old .= ae0Evt
                        c_sched_ref .= [replace ("prog1",pprop)
                                          & add    .~ singleton "sch1" () ]
                        f_sched_ref .= Just ("prog1",pprop) 
        ae0Evt = create $ do
            coarse_sched .= M.fromList 
                [("sch0",c [expr| y = y|]),("sch2",c [expr| y = 0 |])]
            raw_guards .= M.fromList
                [("grd0",c [expr| x = 0 |])]
        ae1aEvt = create $ do
            coarse_sched .= M.fromList 
                [("default",c [expr| \false |])]
            actions .= M.fromList
                [ ("act0",c' [act| y := y + 1 |])
                , ("act1",c' [act| x := x - 1 |])]
        ae1bEvt = create $ do
            coarse_sched .= M.fromList 
                [("default",c [expr| \false |])]
            params .= symbol_table [z3Var "p" bool]
            actions .= M.fromList
                [ ("act0",c' [act| y := y + 1 |])
                , ("act1",c' [act| x := x - 1 |])]
        ce0aEvt = create $ do
            coarse_sched .= M.fromList 
                [("sch1",c [expr| y = y|]),("sch2",c [expr| y = 0 |])]
        ce0bEvt = create $ do
            coarse_sched .= M.fromList 
                [("sch0",c [expr| y = y|]),("sch2",c [expr| y = 0 |])]
        ce1Evt = create $ do
            params .= symbol_table [z3Var "p" bool]
            coarse_sched .= M.fromList 
                [("default",c [expr| \false |])]
            witness .= symbol_table' witVar
                [ (WitEq xvar $ c' [expr| x - 1 |]) ]
            actions .= M.fromList
                [ ("act0",c' [act| y := y + 1 |])]
            abs_actions .= M.fromList
                [ ("act0",c' [act| y := y + 1 |])
                , ("act1",c' [act| x := x - 1 |])]
            -- eql_vars .= symbol_table [y]
        ce2Evt = create $ do
            AST.indices .= symbol_table [z3Var "q" int]
            coarse_sched .= M.fromList 
                [("default",c [expr| \false |])]
        skipEvt = create $ do 
            coarse_sched .= M.fromList 
                [("default",c [expr| \false |])]
        evts0 = fromJust $ makeGraph $ do
            ae0  <- newRightVertex (Right "ae0") (def & new .~ ae0Evt)
            ae1a <- newRightVertex (Right "ae1a") (def & new .~ ae1aEvt)
            ae1b <- newRightVertex (Right "ae1b") (def & new .~ ae1bEvt)
            cskip <- newRightVertex skipLbl (def & new .~ skipEvt)
            askip <- newLeftVertex skipLbl (def & old .~ skipEvt)
            forM_ [ae0,ae1a,ae1b,cskip] $ newEdge askip
        evts1 = fromJust $ makeGraph $ do
            ae0  <- newLeftVertex (Right "ae0") ae0sched
            ae1a <- newLeftVertex (Right "ae1a") (def & old .~ ae1aEvt)
            ae1b <- newLeftVertex (Right "ae1b") (def & old .~ ae1bEvt)
            askip <- newLeftVertex skipLbl (def & old .~ skipEvt)
            ce0a <- newRightVertex (Right "ce0a") (def & new .~ ce0aEvt)
            ce0b <- newRightVertex (Right "ce0b") (def & new .~ ce0bEvt)
            ce1  <- newRightVertex (Right "ce1") ce1Evt
            ce2  <- newRightVertex (Right "ce2") (def & new .~ ce2Evt)
            cskip <- newRightVertex skipLbl (def & new .~ skipEvt)
            newEdge ae0 ce0a
            newEdge ae0 ce0b
            newEdge ae1a ce1
            newEdge ae1b ce1
            newEdge askip ce2
            newEdge askip cskip

name9 :: TestName
name9 = testName "QuickCheck inheritance"

prop9 :: (PropName -> Property -> IO (a, Result))
      -> IO ([a], Bool)
prop9 = $(quickCheckWrap 'prop_inherit_equiv)
