{-# LANGUAGE OverloadedStrings
    , RankNTypes
    , TemplateHaskell
    , GeneralizedNewtypeDeriving #-}
module Document.Phase.Test where

    --
    -- Modules
    --
import Document.Phase
import Document.Phase.Declarations
import Document.Phase.Expressions
import Document.Phase.Structures
import Document.Pipeline
import Document.Proof
import Document.Scope
import Document.ExprScope hiding (var)
import Document.VarScope  hiding (var)

import Latex.Monad

import Logic.Theory hiding (command)

import Theories.Arithmetic
import Theories.SetTheory

import UnitB.Expr hiding (fromJust)
import Tests.UnitTest

import UnitB.AST as AST

    --
    -- Libraries
    --
import Control.Applicative
import Control.Arrow
import Control.Lens hiding ((<.>),(.=))
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Writer

import Data.List as L
import Data.List.NonEmpty as NE
import Data.Map  as M
import Data.Maybe

import Utilities.BipartiteGraph as G
import Utilities.Syntactic

newtype MapSyntax k a b = MapSyntax (Writer [(k,a)] b)
    deriving (Functor,Applicative,Monad)

(##) :: k -> a -> MapSyntax k a ()
x ## y = MapSyntax (tell [(x,y)])

runMap :: (Ord k, Scope a) => MapSyntax k a b -> Map k a
runMap (MapSyntax cmd) = M.fromListWith merge_scopes $ execWriter cmd

test_case :: TestCase
test_case = test

test :: TestCase
test = $(makeTestSuite "Unit tests for the parser")

name0 :: String
name0 = "test 0, phase 1 (structure), create object" 

case0 :: IO (MTable MachineP1)
case0 = do
    let ms = M.fromList [(MId "m0",()),(MId "m1",())]
        p0 = mapWithKey (const . MachineP0 ms) ms
        thy = M.fromList 
                [ (MId "m0", M.fromList $ ("arithmetic",arithmetic):thy2) 
                , (MId "m1", M.fromList $ ("sets", set_theory):thy2) ]
        thy2 = [("basic", basic_theory),("arithmetic",arithmetic)]
        s0 = Sort "S0" "S0" 0
        s0' = make_type s0 [] 
        se new_type = zlift (set_type new_type) ztrue
        s1 = Sort "\\S1" "sl@S1" 0
        s1' = make_type s1 [] 
        li = LI "file.ext" 1 1
        sorts = M.fromList
                [ (MId "m0",M.singleton "S0" s0) 
                , (MId "m1",M.fromList [("S0",s0),("\\S1",s1)])]
        f th = M.unions $ L.map AST.types $ M.elems th
        allSorts = M.intersectionWith (\ts th -> ts `M.union` f th) sorts thy
        pdef  = M.fromList
                [ (MId "m0",[("S0",(Def [] "S0" [] (set_type s0') (se s0'),Local,li))]) 
                , (MId "m1",[("\\S1",(Def [] "sl@S1" [] (set_type s1') (se s1'),Local,li))])]
        evts = M.fromList 
                [ (MId "m0",evts0)
                , (MId "m1",evts1) ]
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
    return $ make_phase1 <$> p0 <.> thy 
                         <.> sorts <.> allSorts 
                         <.> pdef <.> evts

result0 :: MTable MachineP1
result0 = M.fromList 
        [ (MId "m0",m0) 
        , (MId "m1",m1) ]
    where
        ms = M.fromList 
            [ (MId "m0",()) 
            , (MId "m1",()) ]
        skipEvt = Left SkipEvent
        evts0 = fromJust $ makeGraph $ do
            ae0 <- newRightVertex (Right "ae0") EventP1
            ae1a <- newRightVertex (Right "ae1a") EventP1
            ae1b <- newRightVertex (Right "ae1b") EventP1
            cskip <- newRightVertex skipEvt EventP1
            askip <- newLeftVertex skipEvt EventP1
            forM_ [ae0,ae1a,ae1b,cskip] $ newEdge askip
        evts1 = fromJust $ makeGraph $ do
            ae0 <- newLeftVertex (Right "ae0") EventP1
            ae1a <- newLeftVertex (Right "ae1a") EventP1
            ae1b <- newLeftVertex (Right "ae1b") EventP1
            askip <- newLeftVertex skipEvt EventP1
            ce0a <- newRightVertex (Right "ce0a") EventP1
            ce0b <- newRightVertex (Right "ce0b") EventP1
            ce1 <- newRightVertex (Right "ce1") EventP1
            ce2 <- newRightVertex (Right "ce2") EventP1
            cskip <- newRightVertex skipEvt EventP1
            newEdge ae0 ce0a
            newEdge ae0 ce0b
            newEdge ae1a ce1
            newEdge ae1b ce1
            newEdge askip ce2
            newEdge askip cskip
        p0 = MachineP0 ms . MId
        tp0 = TheoryP0 ()
        m0 = MachineP1 (p0 "m0") evts0 (TheoryP1 tp0 thy0 sorts0 allSorts0 pdef0)
        m1 = MachineP1 (p0 "m1") evts1 (TheoryP1 tp0 thy1 sorts1 allSorts1 pdef1)
        s0 = Sort "S0" "S0" 0
        s0' = make_type s0 [] 
        se new_type = zlift (set_type new_type) ztrue
        s1 = Sort "\\S1" "sl@S1" 0
        s1' = make_type s1 [] 
        sorts0 = M.singleton "S0" s0
        sorts1 = M.singleton "\\S1" s1 `M.union` sorts0
        f th = M.unions $ L.map AST.types $ M.elems th
        allSorts0 = sorts0 `M.union` f thy0
        allSorts1 = sorts1 `M.union` f thy1
        pdef0  = [("S0",(Def [] "S0" [] (set_type s0') (se s0'),Local,li))]
        pdef1  = [("\\S1",(Def [] "sl@S1" [] (set_type s1') (se s1'),Local,li))]
        thy0 = M.singleton "arithmetic" arithmetic `M.union` thy2
        thy1 = M.singleton "sets" set_theory `M.union` thy2
        thy2 = M.fromList [("basic",basic_theory),("arithmetic",arithmetic)]
        li = LI "file.ext" 1 1

name1 :: String
name1 = "test 1, phase 1, parsing"

case1 :: IO (Either [Error] SystemP1)
case1 = return $ runPipeline' ms cs () $ run_phase0_blocks >>> run_phase1_types
    where
        ms = M.map (:[]) $ M.fromList 
                [ ("m0",makeLatex "file.ext" $ do       
                            command "newset" [text "S0"]                 
                            command "newevent" [text "ae0"]
                            command "newevent" [text "ae1a"]
                            command "newevent" [text "ae1b"]
                        ) 
                    -- what if we split or merge non-existant events?
                , ("m1",makeLatex "file.ext" $ do
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

name2 :: String
name2 = "test 2, phase 2 (variables), creating state"

lnZip :: Ord a => Map a b -> Traversal (Map a c) (Map a d) (c,b) d
lnZip m f m' = traverse f $ M.intersectionWith (,) m' m

case2 :: IO (Either [Error] SystemP2)
case2 = return $ do
        r <- result1
        runMM (r & (mchTable.lnZip vs) (uncurry make_phase2)) ()
    where
        li = LI "file.ext" 1 1
        s0 = Sort "S0" "S0" 0
        s0' = make_type s0 [] 
        se new_type = zlift (set_type new_type) ztrue
        s1 = Sort "\\S1" "sl@S1" 0
        s1' = make_type s1 [] 
        vs0 = M.fromList
                [ ("x",VarScope $ Machine (Var "x" int) Local li) 
                , ("y",VarScope $ Machine (Var "y" int) Local li)
                , ("S0",VarScope $ TheoryDef (Def [] "S0" [] (set_type s0') (se s0')) Local li) ]
        vs1 = M.fromList
                [ ("z",VarScope $ Machine (Var "z" int) Local li) 
                , ("y",VarScope $ Machine (Var "y" int) Inherited li) 
                , ("x",VarScope $ DelMch (Just $ Var "x" int) Local li) 
                , ("S0",VarScope $ TheoryDef (Def [] "S0" [] (set_type s0') (se s0')) Local li)
                , ("\\S1",VarScope $ TheoryDef (Def [] "sl@S1" [] (set_type s1') (se s1')) Local li) ]
        vs = M.fromList 
                [ ("m0",vs0) 
                , ("m1",vs1)]

withKey :: Lens (Map a b) (Map c d) (Map a (a,b)) (Map c d)
withKey = lens (M.mapWithKey (,)) (\_ -> id)

result2 :: Either [Error] SystemP2
result2 = do
        sys <- result1
        let 
            var n = Var n int
            notation m = th_notation $ empty_theory { extends = m^.pImports }
            parser m = default_setting (notation m)
            li = LI "file.ext" 1 1
            s0 = Sort "S0" "S0" 0
            s0' = make_type s0 [] 
            se new_type = zlift (set_type new_type) ztrue
            s1 = Sort "\\S1" "sl@S1" 0
            s1' = make_type s1 [] 
            fieldsM mid
                | mid == "m0" = [ PStateVars "x" $ var "x", PStateVars "y" $ var "y" ]
                | otherwise   = [ PStateVars "z" $ var "z"
                                , PDelVars "x" (var "x",li)
                                , PAbstractVars "x" $ var "x" 
                                , PAbstractVars "y" $ var "y" 
                                , PStateVars "y" $ var "y" ]
            fieldsT mid
                | mid == "m0" = [ PDefinitions "S0" (Def [] "S0" [] (set_type s0') (se s0')) ]
                | otherwise   = [ PDefinitions "S0" (Def [] "S0" [] (set_type s0') (se s0')) 
                                , PDefinitions "\\S1" (Def [] "sl@S1" [] (set_type s1') (se s1')) ]
            upMachine mid m m' = makeMachineP2' m 
                        (m^.pCtxSynt & decls %~ M.union (m'^.pAllVars) 
                                     & primed_vars %~ M.union (m'^.pAllVars)) 
                        (fieldsM mid)
            upTheory mid t t' = makeTheoryP2 t (notation t) 
                        (parser t & decls %~ M.union ((t'^.pConstants) `M.union` (t'^.pDefVars))
                                  & sorts %~ M.union (t'^.pTypes)) 
                        (fieldsT mid)
            -- f :: MachineP1' EventP1 TheoryP1 -> MachineP1' EventP2 TheoryP2
            -- f m = m & pContext %~ ()
            --         & pEventRef %~ (\g -> g & traverseLeft %~ upEvent & traverseRight %~ upEvent)
            upEvent m _ e _ = makeEventP2 e (m^.pMchSynt) (m^.pMchSynt) []
        return $ sys & mchTable.withKey.traverse %~ \(mid,m) -> 
                layeredUpgradeRec (upTheory mid) (upMachine mid) upEvent upEvent m
        -- (\m -> makeMachineP2' (f m) _ [])

name3 :: String
name3 = "test 3, phase 2, parsing"

case3 :: IO (Either [Error] SystemP2)
case3 = return $ do
    let ms = M.fromList [("m0",[ms0]),("m1",[ms1])]
        ms0 = makeLatex "file.ext" $ do       
                  command "variable" [text "x,y : \\Int"]                 
        ms1 = makeLatex "file.ext" $ do       
                  command "variable" [text "z : \\Int"]                 
                  command "removevar" [text "x"]
        cs = M.empty
    r <- result1
    runPipeline' ms cs r run_phase2_vars

result3 :: Either [Error] SystemP2
result3 = result2

name4 :: String
name4 = "test 4, phase 3 (expressions), create object"

case4 :: IO (Either [Error] (SystemP MachineP3))
case4 = return $ do
        r <- result2
        runMM (r & (mchTable.lnZip es) (uncurry make_phase3)) ()
    where
        decl x con y = do
            scope <- ask
            lift $ x ## ExprScope (con y scope li)
        event evt lbl con x = event' evt lbl [evt] con x
        mkEvent evt lbl es con x inh = do
            scope <- ask
            lift $ lbl ## ExprScope (EventExpr $ M.singleton (Right evt) 
                    (EvtExprScope $ con (inh (fromMaybe (evt :| []) $ nonEmpty es,x)) scope li)) 
        event' evt lbl es con x = mkEvent evt lbl es con x InhAdd
        del_event evt lbl es con = mkEvent evt lbl es con undefined $ InhDelete . const Nothing
        li = LI "file.ext" 1 1 
        x  = fst $ var "x" int
        y  = fst $ var "y" int
        es = M.fromList [("m0",es0),("m1",es1)]
        es0 = runMap $ flip runReaderT Local $ do
                decl "inv0" Invariant (DispExpr "x \\le y" $ $typeCheck $ x .<= y)
                --event 
                event "ae0"  "grd0" Guard $ DispExpr "x = 0" $ $typeCheck$ x .= 0 
                forM_ ["ae0","ae1a","ae1b"] $ \evt -> 
                    event evt "default" CoarseSchedule zfalse
                event "ae1a" "act0" Action $ DispExpr "y + 1" <$> $typeCheck (y $= y + 1)
        es1 = runMap $ flip runReaderT Inherited $ do
                decl "inv0" Invariant (DispExpr "x \\le y" $ $typeCheck $ x .<= y)
                --event 
                event' "ce0a" "grd0" ["ae0"] Guard $ DispExpr "x = 0" $ $typeCheck$ x .= 0 
                event' "ce0b" "grd0" ["ae0"] Guard $ DispExpr "x = 0" $ $typeCheck$ x .= 0 
                local (const Local) $ do
                    del_event "ce0a" "grd0" [] Guard
                    del_event "ce0b" "grd0" [] Guard
                forM_ [("ce0a",["ae0"]),("ce0b",["ae0"]),("ce1",["ae1a","ae1b"]),("ce2",[])] $ \(evt,es) -> 
                    event' evt "default" es CoarseSchedule zfalse
                event' "ce1" "act0" ["ae1a"] Action $ DispExpr "y + 1" <$> $typeCheck (y $= y + 1)

result4 :: Either [Error] (SystemP MachineP3)
result4 = (mchTable.withKey.traverse %~ uncurry upgradeAll) <$> result3
    where
        upgradeAll mid = upgrade newThy (newMch mid) (newEvt mid) (newEvt mid)
        x  = fst $ var "x" int
        y  = fst $ var "y" int
        newMch mid m 
            | mid == "m0" = makeMachineP3' m empty_property_set 
                    (makePropertySet' [Inv "inv0" $ DispExpr "x \\le y" $ $typeCheck$ x .<= y])
                    [PInvariant "inv0" $ DispExpr "x \\le y" $ $typeCheck$ x .<= y ]
            | otherwise = makeMachineP3' m 
                    (makePropertySet' [Inv "inv0" $ DispExpr "x \\le y" $ $typeCheck$ x .<= y])
                    empty_property_set 
                    [PInvariant "inv0" $ DispExpr "x \\le y" $ $typeCheck$ x .<= y ]
        newThy m = makeTheoryP3 m []
        newEvt mid _m (Right eid) e = makeEventP3 e $ [ ECoarseSched "default" zfalse] ++ evtField mid eid
        newEvt _mid _m (Left _) e = makeEventP3 e []
        evtField mid eid
            | eid == "ae0"                 = [EGuards  "grd0" $ DispExpr "x = 0" $ $typeCheck (x .= 0)]
            | eid == "ae1a"                = [EActions "act0" $ DispExpr "y + 1" <$> $typeCheck (y $= y + 1)]
            | eid == "ce1" && mid == "m1"  = [EActions "act0" $ DispExpr "y + 1" <$> $typeCheck (y $= y + 1)]
            | otherwise = []

name5 :: String
name5 = "test 5, phase 3, parsing"

case5 :: IO (Either [Error] (SystemP MachineP3))
case5 = return $ do
    let ms = M.fromList [("m0",[ms0]),("m1",[ms1])]
        ms0 = makeLatex "file.ext" $ do       
                  command "invariant" [text "inv0",text "x \\le y"]                 
                  command "evguard" [text "ae0", text "grd0", text "x = 0"]
                  command "evbcmeq" [text "ae1a", text "act0", text "y", text "y+1"]
        ms1 = makeLatex "file.ext" $ do       
                  command "removeguard" [text "ce0a",text "grd0"]
                  command "removeguard" [text "ce0b",text "grd0"]
        cs = M.empty
    r <- result2
    runPipeline' ms cs r run_phase3_exprs

result5 :: Either [Error] (SystemP MachineP3)
result5 = result4
