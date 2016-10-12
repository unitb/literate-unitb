{-# LANGUAGE OverloadedStrings #-}
module UnitB.Proof.PO where

    -- Modules
import Logic.Expr as E hiding (Context)
import Logic.Proof.POGenerator

import UnitB.Proof.Rules
import UnitB.Property

    -- Libraries
import Control.Lens 
import Control.Monad

import Data.List as L
import Data.List.NonEmpty as NE
import Data.Map as M hiding ((\\))
import Data.Maybe
import Data.Typeable

import Prelude hiding (id,(.))

class LivenessRule rule => LivenessRulePO rule  where
    liveness_po :: RawProgressProp 
                -> rule
                -> ProgressHyp rule RawProgressProp
                -> TransientHyp rule RawTransient
                -> SafetyHyp rule RawSafetyProp
                -> POGen ()
    automaticSafety :: RawProgressProp -> rule -> [RawSafetyProp]
    automaticTransient :: RawProgressProp -> rule -> [RawTransient]
    automaticSafety _ _ = []
    automaticTransient _ _ = []

instance LivenessRulePO Ensure where
    liveness_po _ _ Proxy Proxy Proxy = return ()
    automaticSafety (LeadsTo vs p q) (Ensure _ _) = [saf]
        where
            saf = Unless vs p q
    automaticTransient (LeadsTo vs p q) (Ensure lbls hint) = [tr]
        where
            tr  = Tr (symbol_table vs) 
                     (p `zand` znot q) lbls 
                     hint 
instance LivenessRulePO Monotonicity where
    liveness_po (LeadsTo fv0 p0 q0) Monotonicity 
            (Identity (LeadsTo fv1 p1 q1)) 
            Proxy Proxy = do
        emit_goal ["lhs"] (
            zforall (fv0 ++ fv1) ztrue $
                     (p0 `zimplies` p1))
        emit_goal ["rhs"] (
            zforall (fv0 ++ fv1) ztrue $
                     (q1 `zimplies` q0))
instance LivenessRulePO Implication where
    liveness_po (LeadsTo fv1 p1 q1) Implication
            Proxy Proxy Proxy = do
        emit_goal [] (
            zforall fv1 ztrue $
                     (p1 `zimplies` q1))
instance LivenessRulePO Disjunction where
    liveness_po (LeadsTo fv0 p0 q0) Disjunction 
            ps Proxy Proxy = do
        emit_goal ["lhs"] (
            zforall fv0 ztrue (
                ( p0 `zimplies` zsome (NE.map disj_p ps') ) ) )
        emit_goal ["rhs"] (
            zforall fv0 ztrue (
                ( zsome (NE.map disj_q ps') `zimplies` q0 ) ) )
        where
            ps' = NE.map disj_vs ps
            disj_vs p@(LeadsTo fv1 _ _) = (fv1 \\ fv0,p)
            disj_p ([], LeadsTo _ p1 _) = p1
            disj_p (vs, LeadsTo _ p1 _) = zexists vs ztrue p1
            disj_q ([], LeadsTo _ _ q1) = q1
            disj_q (vs, LeadsTo _ _ q1) = zexists vs ztrue q1
instance LivenessRulePO NegateDisjunct where
    liveness_po (LeadsTo fv0 p0 q0) NegateDisjunct
            (Identity (LeadsTo fv1 p1 q1)) 
            Proxy Proxy = do
        emit_goal ["lhs"] (
            zforall (fv0 ++ fv1) ztrue $
                        (zand p0 (znot q0) `zimplies` p1))
        emit_goal ["rhs"] (
            zforall (fv0 ++ fv1) ztrue $
                        (q1 `zimplies` q0))
instance LivenessRulePO Transitivity where
    liveness_po (LeadsTo fv0 p0 q0) Transitivity
            xs Proxy Proxy = do
        let (LeadsTo fv1 p1 _) = NE.head xs
            (LeadsTo fv2 _ q2) = NE.last xs
            conseq = L.zip (NE.toList xs) (L.drop 1 $ NE.toList xs)
        emit_goal ["lhs"] ( 
            zforall (fv0 ++ fv1 ++ fv2) ztrue $
                    p0 `zimplies` p1 )
        forM_ (L.zip [0..] conseq) $ \(i,(p,q)) -> do
            let (LeadsTo fv1 _ q1) = p
                (LeadsTo fv2 p2 _) = q
                l1 = label $ show (i :: Int)
                l2 = label $ show (i + 1 :: Int)
            emit_goal ["mhs" </> l1 </> l2] ( 
                zforall (fv0 ++ fv1 ++ fv2) ztrue $
                        q1 `zimplies` p2 )
        emit_goal ["rhs"] ( 
            zforall (fv0 ++ fv1 ++ fv2) ztrue $
                    q2 `zimplies` q0 )
instance LivenessRulePO PSP where
    liveness_po (LeadsTo fv0 p0 q0) PSP
            (Identity (LeadsTo fv1 p1 q1))
            Proxy 
            (Identity (Unless fv2 r b)) = do
        emit_goal ["lhs"] (
            zforall (fv0 ++ fv1 ++ fv2) ztrue $
                (zand p1 r `zimplies` p0))
        emit_goal ["rhs"] (
            zforall (fv0 ++ fv1 ++ fv2) ztrue $
                    (q0 `zimplies` zor (q1 `zand` r) b))
instance LivenessRulePO Induction where
    liveness_po (LeadsTo fv0 p0 q0) (Induction v)
            (Identity (LeadsTo fv1 p1 q1))
            Proxy Proxy = do
        emit_goal ["lhs"] (
            zforall (fv0 ++ fv1) ztrue $
                ((p0 `zand` variant_equals_dummy v `zand` variant_bounded v) `zimplies` p1)
                )
        emit_goal ["rhs"] (
            zforall (fv0 ++ fv1) ztrue $
                (q1 `zimplies` zor (p0 `zand` variant_decreased v `zand` variant_bounded v) q0)
                )
instance LivenessRulePO Add where
    liveness_po _ Add Proxy Proxy Proxy = emit_goal [] (zfalse :: Expr)
instance LivenessRulePO Discharge where
    liveness_po (LeadsTo fv0 p0 q0)
            Discharge Proxy (Identity (Tr fv1 p1 _ _)) (Just (Unless fv2 p2 q2)) = do
        emit_goal ["saf/lhs"] (
            zforall (fv0 ++ M.elems fv1 ++ fv2) ztrue (
                    p0 `zimplies` p2
                    ) )
        emit_goal ["saf/rhs"] (
            zforall (fv0 ++ M.elems fv1 ++ fv2) ztrue (
                    q2 `zimplies` q0
                    ) )
        emit_goal ["tr"] (
            zforall (fv0 ++ M.elems fv1 ++ fv2) ztrue (
                    zand p0 (znot q0) `zimplies` p1
                    ) )
    liveness_po (LeadsTo fv0 p0 q0)
            Discharge Proxy (Identity (Tr fv1 p1 _ _)) Nothing = do
        emit_goal ["tr/lhs"] (
            zforall (fv0 ++ M.elems fv1) ztrue (
                     (p0 `zimplies` p1) ) )
        emit_goal ["tr/rhs"] (
            zforall (fv0 ++ M.elems fv1) ztrue (
                     (znot p1 `zimplies` q0) ) )
