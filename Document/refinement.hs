{-# LANGUAGE FlexibleInstances, FlexibleContexts, IncoherentInstances #-}
module Document.Refinement where

    -- Module
import Document.Visitor
import Document.Proof

import UnitB.AST
import UnitB.PO
import UnitB.Genericity

import Latex.Parser

import Z3.Z3

    -- Libraries
import Control.Monad.Trans.Either
import Control.Monad.RWS as RWS

import Data.Char
import Data.List as L ( intercalate, (\\), null )
import Data.Map as M hiding ( map, (\\) )

import Utilities.Format
import Utilities.Syntactic

data Architecture = Arc 
    {  proof_struct :: [(Label,Label)]
    ,  ref_struct   :: Map Label Label
    }

empty_arc = Arc [] empty

add_proof_edge x xs = EitherT $ do
        RWS.modify (\x -> x { proof_struct = f $ proof_struct x } )
        return $ Right ()
    where
        f ys = map ((,) x) xs ++ ys

data RuleParserParameter = 
    RuleParserParameter
        Machine 
        (Map Label ProgressProp)
        (Map Label SafetyProp)
        Label
        [Label]
        [LatexDoc]

data Add = Add
    deriving Show

instance RefRule Add where
    rule_name _       = label "add"
    refinement_po _ _ = fromList []

class RuleParser a where
    parse_rule :: a -> [Label] -> String -> RuleParserParameter -> EitherT [Error] (RWS (Int,Int) [Error] b) Rule

instance RefRule a => RuleParser (a,()) where
    parse_rule (x,_) [] _ _ = return $ Rule x
    parse_rule (x,_) hyps_lbls _ _ = do
        (i,j) <- lift $ ask
        left [(format "too many hypotheses in the application of the rule: {0}" 
                    $ intercalate "," $ map show hyps_lbls, i, j)]

instance RuleParser (a,()) => RuleParser (ProgressProp -> a,()) where
    parse_rule (f,_) (x:xs) rule param@(RuleParserParameter m prog saf goal_lbl hyps_lbls _) = do
        case M.lookup x prog of
            Just p -> parse_rule (f p, ()) xs rule param
            Nothing -> do
                (i,j) <- lift $ ask
                left [(format "refinement ({0}): {1} should be a progress property" rule goal_lbl,i,j)]
    parse_rule _ [] rule _ = do
                (i,j) <- lift $ ask
                left [(format "refinement ({0}): expecting more properties" rule,i,j)]

instance RuleParser (a,()) => RuleParser (SafetyProp -> a,()) where
    parse_rule (f,_) (x:xs) rule param@(RuleParserParameter m prog saf goal_lbl hyps_lbls _) = do
        case M.lookup x saf of
            Just p -> parse_rule (f p, ()) xs rule param
            Nothing -> do
                (i,j) <- lift $ ask
                left [(format "refinement ({0}): {1} should be a safety property" rule goal_lbl,i,j)]
    parse_rule _ [] rule _ = do
                (i,j) <- lift $ ask
                left [(format "refinement ({0}): expecting more properties" rule,i,j)]

instance RuleParser (a,()) => RuleParser (Transient -> a,()) where
    parse_rule (f,_) (x:xs) rule param@(RuleParserParameter m prog saf goal_lbl hyps_lbls _) = do
        case M.lookup x $ transient $ props m of
            Just p -> parse_rule (f p, ()) xs rule param
            Nothing -> do
                (i,j) <- lift $ ask
                left [(format "refinement ({0}): {1} should be a safety property" rule goal_lbl,i,j)]
    parse_rule _ [] rule _ = do
                (i,j) <- lift $ ask
                left [(format "refinement ({0}): expecting more properties" rule,i,j)]

instance RuleParser (a,()) => RuleParser (Schedule -> a,()) where
    parse_rule (f,_) (x:xs) rule param@(RuleParserParameter m prog saf goal_lbl hyps_lbls _) = do
        case M.lookup x $ schedule $ props m of
            Just p -> parse_rule (f p, ()) xs rule param
            Nothing -> do
                (i,j) <- lift $ ask
                left [(format "refinement ({0}): {1} should be a safety property" rule goal_lbl,i,j)]
    parse_rule _ [] rule _ = do
                (i,j) <- lift $ ask
                left [(format "refinement ({0}): expecting more properties" rule,i,j)]

instance RefRule a => RuleParser ([ProgressProp] -> a,()) where
    parse_rule (f,_) xs rule param@(RuleParserParameter m prog saf goal_lbl hyps_lbls _) = do
            xs <- forM xs g
            return $ Rule (f xs)        
        where
            g x = maybe (do
                (i,j) <- lift $ ask
                left [(format "refinement ({0}): {1} should be a progress property" rule goal_lbl,i,j)] )
                return
                $ M.lookup x prog

instance RefRule a => RuleParser ([SafetyProp] -> a,()) where
    parse_rule (f,_) xs rule param@(RuleParserParameter m prog saf goal_lbl hyps_lbls _) = do
            xs <- forM xs g
            return $ Rule (f xs)        
        where
            g x = maybe (do
                (i,j) <- lift $ ask
                left [(format "refinement ({0}): {1} should be a safety property" rule goal_lbl,i,j)] )
                return
                $ M.lookup x saf

parse rc n param@(RuleParserParameter m prog saf goal_lbl hyps_lbls _) = do
        add_proof_edge goal_lbl hyps_lbls
        parse_rule rc (goal_lbl:hyps_lbls) n param

assert m suff prop = 
        [ ( po_lbl
            , (ProofObligation 
                (           assert_ctx m 
                `merge_ctx` step_ctx m) 
                (invariants p)
                True
                prop))
        ]
    where
        p    = props m
        po_lbl 
            | L.null suff = composite_label []
            | otherwise   = composite_label [label suff]

data Discharge = Discharge ProgressProp Transient (Maybe SafetyProp)
    deriving Show

instance RefRule Discharge where
    rule_name _ = label "discharge"
    refinement_po 
            (Discharge 
                    (LeadsTo fv0 p0 q0)
                    (Transient fv1 p1 _)
                    (Just (Unless fv2 p2 q2))) 
            m = fromList $
        assert m "" (
            zforall (fv0 ++ M.elems fv1 ++ fv2) ztrue (
                zall[ p0 `zimplies` p2
                    , q2 `zimplies` q0
                    , zand p0 (znot q0) `zimplies` p1
                    ]  ) )
    refinement_po 
            (Discharge 
                    (LeadsTo fv0 p0 q0)
                    (Transient fv1 p1 _)
                    Nothing)
            m = fromList $
                assert m "" (
                    zforall (fv0 ++ M.elems fv1) ztrue (
                        zand (p0 `zimplies` p1)
                             (znot p1 `zimplies` q0) ) )

mk_discharge :: ProgressProp -> Transient -> [SafetyProp] -> Discharge
mk_discharge p tr [s] = Discharge p tr $ Just s
mk_discharge p tr [] = Discharge p tr Nothing

parse_discharge rule params@(RuleParserParameter m prog saf goal_lbl hyps_lbls _) = do
    (i,j) <- lift $ ask
    when (1 > length hyps_lbls || length hyps_lbls > 2)
        $ left [(format "too many hypotheses in the application of the rule: {0}" 
                    $ intercalate "," $ map show hyps_lbls,i,j)]
    parse (mk_discharge,()) rule params

data Monotonicity = Monotonicity ProgressProp ProgressProp
    deriving Show

instance RefRule Monotonicity where
    rule_name _   = label "monotonicity"
    refinement_po (Monotonicity 
                    (LeadsTo fv0 p0 q0)
                    (LeadsTo fv1 p1 q1))
                  m = fromList ( 
                assert m "lhs" (
                    zforall (fv0 ++ fv1) ztrue $
                             (p0 `zimplies` p1))
             ++ assert m "rhs" (
                    zforall (fv0 ++ fv1) ztrue $
                             (q1 `zimplies` q0)))

data Implication = Implication ProgressProp
    deriving Show

instance RefRule Implication where
    rule_name _   = label "implication"
    refinement_po (Implication 
                    (LeadsTo fv1 p1 q1))
                  m = fromList $ 
                assert m "" (
                    zforall fv1 ztrue $
                             (p1 `zimplies` q1))

data Disjunction = Disjunction ProgressProp [([Var], ProgressProp)]
    deriving Show

instance RefRule Disjunction where
    rule_name _ = label "disjunction"
    refinement_po (Disjunction 
                    (LeadsTo fv0 p0 q0)
                    ps) m = fromList (
                assert m "lhs" (
                    zforall fv0 ztrue (
                        ( p0 `zimplies` zsome (map disj_p ps) ) ) )
             ++ assert m "rhs" (
                    zforall fv0 ztrue (
                        ( zsome (map disj_q ps) `zimplies` q0 ) ) ) )
        where
            disj_p ([], LeadsTo fv1 p1 q1) = p1
            disj_p (vs, LeadsTo fv1 p1 q1) = zexists vs ztrue p1
            disj_q ([], LeadsTo fv1 p1 q1) = q1
            disj_q (vs, LeadsTo fv1 p1 q1) = zexists vs ztrue q1

disjunction :: ProgressProp -> [ProgressProp] -> Disjunction
disjunction pr0@(LeadsTo fv0 p0 q0) ps = 
        let f pr1@(LeadsTo fv1 _ _) = (fv1 \\ fv0, pr1)
            ps0 = map f ps
        in (Disjunction pr0 ps0)

data NegateDisjunct = NegateDisjunct ProgressProp ProgressProp
    deriving Show

instance RefRule NegateDisjunct where
    rule_name _   = label "trading"
    refinement_po 
            (NegateDisjunct
                    (LeadsTo fv0 p0 q0)
                    (LeadsTo fv1 p1 q1))
            m = fromList $ 
                assert m "" (
                    zforall (fv0 ++ fv1) ztrue $
                        zand (zand p0 (znot q0) `zimplies` p1)
                                (q1 `zimplies` q0))
        
data Transitivity = Transitivity ProgressProp ProgressProp ProgressProp
    deriving Show

instance RefRule Transitivity where
    rule_name _ = label "transitivity"
    refinement_po 
            (Transitivity
                    (LeadsTo fv0 p0 q0)
                    (LeadsTo fv1 p1 q1)
                    (LeadsTo fv2 p2 q2))
            m = fromList $
                assert m "" $ 
                    zforall (fv0 ++ fv1 ++ fv2) ztrue $
                        zall[ p0 `zimplies` p1
                            , q1 `zimplies` p2
                            , q2 `zimplies` q0
                            ]

data PSP = PSP ProgressProp ProgressProp SafetyProp
    deriving Show

instance RefRule PSP where
    rule_name _ = label "PSP"
    refinement_po 
            (PSP
                    (LeadsTo fv0 p0 q0)
                    (LeadsTo fv1 p1 q1)
                    (Unless fv2 r b))
            m = fromList (
                assert m "lhs" (
                    zforall (fv0 ++ fv1 ++ fv2) ztrue $
                        (zand p1 r `zimplies` p0))
             ++ assert m "rhs" (
                    zforall (fv0 ++ fv1 ++ fv2) ztrue $
                            (q0 `zimplies` zor (q1 `zand` r) b)))

data Induction = Induction ProgressProp ProgressProp Variant
    deriving Show

instance RefRule Induction where
    rule_name _ = label "induction"
    refinement_po 
            (Induction 
                    (LeadsTo fv0 p0 q0)
                    (LeadsTo fv1 p1 q1) v)
            m = fromList (
                assert m "lhs" (
                    zforall (fv0 ++ fv1) ztrue $
                        ((p0 `zand` variant_equals_dummy v `zand` variant_bounded v) `zimplies` p1)
                        )
             ++ assert m "rhs" (
                    zforall (fv0 ++ fv1) ztrue $
                        (q1 `zimplies` zor (p0 `zand` variant_decreased v `zand` variant_bounded v) q0)
                        ))

parse_induction rule (RuleParserParameter m prog saf goal_lbl hyps_lbls hint) = do
        (i,j) <- ask
        toEither $ error_list
            [   ( length hyps_lbls /= 1
                , format "too many hypotheses in the application of the rule: {0}" 
                    $ intercalate "," $ map show hyps_lbls)
            ]
        let [h0] = hyps_lbls
        toEither $ error_list
            [   ( not (goal_lbl `member` prog)
                , format "refinement ({0}): {1} should be a progress property" rule goal_lbl )
            ,   ( not (h0 `member` prog)
                , format "refinement ({0}): {1} should be a progress property" rule h0 )
            ]
        (dir,var,bound) <- case find_cmd_arg 3 ["\\var"] hint of
            Just (_,_,[var,dir,bound],_) -> do
                    var   <- get_expr m var   
                    bound <- get_expr m bound 
                    dir  <- case map toLower $ concatMap flatten dir of
                        "up"   -> return Up
                        "down" -> return Down
                        _      -> left [("expecting a direction for the variant",i,j)]
                    var <- hoistEither $ either
                        (\x -> Left [(x,i,j)]) 
                        Right
                        $ (zcast int)
                        $ Right var
                    bound <- hoistEither $ either
                        (\x -> Left [(x,i,j)])
                        Right
                        $ zcast int
                        $ Right bound
                    return (dir,var,bound)
            Nothing -> left [("expecting a variant", i,j)]
        let pr0@(LeadsTo fv0 p0 q0) = prog ! goal_lbl
        let pr1@(LeadsTo fv1 p1 q1) = prog ! h0
        dum <- case fv1 \\ fv0 of
            [v] -> return v
            _   -> left [(   "inductive formula should have one free "
                            ++ "variable to record the variant",i,j)]                    
        add_proof_edge goal_lbl [h0]
        return $ Rule (Induction pr0 pr1 (IntegerVariant dum var bound dir))

--data Cancellation = Cancellation ProgressProp ProgressProp ProgressProp
--
--instance RefRule Cancellation where
--    rule_name _ = label "cancellation"
--    refinement_po 
--        (   Cancellation 
--                    (LeadsTo fv0 p0 q0)
--                    (LeadsTo fv1 p1 q1)
--                    (LeadsTo fv2 p2 q2))
--        m = fromList (
--            assert m "p" (p0 `zimplies` p1)
--         ++ assert m "q" (q1 `zimplies` 
--         ++ assert m "r"
--         ++ assert m "b"
